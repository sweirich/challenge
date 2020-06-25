{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module Cps where

import Prelude hiding ((!!),(>>),drop,take,length)
import Test.QuickCheck hiding ((===))

import Nat
import Imports

import AssertEquality
import Poly(Ty(..),STy(..),PolyTySym0,VarTySym0)
import PolyTyped

import qualified Subst as W
import qualified SubstTyped as S
import SubstProperties

$(singletons [d|
    voidTy = PolyTy (VarTy Z)
    |])




-- | Access a runtime version of the type
-- of a (well-typed) expression
typeOf :: Sing g -> Exp g t -> Sing t
typeOf g (VarE v)       = S.singIndx g v
typeOf g (IntE x)       =
  SIntTy
typeOf g (LamE t1 e)    =
  t1 :%-> typeOf (SCons t1 g) e
typeOf g (AppE e1 e2)   =
  case typeOf g e1 of
    _ :%-> t2 -> t2
typeOf g (TyLam e)    =
  SPolyTy (typeOf (sIncList g) e)
typeOf g (TyApp e tys)  =
  case typeOf g e of
    SPolyTy t1 -> W.sSubst (W.sSingleSub tys) t1

------------------------------------------------
-- This part is the type translation. To make it work, 
-- we need the type family dependency. However, the 
-- singletons library cannot add this, so we must write the 
-- same three functions three separate times.

type family CpsTy a = r | r -> a where
  CpsTy (VarTy i)      = VarTy i
  CpsTy IntTy          = IntTy
  CpsTy (t1 :-> t2)   =
     CpsTy t1 :-> (ContTy t2 :-> VoidTy)
  CpsTy (PolyTy t1)  =
    PolyTy (ContTy t1 :-> VoidTy)

type family ContTy a = r | r -> a where
  ContTy t = CpsTy t :-> VoidTy

type family CpsList g = r | r -> g where
  CpsList '[] = '[]
  CpsList (t : g) = (CpsTy t : CpsList g)

cpsTy :: Ty -> Ty
cpsTy (VarTy i)      = VarTy i
cpsTy IntTy          = IntTy
cpsTy (t1 :-> t2)    = cpsTy t1 :-> (contTy t2 :-> voidTy)
cpsTy (PolyTy t1)  = PolyTy (contTy t1 :-> voidTy)

contTy :: Ty -> Ty
contTy t = cpsTy t :-> voidTy

cpsList :: [Ty] -> [Ty]
cpsList = map cpsTy

sCpsTy :: Sing t -> Sing (CpsTy t)
sCpsTy (SVarTy i)      = SVarTy i
sCpsTy SIntTy          = SIntTy
sCpsTy (t1 :%-> t2)    = sCpsTy t1 :%-> (sContTy t2 :%-> sVoidTy)
sCpsTy (SPolyTy t1)    = SPolyTy (sContTy t1 :%-> sVoidTy)

sContTy :: Sing t -> Sing (ContTy t)
sContTy t = sCpsTy t :%->  sVoidTy

sCpsList :: Sing ts -> Sing (CpsList ts)
sCpsList SNil = SNil
sCpsList (SCons t ts) = SCons (sCpsTy t) (sCpsList ts)

--------------------------------------------------------

type family CpsSub (s :: W.Sub Ty) where
    CpsSub (W.Inc k)     = W.Inc k
    CpsSub (t W.:< s)    = CpsTy t W.:< CpsSub s
    CpsSub (s1 W.:<> s2) = CpsSub s1 W.:<> CpsSub s2

cpsSub :: W.Sub Ty -> W.Sub Ty
cpsSub (W.Inc k)     = W.Inc k
cpsSub (t W.:< s)    = cpsTy t W.:< cpsSub s
cpsSub (s1 W.:<> s2) = cpsSub s1 W.:<> cpsSub s2

--------------------------------------------------------

data Cont g t where
  Obj   :: Exp g (t :-> VoidTy)  -> Cont g t
  Meta  :: Exp (t : g) VoidTy     -> Cont g t

applyCont :: Cont g t -> Exp g t -> Exp g VoidTy
applyCont (Obj o)  v  = AppE o v
applyCont (Meta k) v  = S.subst (S.singleSub v) k

reifyCont :: Sing t -> Cont g t -> Exp g (t :-> VoidTy)
reifyCont t (Obj o)   = o
reifyCont t (Meta k)  = LamE t k

substTyCont :: Sing (s :: W.Sub Ty) -> Cont g t -> Cont (Map (W.SubstSym1 s) g) (W.Subst s t)
substTyCont s (Obj o)   = Obj (substTy s o)
substTyCont s (Meta k)  = Meta (substTy s k)

substCont :: S.Sub Exp g g' -> Cont g t -> Cont g' t
substCont s (Obj o)   = Obj (S.subst s o)
substCont s (Meta k)  = Meta (S.subst (S.lift s) k)

data CpsCtx g g' where

  CpsStart  :: CpsCtx '[] '[]
  -- Empty context

  CpsLamE   :: Sing t1 -> proxy t2 -> CpsCtx g g'
            -> CpsCtx (t1 : g) (ContTy t2 : CpsTy t1 : g')
  -- Context in the body of LamE. The input has the type
  -- of the parameter and the output has both its converted
  -- type and a continuation. 

  CpsTyLam  :: Sing t1 -> CpsCtx g g'
            -> CpsCtx g (ContTy t1 : g')
  -- Context in the body of a TyLam. The output includes
  -- a continuation for the polymorphic term.

  CpsMetaE   :: Sing t1 -> CpsCtx g g'
          -> CpsCtx (t1 : g) (CpsTy t1  : g')
  -- Context in the body of Meta. The input has the type
  -- of the parameter and the output has the converted type.
          

cpsIdx :: CpsCtx g g' -> S.Idx g t -> S.Idx g' (CpsTy t)
cpsIdx CpsStart v = case v of {}
cpsIdx (CpsLamE t1 t2 gg) S.Z      = S.S S.Z
cpsIdx (CpsLamE t1 t2 gg) (S.S v)  = S.S (S.S (cpsIdx gg v))
cpsIdx (CpsTyLam t1 gg)   v         = S.S (cpsIdx gg v)
cpsIdx (CpsMetaE t1 gg)   S.Z      = S.Z
cpsIdx (CpsMetaE t1 gg)   (S.S v)  =
  S.S (cpsIdx gg v)
  

cpsExp :: forall t g g'.
        CpsCtx g g' 
     -> Exp g t
     -> Cont g' (CpsTy t) 
     -> Exp g' VoidTy
cpsExp g (VarE v)      k =  applyCont k (VarE (cpsIdx g v))
cpsExp g (IntE i)      k =  applyCont k (IntE i)
cpsExp g (LamE t1 e1)  k =
  case typeOf (fstCtx g) (LamE t1 e1) of
    (_t1 :%-> t2) ->
      let
        e'  = LamE (sCpsTy t1)
               $ LamE (sContTy t2)
                 $ cpsExp (CpsLamE t1 t2 g) e1 k'
  
        k'  = Obj $ VarE S.Z
  
      in
        applyCont k e'    
cpsExp g (TyLam e) k   = 
  case typeOf (fstCtx g) (TyLam e) of
     SPolyTy t1 -> 
       applyCont k
       $ TyLam 
       $ LamE (sContTy t1) 
       $ cpsExp (CpsTyLam t1
                 (sIncCpsCtx g)) e (Obj $ VarE S.Z)
 
cpsExp g (AppE e1 e2)  k =
  case typeOf (fstCtx g) e1 of
    ((t1 :: Sing t1) :%-> (t2 :: Sing t2)) -> let
      
         k1 :: Cont g' (CpsTy (t1 :-> t2))
         k1 = Meta $ cpsExp (CpsMetaE (t1 :%-> t2) g)
                        (S.subst S.weakSub e2) k2
   
         k2 :: Cont (CpsTy (t1 :-> t2) ': g') (CpsTy t1)
         k2 =  Meta $ AppE (AppE (VarE (S.S S.Z)) (VarE S.Z))
                (reifyCont (sCpsTy t2)
                 (substCont S.weakSub 
                   (substCont S.weakSub k)))
   
     in
       cpsExp g e1 k1
 
cpsExp (g :: CpsCtx g g') (TyApp e1 (ty :: Sing (ty :: Ty))) k =
  case typeOf (fstCtx g) e1 of
    SPolyTy (t1 :: Sing t1)
      | Refl <- cpsCommutes @t1 @(W.SingleSub ty)
      -> 
        let 
          k1 :: Cont g' (CpsTy (PolyTy t1))
          k1 = Meta $ AppE (TyApp (VarE S.Z)
                              (sCpsTy ty)) (reifyCont t1' k2)
  
          k2 :: Cont (CpsTy (PolyTy t1) ': g') 
                     (W.Subst (W.SingleSub (CpsTy ty)) (CpsTy t1))
          k2 = substCont S.weakSub k
  
          t1' :: Sing (W.Subst (W.SingleSub (CpsTy ty))  (CpsTy t1))
          t1' = W.sSubst (W.sSingleSub (sCpsTy ty)) (sCpsTy t1)
        in
          cpsExp g e1 k1



cpsCommutes :: forall ty (s :: W.Sub Ty).
             CpsTy (W.Subst s ty) :~: W.Subst (CpsSub s) (CpsTy ty)
cpsCommutes = assertEquality

-- Justification for axiom above using quickCheck
prop_cpsCommutes ty s =
   cpsTy (W.subst s ty) == W.subst (cpsSub s) (cpsTy ty)


sIncCpsCtx  :: forall n g g'.
               CpsCtx g g'
            -> CpsCtx (IncList g) (IncList g')
sIncCpsCtx CpsStart = CpsStart
sIncCpsCtx (CpsLamE (t1 :: Sing t1) (t2 :: p t2) g)
  | Refl <- cpsCommutes @t1 @W.WeakSub
  , Refl <- cpsCommutes @t2 @W.WeakSub
  = CpsLamE (W.sSubst W.sWeakSub t1)
     (Proxy :: Proxy (W.Subst W.WeakSub t2)) (sIncCpsCtx g)
sIncCpsCtx (CpsMetaE (t1 :: Sing t1) g)
  | Refl <- cpsCommutes @t1 @W.WeakSub
  = CpsMetaE (W.sSubst W.sWeakSub t1) (sIncCpsCtx g)
sIncCpsCtx (CpsTyLam (t1 :: Sing t1) g)
  | Refl <- cpsCommutes @t1 @W.WeakSub
  = CpsTyLam (W.sSubst W.sWeakSub t1) (sIncCpsCtx g)

fstCtx :: CpsCtx g g' -> Sing g
fstCtx CpsStart = SNil
fstCtx (CpsLamE t1 t2 g) = SCons t1 (fstCtx g)
fstCtx (CpsMetaE t1 g)    = SCons t1 (fstCtx g)
fstCtx (CpsTyLam t1 g)   = fstCtx g

