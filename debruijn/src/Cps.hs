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

import qualified Subst as U
import qualified SubstTyped as T
import SubstProperties

$(singletons [d|
    voidTy = PolyTy (VarTy Z)
    |])




-- | Access a runtime version of the type
-- of a (well-typed) expression
typeOf :: Sing g -> Exp g t -> Sing t
typeOf g (VarE v)       = T.singIndx g v
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
    SPolyTy t1 -> U.sSubst (U.sSingleSub tys) t1

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

type family CpsSub (s :: U.Sub Ty) where
    CpsSub (U.Inc k)     = U.Inc k
    CpsSub (t U.:< s)    = CpsTy t U.:< CpsSub s
    CpsSub (s1 U.:<> s2) = CpsSub s1 U.:<> CpsSub s2

cpsSub :: U.Sub Ty -> U.Sub Ty
cpsSub (U.Inc k)     = U.Inc k
cpsSub (t U.:< s)    = cpsTy t U.:< cpsSub s
cpsSub (s1 U.:<> s2) = cpsSub s1 U.:<> cpsSub s2

--------------------------------------------------------

data Cont g t where
  Obj   :: Exp g (t :-> VoidTy)  -> Cont g t
  Meta  :: Exp (t : g) VoidTy     -> Cont g t

applyCont :: Cont g t -> Exp g t -> Exp g VoidTy
applyCont (Obj o)  v  = AppE o v
applyCont (Meta k) v  = T.subst (T.singleSub v) k

reifyCont :: Sing t -> Cont g t -> Exp g (t :-> VoidTy)
reifyCont t (Obj o)   = o
reifyCont t (Meta k)  = LamE t k

substTyCont :: Sing (s :: U.Sub Ty) -> Cont g t -> Cont (Map (U.SubstSym1 s) g) (U.Subst s t)
substTyCont s (Obj o)   = Obj (substTy s o)
substTyCont s (Meta k)  = Meta (substTy s k)

substCont :: T.Sub Exp g g' -> Cont g t -> Cont g' t
substCont s (Obj o)   = Obj (T.subst s o)
substCont s (Meta k)  = Meta (T.subst (T.lift s) k)

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
          

cpsIdx :: CpsCtx g g' -> T.Idx g t -> T.Idx g' (CpsTy t)
cpsIdx CpsStart v = case v of {}
cpsIdx (CpsLamE t1 t2 gg) T.Z      = T.S T.Z
cpsIdx (CpsLamE t1 t2 gg) (T.S v)  = T.S (T.S (cpsIdx gg v))
cpsIdx (CpsTyLam t1 gg)   v         = T.S (cpsIdx gg v)
cpsIdx (CpsMetaE t1 gg)   T.Z      = T.Z
cpsIdx (CpsMetaE t1 gg)   (T.S v)  =
  T.S (cpsIdx gg v)
  

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
  
        k'  = Obj $ VarE T.Z
  
      in
        applyCont k e'    
cpsExp g (TyLam e) k   = 
  case typeOf (fstCtx g) (TyLam e) of
     SPolyTy t1 -> 
       applyCont k
       $ TyLam 
       $ LamE (sContTy t1) 
       $ cpsExp (CpsTyLam t1
                 (sIncCpsCtx g)) e (Obj $ VarE T.Z)
 
cpsExp g (AppE e1 e2)  k =
  case typeOf (fstCtx g) e1 of
    ((t1 :: Sing t1) :%-> (t2 :: Sing t2)) -> let
      
         k1 :: Cont g' (CpsTy (t1 :-> t2))
         k1 = Meta $ cpsExp (CpsMetaE (t1 :%-> t2) g)
                        (T.subst T.incSub e2) k2
   
         k2 :: Cont (CpsTy (t1 :-> t2) ': g') (CpsTy t1)
         k2 =  Meta $ AppE (AppE (VarE (T.S T.Z)) (VarE T.Z))
                (reifyCont (sCpsTy t2)
                 (substCont T.incSub 
                   (substCont T.incSub k)))
   
     in
       cpsExp g e1 k1
 
cpsExp (g :: CpsCtx g g') (TyApp e1 (ty :: Sing (ty :: Ty))) k =
  case typeOf (fstCtx g) e1 of
    SPolyTy (t1 :: Sing t1)
      | Refl <- cpsCommutes @t1 @(U.SingleSub ty)
      -> 
        let 
          k1 :: Cont g' (CpsTy (PolyTy t1))
          k1 = Meta $ AppE (TyApp (VarE T.Z)
                              (sCpsTy ty)) (reifyCont t1' k2)
  
          k2 :: Cont (CpsTy (PolyTy t1) ': g') 
                     (U.Subst (U.SingleSub (CpsTy ty)) (CpsTy t1))
          k2 = substCont T.incSub k
  
          t1' :: Sing (U.Subst (U.SingleSub (CpsTy ty))  (CpsTy t1))
          t1' = U.sSubst (U.sSingleSub (sCpsTy ty)) (sCpsTy t1)
        in
          cpsExp g e1 k1



cpsCommutes :: forall ty (s :: U.Sub Ty).
             CpsTy (U.Subst s ty) :~: U.Subst (CpsSub s) (CpsTy ty)
cpsCommutes = assertEquality

-- Justification for axiom above using quickCheck
prop_cpsCommutes ty s =
   cpsTy (U.subst s ty) == U.subst (cpsSub s) (cpsTy ty)


sIncCpsCtx  :: forall n g g'.
               CpsCtx g g'
            -> CpsCtx (IncList g) (IncList g')
sIncCpsCtx CpsStart = CpsStart
sIncCpsCtx (CpsLamE (t1 :: Sing t1) (t2 :: p t2) g)
  | Refl <- cpsCommutes @t1 @U.IncSub
  , Refl <- cpsCommutes @t2 @U.IncSub
  = CpsLamE (U.sSubst U.sIncSub t1)
     (Proxy :: Proxy (U.Subst U.IncSub t2)) (sIncCpsCtx g)
sIncCpsCtx (CpsMetaE (t1 :: Sing t1) g)
  | Refl <- cpsCommutes @t1 @U.IncSub
  = CpsMetaE (U.sSubst U.sIncSub t1) (sIncCpsCtx g)
sIncCpsCtx (CpsTyLam (t1 :: Sing t1) g)
  | Refl <- cpsCommutes @t1 @U.IncSub
  = CpsTyLam (U.sSubst U.sIncSub t1) (sIncCpsCtx g)

fstCtx :: CpsCtx g g' -> Sing g
fstCtx CpsStart = SNil
fstCtx (CpsLamE t1 t2 g) = SCons t1 (fstCtx g)
fstCtx (CpsMetaE t1 g)    = SCons t1 (fstCtx g)
fstCtx (CpsTyLam t1 g)   = fstCtx g

