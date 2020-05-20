{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module Cps where

import Prelude hiding ((!!),(>>),drop,take,length)
import Test.QuickCheck hiding ((===))
import Unsafe.Coerce
import Debug.Trace

import Imports
import Nat
import Poly(Ty(..),STy(..),PolyTySym0,VarTySym0)
import Subst
import PolyTyped
import qualified SubstTyped as ST

$(singletons [d|
    voidTy = PolyTy (VarTy Z)
    |])

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

data Cont g t where
  Obj   :: Exp g (t :-> VoidTy)  -> Cont g t
  Meta  :: Exp (t : g) VoidTy     -> Cont g t

applyCont :: Cont g t -> Exp g t -> Exp g VoidTy
applyCont (Obj o)  v  = AppE o v
applyCont (Meta k) v  = ST.subst (ST.singleSub v) k

reifyCont :: Sing t -> Cont g t -> Exp g (t :-> VoidTy)
reifyCont t (Obj o)   = o
reifyCont t (Meta k)  = LamE t k

substTyCont :: Sing (s :: Sub Ty) -> Cont g t -> Cont (Map (SubstSym1 s) g) (Subst s t)
substTyCont s (Obj o)   = Obj (substTy s o)
substTyCont s (Meta k)  = Meta (substTy s k)

substCont :: ST.Sub Exp g g' -> Cont g t -> Cont g' t
substCont s (Obj o)   = Obj (ST.subst s o)
substCont s (Meta k)  = Meta (ST.subst (ST.lift s) k)

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
          

cpsIdx :: CpsCtx g g' -> ST.Idx g t -> ST.Idx g' (CpsTy t)
cpsIdx CpsStart v = case v of {}
cpsIdx (CpsLamE t1 t2 gg) ST.Z      = ST.S ST.Z
cpsIdx (CpsLamE t1 t2 gg) (ST.S v)  = ST.S (ST.S (cpsIdx gg v))
cpsIdx (CpsTyLam t1 gg)   v         = ST.S (cpsIdx gg v)
cpsIdx (CpsMetaE t1 gg)   ST.Z      = ST.Z
cpsIdx (CpsMetaE t1 gg)   (ST.S v)  =
  ST.S (cpsIdx gg v)
  

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
  
        k'  = Obj $ VarE ST.Z
  
      in
        applyCont k e'    
cpsExp g (TyLam e) k   = 
  case typeOf (fstCtx g) (TyLam e) of
     SPolyTy t1 -> 
       applyCont k
       $ TyLam 
       $ LamE (sContTy t1) 
       $ cpsExp (CpsTyLam t1
                 (sIncCpsCtx g)) e (Obj $ VarE ST.Z)
 
cpsExp g (AppE e1 e2)  k =
  case typeOf (fstCtx g) e1 of
    ((t1 :: Sing t1) :%-> (t2 :: Sing t2)) -> let
      
         k1 :: Cont g' (CpsTy (t1 :-> t2))
         k1 = Meta $ cpsExp (CpsMetaE (t1 :%-> t2) g)
                        (ST.subst ST.incSub e2) k2
   
         k2 :: Cont (CpsTy (t1 :-> t2) ': g') (CpsTy t1)
         k2 =  Meta $ AppE (AppE (VarE (ST.S ST.Z)) (VarE ST.Z))
                (reifyCont (sCpsTy t2)
                 (substCont ST.incSub 
                   (substCont ST.incSub k)))
   
     in
       cpsExp g e1 k1
 
cpsExp (g :: CpsCtx g g') (TyApp e1 (ty :: Sing ty)) k =
  case typeOf (fstCtx g) e1 of
    SPolyTy (t1 :: Sing t1)
      | Refl <- cpsCommutes2 @ty @t1
      -> 
        let 
          k1 :: Cont g' (CpsTy (PolyTy t1))
          k1 = Meta $ AppE (TyApp (VarE ST.Z)
                              (sCpsTy ty)) (reifyCont t1' k2)
  
          k2 :: Cont (CpsTy (PolyTy t1) ': g') 
                     (Subst (SingleSub (CpsTy ty)) (CpsTy t1))
          k2 = substCont ST.incSub k
  
          t1' :: Sing (Subst (SingleSub (CpsTy ty))  (CpsTy t1))
          t1' = sSubst (sSingleSub (sCpsTy ty)) (sCpsTy t1)
        in
          cpsExp g e1 k1

cpsCommutes :: forall ty.
             CpsTy (Subst IncSub ty) :~: Subst IncSub (CpsTy ty)
cpsCommutes = unsafeCoerce Refl


cps_commutes ty =
   cpsTy (subst incSub ty) == subst incSub (cpsTy ty)

cpsCommutes2 :: forall ty1 ty.
             CpsTy (Subst (SingleSub ty1) ty) :~:
             Subst (SingleSub (CpsTy ty1)) (CpsTy ty)
cpsCommutes2 = unsafeCoerce Refl

cps_commutes2 tys ty =
   cpsTy (subst (singleSub tys) ty) == subst (singleSub (cpsTy tys)) (cpsTy ty)

sIncCpsCtx  :: forall n g g'.
               CpsCtx g g'
            -> CpsCtx (IncList g) (IncList g')
sIncCpsCtx CpsStart = CpsStart
sIncCpsCtx (CpsLamE (t1 :: Sing t1) (t2 :: p t2) g)
  | Refl <- cpsCommutes @t1
  , Refl <- cpsCommutes @t2
  = CpsLamE (sSubst sIncSub t1)
     (Proxy :: Proxy (Subst IncSub t2)) (sIncCpsCtx g)
sIncCpsCtx (CpsMetaE (t1 :: Sing t1) g)
  | Refl <- cpsCommutes @t1
  = CpsMetaE (sSubst sIncSub t1) (sIncCpsCtx g)
sIncCpsCtx (CpsTyLam (t1 :: Sing t1) g)
  | Refl <- cpsCommutes @t1
  = CpsTyLam (sSubst sIncSub t1) (sIncCpsCtx g)

fstCtx :: CpsCtx g g' -> Sing g
fstCtx CpsStart = SNil
fstCtx (CpsLamE t1 t2 g) = SCons t1 (fstCtx g)
fstCtx (CpsMetaE t1 g)    = SCons t1 (fstCtx g)
fstCtx (CpsTyLam t1 g)   = fstCtx g

