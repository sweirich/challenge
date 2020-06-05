-- | Optimized version of Strongly-typed System F
module PolyTypedOpt where

import Imports
-- Note: bug in singletons. Cannot qualify this module import.
import Subst
import SubstProperties 
import qualified SubstTypedOpt as T

-- We import the definition of types from the "untyped" AST so that we can
-- later write a type checker that shares these types. (See TypeCheck.hs).
import Poly (Ty(..),STy(..))

data Exp :: [Ty] -> Ty -> Type where

  IntE   :: Int
         -> Exp g IntTy

  VarE   :: T.Idx g t
         -> Exp g t

  LamE   :: Π t1               -- type of binder
         -> T.Bind Exp t1 g t2    -- body of abstraction
         -> Exp g (t1 :-> t2)

  AppE   :: Exp g (t1 :-> t2)     -- function
         -> Exp g t1              -- argument
         -> Exp g t2

  TyLam  :: Exp (IncList g) t     -- bind a type variable
         -> Exp g (PolyTy t)

  TyApp  :: Exp g (PolyTy t1)     -- type function
         -> Π t2               -- type argument
         -> Exp g (Subst (SingleSub t2) t1)

instance T.SubstC Exp where
   var = VarE

   subst s (IntE x)     = IntE x
   subst s (VarE x)     = T.applyS s x
   subst s (LamE ty e)  = LamE ty (T.substBind s e)
   subst s (AppE e1 e2) = AppE (T.subst s e1) (T.subst s e2)
   subst s (TyLam e)    = TyLam (T.subst (substSubTy sIncSub s) e)
   subst s (TyApp e t)  = TyApp (T.subst s e) t

substTy :: forall g s ty.
   Π (s :: Sub Ty) -> Exp g ty -> Exp (Map (SubstSym1 s) g) (Subst s ty)
substTy s (IntE x)     = IntE x
substTy s (VarE n)     = VarE $ T.mapIdx @(SubstSym1 s)  n
substTy s (LamE t e)   = LamE (sSubst s t) (T.bind (substTy s (T.unbind e)))
substTy s (AppE e1 e2) = AppE (substTy s e1) (substTy s e2)
substTy s (TyLam (e :: Exp (IncList g) t))    
    | Refl <- axiom1 @g s = TyLam (substTy (sLift s) e)
substTy s (TyApp (e :: Exp g (PolyTy t1)) (t :: STy t2))  
    | Refl <- axiom2 @t1 @t2 s
                       = TyApp (substTy s e) (sSubst s t)

substSubTy :: forall s g g'. Π s -> T.Sub Exp g g' -> T.Sub Exp (Map (SubstSym1 s) g) (Map (SubstSym1 s) g')
substSubTy s (T.Inc (x :: T.IncBy g1)) 
  | Refl <- axiom_map1 @(SubstSym1 s) @g1 @g = T.Inc (T.mapInc @(SubstSym1 s)  x) 
substSubTy s (e T.:< s1)   = substTy s e T.:< substSubTy s s1
substSubTy s (s1 T.:<> s2) = substSubTy s s1 T.:<> substSubTy s s2
