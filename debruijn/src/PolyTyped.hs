
module PolyTyped where

import Imports
-- Note: bug in singletons. Cannot qualify this module import.
import Subst
import SubstProperties 
import qualified SubstTyped as T

-- We import the definition of types from the "untyped" AST so that we can
-- later write a type checker that shares these types. (See TypeCheck.hs).
import Poly (Ty(..),STy(..))



data Exp :: [Ty] -> Ty -> Type where

  IntE   :: Int
         -> Exp g IntTy

  VarE   :: T.Idx g t
         -> Exp g t

  LamE   :: Sing t1               -- type of binder
         -> Exp (t1:g) t2         -- body of abstraction
         -> Exp g (t1 :-> t2)

  AppE   :: Exp g (t1 :-> t2)     -- function
         -> Exp g t1              -- argument
         -> Exp g t2

  TyLam  :: Exp (IncList g) t     -- bind a type variable
         -> Exp g (PolyTy t)

  TyApp  :: Exp g (PolyTy t1)     -- type function
         -> Sing t2               -- type argument
         -> Exp g (Subst (SingleSub t2) t1)

instance T.SubstC Exp where
   var = VarE

   subst s (IntE x)     = IntE x
   subst s (VarE x)     = T.applyS s x
   subst s (LamE ty e)  = LamE ty (T.subst (T.lift s) e)
   subst s (AppE e1 e2) = AppE (T.subst s e1) (T.subst s e2)
   subst s (TyLam e)    = TyLam (T.subst (substTy_Sub sIncSub s) e)
   subst s (TyApp e t)  = TyApp (T.subst s e) t

substTy :: forall g s ty.
   Sing (s :: Sub Ty) -> Exp g ty -> Exp (SubstList s g) (Subst s ty)
substTy s (IntE x)     = IntE x
substTy s (VarE n)     = VarE $ T.mapIdx @(SubstSym1 s)  n
substTy s (LamE t e)   = LamE (sSubst s t) (substTy s e)
substTy s (AppE e1 e2) = AppE (substTy s e1) (substTy s e2)
substTy s (TyLam (e :: Exp (SubstList IncSub g) t))    
    | Refl <- axiom1 @g s = TyLam (substTy (sLift s) e)
substTy s (TyApp (e :: Exp g (PolyTy t1)) (t :: Sing t2))  
    | Refl <- axiom2 @t1 @t2 s
                       = TyApp (substTy s e) (sSubst s t)

substTy_Sub :: forall s g g'. Sing s -> T.Sub Exp g g' -> T.Sub Exp (SubstList s g) (SubstList s g')
--substTy_Sub s T.IdS         = T.IdS
substTy_Sub s (T.Inc (x :: T.IncBy g1)) 
  | Refl <- axiom_map1 @(SubstSym1 s) @g1 @g = T.Inc (T.mapInc @(SubstSym1 s)  x) 
substTy_Sub s (e T.:< s1)   = substTy s e T.:< substTy_Sub s s1
substTy_Sub s (s1 T.:<> s2) = substTy_Sub s s1 T.:<> substTy_Sub s s2


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
    SPolyTy t1 -> sSubst (sSingleSub tys) t1