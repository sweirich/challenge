-- | A "scope-safe" interpreter for System F
-- Only tracks the scope of expression variables. 
module PolyScoped where

import Imports
import Nat
import qualified Subst as W
import SubstScoped

-- | Import definition of System F types. 
import Poly (Ty(..))


-- | Syntax of STLC expressions, using GADT to track the scope
--  of the variables in terms
data Exp :: Nat -> Type where
  IntE   :: Int      -- literal ints
         -> Exp n
  VarE   :: !(Idx n)   -- variables (Idx is defined in Subst)
         -> Exp n
  LamE   :: Ty         -- type of binder
         -> Exp (S n)  -- body of abstraction (bind a new variable)
         -> Exp n         
  AppE   :: Exp n     -- function
         -> Exp n     -- argument
         -> Exp n
  TyLam  :: Exp n      -- bind a type variable (expression scope is unchanged)
         -> Exp n
  TyApp  :: Exp n      -- type function
         -> Ty         -- type argument
         -> Exp n
         
     deriving (Eq, Show)

-- Our implementation of de Brujn indices relies on a type class
-- to overload the substitution operation. 
-- In the variable case, we need to look up the index in the substitution 
-- (using `applyS`).
-- When recursing under binders, we need to `lift` the indices in the 
-- substitution one step. (i.e. what was at index 0 in the substitution is 
-- now at index 1, etc.)

instance SubstDB Exp where
   var = VarE

   subst s (IntE x)     = IntE x
   subst s (VarE x)     = applySub s x
   subst s (LamE ty e)  = LamE ty (subst (lift s) e)
   subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)
   subst s (TyLam e)    = TyLam (subst (incTy s) e)  
   subst s (TyApp e t)  = TyApp (subst s e) t


-- | Apply  a type substitution to an expression
substTy :: W.Sub Ty -> Exp n -> Exp n
substTy s (IntE x)     = IntE x
substTy s (VarE n)     = VarE n
substTy s (LamE t e)   = LamE (W.subst s t) (substTy s e)
substTy s (AppE e1 e2) = AppE (substTy s e1) (substTy s e2)
substTy s (TyLam e)    = TyLam (substTy (W.lift s) e)
substTy s (TyApp e t)  = TyApp (substTy s e) (W.subst s t)


-- | Increment all types in an expression substitution
incTy :: forall n m . Sub Exp n m -> Sub Exp n m 
incTy (Inc x)     = Inc x
incTy (e :< s1)   = substTy W.incSub e :< incTy s1
incTy (s1 :<> s2) = incTy s1 :<> incTy s2


-----------------------------------------------------------------------
-- Examples

-- | Small-step evaluation of closed terms.
-- 
-- Either return the next term or Nothing, if the term is already a value.
-- In a closed term, the scope is 'Z', because there are zero free variables.
step :: Exp Z -> Maybe (Exp Z)
step (IntE x)     = Nothing
--step (VarE n)     = error "Unbound variable"
step (LamE t e)   = Nothing
step (AppE e1 e2) = Just $ stepApp e1 e2 where
step (TyLam e)    = Nothing
step (TyApp e t)  = Just $ stepTyApp e t where

stepApp :: Exp Z -> Exp Z  -> Exp Z
stepApp (IntE x)       e2 = error "Type error"
--stepApp (VarE n)       e2 = error "Unbound variable"    
stepApp (LamE t e1)    e2 = subst (singleSub e2) e1
stepApp (AppE e1' e2') e2 = AppE (stepApp e1' e2') e2
stepApp (TyLam e)      e2 = error "Type error"
stepApp (TyApp e1 t1)  e2 = AppE (stepTyApp e1 t1) e2

stepTyApp :: Exp Z -> Ty -> Exp Z
stepTyApp (IntE x)       e2 = error "Type error"
--stepTyApp (VarE n)       t1 = error "Unbound variable"
stepTyApp (LamE t e1)    t1 = error "Type error"
stepTyApp (AppE e1' e2') t1 = TyApp (stepApp e1' e2') t1
stepTyApp (TyLam e1)     t1 = substTy (W.singleSub t1) e1
stepTyApp (TyApp e1 t2)  t1 = TyApp (stepTyApp e1 t2) t1


-- | Reduce open expressions to their normal form
reduce :: Exp n -> Exp n
reduce (IntE x)   = IntE x
reduce (VarE n)   = VarE n
reduce (LamE t e) = LamE t (reduce e)
reduce (AppE (LamE t e1) e2) = subst (singleSub (reduce e2)) (reduce e1)
reduce (AppE (IntE x)    e2) = error "Type error!"
reduce (AppE e1 e2)          = AppE (reduce e1) (reduce e2)
reduce (TyLam e)             = TyLam (reduce e)
reduce (TyApp (TyLam e) t1)  = substTy (W.singleSub t1) (reduce e)
reduce (TyApp e t)           = TyApp (reduce e) t




