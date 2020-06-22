-- | A "scope-safe" interpreter for the simply-typed lambda calculus
module SimpleScoped where

import Imports
import Nat
import SubstScoped

-- | Syntax of Simply-Typed Lambda Calculus (STLC) types
data Ty = IntTy | Ty :-> Ty
  deriving (Eq, Show)

-- | Syntax of STLC expressions, using GADT to track the scope
--  of the variables in terms
data Exp :: Nat -> Type where
  IntE   :: Int      -- literal ints
         -> Exp n
  VarE   :: Idx n     -- variables (Idx is defined in Subst)
         -> Exp n
  LamE   :: Ty         -- type of binder
         -> Exp (S n)  -- body of abstraction (bind a new variable)
         -> Exp n         
  AppE   :: Exp n     -- function
         -> Exp n     -- argument
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

-----------------------------------------------------------------------
-- Examples

-- | Small-step evaluation of closed terms.
-- 
-- Either return the next term or Nothing, if the term is already a value.
-- In a closed term, the scope is 'Z', because there are zero free variables.
step :: Exp Z -> Maybe (Exp Z)
step (IntE x)     = Nothing
step (VarE n)     = case n of {}
step (LamE t e)   = Nothing
step (AppE e1 e2) = Just $ stepApp e1 e2 where

    stepApp :: Exp Z -> Exp Z  -> Exp Z
    stepApp (IntE x)       e2 = error "Type error"
    stepApp (VarE n)       e2 = case n of {}    
    stepApp (LamE t e1)    e2 = subst (singleSub e2) e1
    stepApp (AppE e1' e2') e2 = AppE (stepApp e1' e2') e2


-- | Big-step evaluation of closed terms
-- To do this correctly, we need to define a separate type
-- for values. 
data Val :: Nat -> Type where
  IntV :: Int -> Val n
  LamV :: Ty
        -> Exp (S n)        -- body of abstraction
        -> Val n

eval :: Exp Z -> Val Z
eval (IntE x) = IntV x
eval (VarE n) = case n of {}
eval (LamE t e) = LamV t e
eval (AppE e1 e2) =
  case eval e1 of
    (IntV x) -> error "Type error"
    (LamV t e1') -> eval (subst (singleSub e2) e1')


-- | Reduce open expressions to their normal form
reduce :: Exp n -> Exp n
reduce (IntE x)   = IntE x
reduce (VarE n)   = VarE n
reduce (LamE t e) = LamE t (reduce e)
reduce (AppE (LamE t e1) e2)   = subst (singleSub (reduce e2)) (reduce e1)
reduce (AppE (IntE x)    e2)   = error "Type error!"
reduce (AppE e1 e2) = AppE (reduce e1) (reduce e2)




