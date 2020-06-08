
module SimpleScoped where

import Imports
import Nat
import SubstScoped

-- Syntax of Simply-Typed Lambda Calculus (STLC) types

data Ty = IntTy | Ty :-> Ty
  deriving (Eq, Show)

-- Syntax of STLC expressions, using GADT to track the scope
-- of the variables in terms

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

instance SubstC Exp where
   var = VarE

   subst s (IntE x)     = IntE x
   subst s (VarE x)     = applySub s x
   subst s (LamE ty e)  = LamE ty (subst (lift s) e)
   subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)

-- * Examples of some operations defined using this representation.

-- | is an expression a value?
value :: Exp n -> Bool
value (IntE x)   = True
value (LamE t e) = True
value _          = False

-- | Small-step evaluation
step :: Exp Z -> Maybe (Exp Z)
step (IntE x)   = Nothing
step (VarE n)   = case n of {}   -- cannot have a scope error any more
step (LamE t e) = Nothing
step (AppE (LamE t e1) e2)   = Just $ subst (singleSub e2) e1
step (AppE (IntE _) e2)      = error "Type error!"
step (AppE e1 e2) = do e1' <- step e1
                       return $ AppE e1' e2

-- | open reduction
reduce :: Exp n -> Exp n
reduce (IntE x)   = IntE x
reduce (VarE n)   = VarE n
reduce (LamE t e) = LamE t (reduce e)
reduce (AppE (LamE t e1) e2)   = subst (singleSub (reduce e2)) (reduce e1)
reduce (AppE (IntE x) e2) = error "Type error!"
reduce (AppE e1 e2) = AppE (reduce e1) (reduce e2)

