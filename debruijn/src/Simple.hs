
module Simple where

import Imports
import Nat
import Subst

-- Syntax of Simply-Typed Lambda Calculus (STLC) types

data Ty = IntTy | Ty :-> Ty
  deriving (Eq, Show)

-- Syntax of STLC expressions, using GADT syntax for comparison
-- with later approaches

data Exp :: Type where
  IntE   :: Int      -- literal ints
         -> Exp
  VarE   :: Idx      -- variables (Idx is defined in Subst)
         -> Exp 
  LamE   :: Ty       -- type of binder
         -> Exp      -- body of abstraction
         -> Exp          
  AppE   :: Exp      -- function
         -> Exp      -- argument
         -> Exp
     deriving (Eq, Show)

instance SubstDB Exp where
   var = VarE

   subst s (IntE x)     = IntE x
   subst s (VarE x)     = applySub s x 
   subst s (LamE ty e)  = LamE ty (subst (lift s) e)
   subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)

-------------------------------------------------------------------------
-- * Examples of some operations defined using this representation.


-- | Small-step evaluation
step :: Exp -> Maybe Exp
step (IntE x)     = Nothing
step (VarE n)     = error "Unbound Variable"
step (LamE t e)   = Nothing
step (AppE e1 e2) = Just $ stepApp e1 e2 where

   stepApp :: Exp -> Exp -> Exp 
   stepApp (IntE x)       e2 = error "Type error"
   stepApp (VarE n)       e2 = error "Unbound variable"
   stepApp (LamE t e1)    e2 = subst (singleSub e2) e1
   stepApp (AppE e1' e2') e2 = AppE (stepApp e1' e2') e2
                       
-- | open reduction
reduce :: Exp -> Exp
reduce (IntE x)   = IntE x
reduce (VarE n)   = VarE n
reduce (LamE t e) = LamE t (reduce e)
reduce (AppE (LamE t e1) e2) = subst (singleSub (reduce e2)) (reduce e1)
reduce (AppE (IntE x) e2)    = error "type error" -- don't have to observe this type error, but we can
reduce (AppE e1 e2)          = AppE (reduce e1) (reduce e2) where

-----------------------------------------------------------------------
  
-- | Type checker
typeCheck :: [Ty] -> Exp -> Maybe Ty
typeCheck g (IntE i)    = return IntTy
typeCheck g (VarE j)    = indx g j
typeCheck g (LamE t1 e) = do
  t2 <- typeCheck (t1:g) e
  return (t1 :-> t2)
typeCheck g (AppE e1 e2) = do
  t1 <- typeCheck g e1
  t2 <- typeCheck g e2
  case t1 of
    t12 :-> t22
      | t12 == t2 -> Just t22
    _ -> Nothing

------------------------------------------------------------
-- Example terms

-- \(x :: Int) -> \(y :: Int) -> x
example1 :: Exp 
example1 = LamE IntTy (LamE IntTy (VarE 1))