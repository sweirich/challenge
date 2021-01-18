-- | A version of STLC with a strongly-typed AST
{-# LANGUAGE TemplateHaskell #-}
module SimpleTyped where

import Imports
import Data.Singletons.TH
import SubstTyped

-- Same definition of types as in Simple
$(singletons [d|
   data Ty = IntTy | Ty :-> Ty
      deriving (Eq,Show)
   |])

-- But the type of expressions now includes a context (g) and type (t)
data Exp :: [Ty] -> Ty -> Type where

 IntE   :: Int -> Exp g IntTy

 VarE   :: !(Idx g t)            -- variable index
        -> Exp g t               -- important to make this strict

 LamE   :: Π (t1 :: Ty)          -- type of binder
        -> Exp (t1:g) t2         -- body of abstraction
        -> Exp g (t1 :-> t2)

 AppE   :: Exp g (t1 :-> t2)     -- function
        -> Exp g t1              -- argument
        -> Exp g t2

-- same instance definition as before
instance SubstDB Exp where
   var = VarE

   rename s (IntE x)     = IntE x
   rename s (VarE x)     = VarE (s x)
   rename s (LamE ty e)  = LamE ty (rename (liftRename s) e)
   rename s (AppE e1 e2) = AppE (rename s e1) (rename s e2)

   subst s (IntE x)     = IntE x
   subst s (VarE x)     = applySub s x
   subst s (LamE ty e)  = LamE ty (subst (lift s) e)
   subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)

-----------------------------------------------------------------------

instance Show (Exp g t) where
  show (IntE i)     = show i
  show (VarE x)     = "v" ++ show (idxToInt x)
  show (LamE t e)   = "\\" ++ show t ++ "." ++ show e
  show (AppE e1 e2) = show e1 ++ parens e2 (show e2) where
      parens (IntE _) s = s
      parens (VarE _) s = s
      parens _ s = "(" ++ s ++ ")"


-----------------------------------------------------------------------
-- Examples

ex :: Exp '[] ('IntTy ':-> 'IntTy)
ex = AppE (LamE (SIntTy :%-> SIntTy) (VarE Z)) (LamE SIntTy (VarE Z))

-- | Small-step evaluation of closed terms.
--
-- Either return the next term or Nothing, if the term is already a value.
-- Note that the type of this function shows that types are preserved during
-- evaluation
step :: Exp '[] t -> Maybe (Exp '[] t)
step (IntE x)     = Nothing
--step (VarE n)     = error "Unbound variable"
step (LamE t e)   = Nothing
step (AppE e1 e2) = Just $ stepApp e1 e2 where

    -- Helper function for the AppE case. This function "proves" that we will
    -- *always* take a step if a closed term is an application expression.
    stepApp :: Exp '[] (t1 :-> t2) -> Exp '[] t1  -> Exp '[] t2
    --stepApp (IntE x)       e2 = error "Type error"
    --stepApp (VarE n)       e2 = error "Unbound variable"
    stepApp (LamE t e1)    e2 = subst (singleSub e2) e1
    stepApp (AppE e1' e2') e2 = AppE (stepApp e1' e2') e2

-- | Big-step evaluation of closed terms
-- To do this correctly, we need to define a separate type
-- for values.
data Val :: [Ty] -> Ty -> Type where
  IntV :: Int -> Val g IntTy
  LamV :: Π (t1 :: Ty)          -- type of binder
        -> Exp (t1:g) t2        -- body of abstraction
        -> Val g (t1 :-> t2)

-- | Like 'step', but return a 'Val' if the term is already a value.
stepV :: Exp '[] t -> Either (Val '[] t) (Exp '[] t)
stepV (IntE x)     = Left (IntV x)
--stepV (VarE n)     = error "Unbound variable"
stepV (LamE t e)   = Left (LamV t e)
stepV (AppE e1 e2) = stepApp e1 e2 where
    stepApp :: Exp '[] (t1 :-> t2) -> Exp '[] t1  -> Either (Val '[] t2) (Exp '[] t2)
    --stepApp (IntE x)       e2 = error "Type error"
    --stepApp (VarE n)       e2 = error "Unbound variable"
    stepApp (LamE t e1)    e2 = Right (subst (singleSub e2) e1)
    stepApp (AppE e1' e2') e2 = Right (AppE (either val2exp id (stepApp e1' e2')) e2)

-- | Convert 'Val' to 'Exp'.
--
-- Good check, that we haven't added extras.
val2exp :: Val g t -> Exp g t
val2exp (IntV x)   = IntE x
val2exp (LamV t x) = LamE t x

eval :: Exp '[] t -> Val '[] t
eval (IntE x) = IntV x
--eval (VarE n) = error "Unbound variable"
eval (LamE t e) = LamV t e
eval (AppE e1 e2) =
  case eval e1 of
    (LamV t e1') -> eval (subst (singleSub e2) e1')

-- | Open, parallel reduction (i.e. reduce under lambda expressions)
-- This doesn't fully reduce the lambda term to normal form in one step
reduce :: Exp g t -> Exp g t
reduce (IntE x)   = IntE x 
reduce (VarE n)   = VarE n
reduce (LamE t e) = LamE t (reduce e)
reduce (AppE e1 e2) = case reduce e1 of
  -- IntE x    -> error "type error" -- don't have to observe this type error, but we can  
  LamE t e1 -> subst (singleSub (reduce e2)) e1
  e1'       -> AppE e1' (reduce e2)
