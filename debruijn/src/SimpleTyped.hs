-- | A version of STLC with a strongly-typed AST
module SimpleTyped where

import Imports
import SubstTyped

-- Same definition of types as in Simple
data Ty = IntTy | Ty :-> Ty
   deriving (Eq,Show)

-- But the type of expressions now includes a context (g) and type (t)
data Exp :: [Ty] -> Ty -> Type where

 IntE   :: Int -> Exp g IntTy

 VarE   :: Idx g t               -- variable index
        -> Exp g t

 LamE   :: Π (t1 :: Ty)          -- type of binder
        -> Exp (t1:g) t2         -- body of abstraction
        -> Exp g (t1 :-> t2)

 AppE   :: Exp g (t1 :-> t2)     -- function
        -> Exp g t1              -- argument
        -> Exp g t2

-- same instance definition as before
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
-- Note that the type of this function shows that types are preserved during
-- evaluation
step :: Exp '[] t -> Maybe (Exp '[] t)
step (IntE x)     = Nothing
step (VarE n)     = case n of {}
step (LamE t e)   = Nothing
step (AppE e1 e2) = Just $ stepApp e1 e2 where

    -- Helper function for the AppE case. This function "proves" that we will
    -- *always* take a step if a closed term is an application expression.
    stepApp :: Exp '[] (t1 :-> t2) -> Exp '[] t1  -> Exp '[] t2
    --stepApp (IntE x)       e2 = error "Type error"
    stepApp (VarE n)       e2 = case n of {}
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
stepV (VarE n)     = case n of {}
stepV (LamE t e)   = Left (LamV t e)
stepV (AppE e1 e2) = stepApp e1 e2 where
    stepApp :: Exp '[] (t1 :-> t2) -> Exp '[] t1  -> Either (Val '[] t2) (Exp '[] t2)
    --stepApp (IntE x)       e2 = error "Type error"
    stepApp (VarE n)       e2 = case n of {}
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
eval (VarE n) = case n of {}
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


-----------------------------------------------------------------------
-- Evaluation to normal form

-- The key take away is that this is mostly boilerplate.

-- Yet another variant of 'Exp'.
--
-- How handy that Neutral and Normal start with letter N.
--
newtype Norm g t = Norm (GenNorm Norm g t)
type Neut = GenNeut Norm

-- We define more generic version of 'Norm' and 'Neut',
-- so we can define
data GenNeut :: ([Ty] -> Ty -> Type) -> [Ty] -> Ty -> Type where
 VarN   :: Idx g t               -- variable index
        -> GenNeut norm g t

 AppN   :: GenNeut norm g (t1 :-> t2)     -- function
        -> norm      g t1              -- argument
        -> GenNeut norm g t2

data GenNorm :: ([Ty] -> Ty -> Type) -> [Ty] -> Ty -> Type where
 IntN   :: Int
        -> GenNorm norm g IntTy

 LamN   :: Π (t1 :: Ty)           -- type of binder
        -> norm (t1:g) t2         -- body of abstraction
        -> GenNorm norm g (t1 :-> t2)

 NeutN :: GenNeut norm g t -> GenNorm norm g t

-- | Like 'reduce' but using 'Norm' as result.
--
-- We can remove the equation
--
--     reduce (AppE (LamE t e1) e2) = ...
--
-- from the definition of 'reduce' - and we won't notice the cheat.
-- with 'Norm' type-check is unforgiving.
--
-- (In fact, I think that 'reduce'  some redexes)
--
reduceN :: Exp g t -> Norm g t
reduceN (IntE x)   = Norm (IntN x)
reduceN (VarE x)   = Norm (NeutN (VarN x))
reduceN (LamE t e) = Norm (LamN t (reduceN e))
reduceN (AppE e1 e2) = case evalW e1 of
  NeutN e1'  -> Norm (NeutN (AppN (reduceW e1') (reduceN e2)))
  LamN t e1' ->
      -- here we have various reduction strategies
      -- The following is easiest without any additional machinery,
      -- substitute terms as is. This most likely duplicates work.
      --
      --   reduceN (subst (singleSub e2) e1')
      --
      -- or we can do
      --
      --  reduceN (subst (singleSub (norm2exp (reduceN e2))) (norm2exp (reduceN e1')))
      --  ^ I think the reduceN after subst is missing from 'reduce' on 'Exp'.
      --
      -- or we can define substitution on 'Norm'!
      --
      subst (singleSub (reduceN e2)) (reduceN e1')

      -- these three strategies reduce differenty, but
      -- the types tell that we get a normal form at the end.
      -- (And the meta-theory tells that it will be the same).

-- again, (almost) the same instance definition as before.
instance SubstDB Norm where
   var = Norm . NeutN . VarN

   subst s (Norm (IntN x))         = Norm (IntN x)
   subst s (Norm (LamN ty e))      = Norm (LamN ty (subst (lift s) e))
   subst s (Norm (NeutN (VarN x))) = applySub s x

   -- substitution in application causes evaluation,
   -- i.e. recursive substitutions.
   subst s (Norm (NeutN (AppN e1 e2))) = case subst s (Norm (NeutN e1)) of
     Norm (NeutN e1')   -> Norm (NeutN (AppN e1' e2'))
     Norm (LamN ty e1') -> subst (singleSub e2') e1'
     where
       e2' = subst s e2

-- | A helper for 'reduceN', fully evaluate
reduceW :: GenNeut Exp g t ->  GenNeut Norm g t
reduceW (VarN n)     = VarN n
reduceW (AppN e1 e2) = AppN (reduceW e1) (reduceN e2)

norm2exp :: Norm g t -> Exp g t
norm2exp (Norm (IntN x))   = IntE x
norm2exp (Norm (LamN t x)) = LamE t (norm2exp x)
norm2exp (Norm (NeutN e))  = neut2exp e

neut2exp :: Neut g t -> Exp g t
neut2exp (VarN x) = VarE x
neut2exp (AppN e1 e2) = AppE (neut2exp e1) (norm2exp e2)

-- | A term in WHNF is normal form where
-- non-head positions (lambda body, application argument) aren't
-- evaluated, i.e. are 'Exp'.
type WHNF = GenNorm Exp

-- | Like 'evalW but in any context.
evalW :: Exp g t -> WHNF g t
evalW (IntE x)     = IntN x
evalW (VarE n)     = NeutN (VarN n)
evalW (LamE t e)   = LamN t e
evalW (AppE e1 e2) = case evalW e1 of
  LamN t e1' -> evalW $ subst (singleSub e2) e1'
  NeutN e1'  -> NeutN (AppN e1' e2)
