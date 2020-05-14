-- | A version of STLC with a strongly-typed AST
module SimpleTyped where

import Imports
-- need a typed version of the substitution
import SubstTyped

-- Same definition of types as in Simple
data Ty = IntTy | Ty :-> Ty
   deriving (Eq,Show)

-- But expression datatype includes a context (g) and type
data Exp :: [Ty] -> Ty -> Type where

 IntE   :: Int -> Exp g IntTy

 VarE   :: Idx g t               -- variable index
        -> Exp g t

 LamE   :: Sing t1               -- type of binder
        -> Exp (t1:g) t2         -- body of abstraction
        -> Exp g (t1 :-> t2)

 AppE   :: Exp g (t1 :-> t2)     -- function
        -> Exp g t1              -- argument
        -> Exp g t2
 

instance SubstC Exp where
   var = VarE

   subst s (IntE x)     = IntE x
   subst s (VarE x)     = applyS s x
   subst s (LamE ty e)  = LamE ty (subst (lift s) e)
   subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)


-----------------------------------------------------------------------
-- | is an expression a value?
value :: Exp g t -> Bool
value (IntE x)   = True
value (LamE t e) = True
value _          = False

-- | Small-step evaluation
step :: Exp '[] t -> Maybe (Exp '[] t)
step (IntE x)   = Nothing
step (VarE n)   = error "Unbound Variable"
step (LamE t e) = Nothing
step (AppE (LamE t e1) e2)   = Just $ subst (singleSub e2) e1
step (AppE e1 e2) | value e1 = error "Type error!"
step (AppE e1 e2) = do e1' <- step e1
                       return $ AppE e1' e2

-- | open reduction
reduce :: Exp g t -> Exp g t
reduce (IntE x)   = IntE x
reduce (VarE n)   = VarE n
reduce (LamE t e) = LamE t (reduce e)
reduce (AppE (LamE t e1) e2)   = subst (singleSub (reduce e2)) (reduce e1)
reduce (AppE e1 e2) | value e1 = error "Type error!"
reduce (AppE e1 e2) = AppE (reduce e1) (reduce e2)

-- | A proof of False
data False where
   IsFalse :: (forall a . a) -> False

eval :: Exp '[] t -> Exp '[] t
eval (AppE e1 e2) = 
   case unLam (eval e1) of
      Left (IsFalse k) -> k
      Right e11        -> subst (singleSub e2) e11
eval (IntE x)     = IntE x
eval (VarE v)     = case v of 
eval (LamE ty e)  = LamE ty e

-- | The only error allowed is if we don't evaluate the term
-- completely. Maybe this example would be better as a small-step
-- semantics.

unLam :: Exp '[] (t1 :-> t2) -> Either False (Exp '[t1] t2)
unLam (LamE t1 e11) = Right e11
unLam (AppE e1 e2)  = case unLam e1 of
                        Left i -> Left i
                        Right _ -> error "Found a non-value"
unLam (VarE v)      = Left (IsFalse (case v of))

