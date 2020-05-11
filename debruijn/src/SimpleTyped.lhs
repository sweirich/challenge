> {-# LANGUAGE TemplateHaskell #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
> 
> module SimpleTyped where

> import Imports
> import SubstTyped

Let's start with an example of the simply-typed lambda calculus (STLC), using a
strongly typed term representation.

First, we need some types, a base type and a form for function types.

> data Ty = IntTy | Ty :-> Ty

Now, let's define the syntax of STLC using a GADT.

> data Exp :: [Ty] -> Ty -> Type where

>  IntE   :: Int -> Exp g IntTy
  
>  VarE   :: Var g t               -- variable index
>         -> Exp g t
         
>  LamE   :: Sing t1               -- type of binder
>         -> Exp (t1:g) t2         -- body of abstraction
>         -> Exp g (t1 :-> t2)
         
>  AppE   :: Exp g (t1 :-> t2)     -- function
>         -> Exp g t1              -- argument
>         -> Exp g t2

Let's write an evaluator for this language.

> -- | A proof of False
> data False where
>    IsFalse :: (forall a . a) -> False


> eval :: Exp '[] t -> Exp '[] t
> eval (AppE e1 e2) = 
>    case unLam (eval e1) of
>       Left (IsFalse k) -> k
>       Right e11        -> subst (singleSub e2) e11
> eval (IntE x)     = IntE x
> eval (VarE v)     = case v of 
> eval (LamE ty e)  = LamE ty e

> -- | The only error allowed is if we don't evaluate the term
> -- completely. Maybe this example would be better as a small-step
> -- semantics.
> 
> unLam :: Exp '[] (t1 :-> t2) -> Either False (Exp '[t1] t2)
> unLam (LamE t1 e11) = Right e11
> unLam (AppE e1 e2)  = case unLam e1 of
>                         Left i -> Left i
>                         Right _ -> error "Found a non-value"
> unLam (VarE v)      = Left (IsFalse (case v of))



> instance SubstC Exp where
>    var = VarE
> 
>    subst s (IntE x)     = (IntE x)
>    subst s (VarE x)     = applyS s x
>    subst s (LamE ty e)  = LamE ty (subst (lift s) e)
>    subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)

