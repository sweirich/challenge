> {-# LANGUAGE TemplateHaskell #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
> 
> module Simple where

> import Imports
> import Nat
> import Subst

Let's start with an example of the simply-typed lambda calculus (STLC).

First, we need some types.

> data Ty = IntTy | Ty :-> Ty
>   deriving (Eq, Show)

Now, let's define the syntax of STLC.

> data Exp :: Type where

>  IntE   :: Int -> Exp
>  VarE   :: Nat
>         -> Exp 
>  LamE   :: Ty       -- type of binder
>         -> Exp      -- body of abstraction
>         -> Exp          
>  AppE   :: Exp      -- function
>         -> Exp      -- argument
>         -> Exp
>    deriving (Eq, Show)

Let's write a small-step substitution-based evaluator for this language.

> eval :: Exp -> Exp
> eval (AppE e1 e2) = 
>    case eval e1 of
>       LamE ty e11 -> subst (singleSub e2) e11
>       _ -> error "Type Error!"
> eval (IntE x) = IntE x
> eval (VarE x) = error $ "Unbound variable: " ++ show x
> eval (LamE ty e) = LamE ty e


> instance SubstC Exp where
>    var = VarE
> 
>    subst s (IntE x)     = (IntE x)
>    subst s (VarE x)     = applyS s x
>    subst s (LamE ty e)  = LamE ty (subst (lift s) e)
>    subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)



