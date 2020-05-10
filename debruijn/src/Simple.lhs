> {-# LANGUAGE TemplateHaskell #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
> 
> module Simple where

> import Imports
> import Nat

Let's start with an example of the simply-typed lambda calculus (STLC), using a
strongly typed term representation.

First, we need some types, a base type and a form for function types.

> $(singletons [d| data Ty = Base | Ty :-> Ty |])

Now, let's define the syntax of STLC using a GADT.

> type Context = [Ty]

> data Exp :: Context -> Ty -> Type where

>  BaseE  :: Exp g Base
  
>  VarE   :: (g !! n ~ t)          -- scope requirement
>         => Sing n                -- variable index
>         -> Exp g t
         
>  LamE   :: Sing t1               -- type of binder
>         -> Exp (t1:g) t2         -- body of abstraction
>         -> Exp g (t1 :-> t2)
         
>  AppE   :: Exp g (t1 :-> t2)     -- function
>         -> Exp g t1              -- argument
>         -> Exp g t2

Let's write a safe evaluator for this language.


> type family Interp (t :: Ty) :: Type where
>    Interp Base        = ()
>    Interp (t1 :-> t2) = Interp t1 -> Interp t2

> eval :: Env g -> Exp g t -> Interp t
> eval env BaseE    = ()
> eval env (VarE n) = lookupEnv env n
> eval env (LamE _ e) = \ x -> eval (ECons x env) e
> eval env (AppE e1 e2) = (eval env e1) (eval env e2)

> data Env (g :: Context) where
>    ENil  :: Env '[]
>    ECons :: Interp t -> Env g -> Env (t ': g)
> 
> lookupEnv :: (g !! n ~ t) => Env g -> Sing n -> Interp t
> lookupEnv ENil SZ = error "impossible"
> lookupEnv ENil (SS n) = error "impossible"
> lookupEnv (ECons x xs) SZ = x
> lookupEnv (ECons x xs) (SS n) = lookupEnv xs n
