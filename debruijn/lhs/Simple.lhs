> {-# LANGUAGE TemplateHaskell #-}
> 
> module Simple where

> import Imports
> import Subst

Let's start with an example of the simply-typed lambda calculus (STLC).

* Syntax

First, we need some types.

> data Ty = IntTy | Ty :-> Ty
>   deriving (Eq, Show)

Now, let's define the syntax of STLC.

> data Exp :: Type where
>   IntE   :: Int
>          -> Exp
>   VarE   :: Idx
>          -> Exp 
>   LamE   :: Ty       -- type of binder
>          -> Exp      -- body of abstraction
>          -> Exp          
>   AppE   :: Exp      -- function
>          -> Exp      -- argument
>          -> Exp
>      deriving (Eq, Show)

* Substitution

We can create an instance of the `SubstC` class by defining the substitution
operation for this term.

> instance SubstC Exp where
>    var = VarE
> 
>    subst s (IntE x)     = IntE x
>    subst s (VarE x)     = applySub s x
>    subst s (LamE ty e)  = LamE ty (subst (lift s) e)
>    subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)

* Examples

Let's write a small-step substitution-based evaluator for this language.

> -- | is an expression a value?
> value :: Exp -> Bool
> value (IntE x)   = True
> value (LamE t e) = True
> value _          = False

> -- | Small-step evaluation
> step :: Exp -> Maybe Exp
> step (IntE x)   = Nothing
> step (VarE n)   = error "Unbound Variable"
> step (LamE t e) = Nothing
> step (AppE (LamE t e1) e2)   = Just $ subst (singleSub e2) e1
> step (AppE e1 e2) | value e1 = error "Type error!"
> step (AppE e1 e2) = do e1' <- step e1
>                        return $ AppE e1' e2

> -- | open reduction
> reduce :: Exp -> Exp
> reduce (IntE x)   = IntE x
> reduce (VarE n)   = VarE n
> reduce (LamE t e) = LamE t (reduce e)
> reduce (AppE (LamE t e1) e2)   = subst (singleSub (reduce e2)) (reduce e1)
> reduce (AppE e1 e2) | value e1 = error "Type error!"
> reduce (AppE e1 e2) = AppE (reduce e1) (reduce e2)





