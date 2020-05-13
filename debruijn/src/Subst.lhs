> {-# LANGUAGE TemplateHaskell #-}
>
> module Subst where

> import Imports

Next, the representation of substitutions. We use a concrete representation of
substitutions, based on the algebraic data type below. 

-- SCW: note singletons rejects GADT syntax for Sub.

> $(singletons [d|
>     data Sub a =
>        IdS                  --  identity subst
>      | Inc                  --  increment by 1 (shift)                
>      | a :· Sub a           --  extend a substitution (like cons)
>      | Sub a :<> Sub a       --  compose substitutions
>             deriving (Eq, Show, Functor) 
>     infixr :·     -- like usual cons operator (:)
>     infixr :<>    -- like usual composition  (.)
>
>    |])


This algebra allows us to construct a number of substitution actions on types
from these primitive operations. Intuitively these operations are:

- |Inc| - A primitive substitution that increments all free variables.
  (We can also generalize this to increment by |n|. (This
  substitution is sometimes written as |(+n)| or $\uparrow^{n}$.))

For example

        ghci> subst (Inc 2) (FnTy (VarTy 0) (VarTy 1))
        FnTy (VarTy 0) (VarTy 3)

- |ty :· s| - Extend a substitution by adding a new definition for
  index Z and shifting everything in |s| one step to the right.
  
For example

        ghci> subst (IntTy :· Inc) (FnTy (VarTy 0) (VarTy 1))
        FnTy IntTy (VarTy 1)

- |IdS| - The identity substitution. When applied, leaves all variables alone.

- |s1 :∘ s2| - Compose two substitutions together. This is equivalent to
  first substituting by |s1| and then substituting by |s2|.


* Variable indices and substitution

This variable representation uses indices to represent variables. Here, an
index is just a natural number.

We can overload the type of the substitution operation by the type of the
argument that it applies to.

The main thing we want to do with a substitution |Sub| is apply it to some
term structure.  Below, we define the opeartion |subst| (which applies a
substiution) mutually with an operation |applyS| (which looks up the |nth|
term in a substitution).

The |subst| operation extends the substitution for a single index
throughout the type structure. When this function calls itself recursively
under a binder, it uses `lift` to modify the input substitution.


The |applyS| operation dispatches on the substitution algebra. In the base
case, it increments the index by |n|. For cons, if the index is zero, it
returns the type |ty|. If not, it decrements the index and looks up the value
in the substition in the tail.  For composition, it first determines the value
of the index in the first substitution, then applies the second substitution
to that type.


> $(singletons [d|
> 
>     data Idx where
>        Z :: Idx
>        S :: Idx -> Idx
>         deriving (Eq, Show)
>
>     class SubstC a where
>        var   :: Idx -> a 
>        subst :: Sub a -> a -> a

>     --  Value of the index x in the substitution s
>     applyS :: SubstC a => Sub a -> Idx -> a
>     applyS IdS            x  = var x
>     applyS Inc            x  = var (S x)
>     applyS (ty :· s)      Z  = ty
>     applyS (ty :· s)   (S x) = applyS s x
>     applyS (s1 :<> s2)    x  = subst s2 (applyS s1 x)
>
>
>   |])
>


* Derived substitutions

We can use these operations to define a singleton substitution:

> $(singletons [d|
>     singleSub :: a -> Sub a
>     singleSub t = t :· IdS
>     |])

Finally, we can define the |lift| substitution, which is exactly what we need
when working with substitutions under binders.

> $(singletons [d|
>     lift :: SubstC a => Sub a -> Sub a
>     lift s = var Z :· (s :<> Inc)
>     |])


We can also map the substitution, inc and lift operations across a list
of terms.

> $(singletons [d|
>      substList :: SubstC a => Sub a -> [a] -> [a]
>      substList s [] = []
>      substList s (t:g) = subst s t : substList s g
>
>      incList :: SubstC a => [a] -> [a]
>      incList = substList Inc
>
>      liftList :: SubstC a => Sub a -> [a] -> [a]
>      liftList s = substList (lift s)
>      |])
> 



* Optimization

In this code, we haven't paid much attention to the runtime performance of the
substitution operations that can be defined with this algebra. 


> {- NOTE: optimization for above. Won't do it now.
> applyS s x | Just f <- isIncN s = var (f x)
> isIncN :: Sub a -> Maybe (Nat -> Nat)
> isIncN IdS        = Just id
> isIncN (Inc :∘ s) = (S .) <$> isIncN s
> isIncN _          = Nothing



Using the substitution |liftN n s|, all free variables in the range |0..n-1|
are left alone, and any free variables in the range of |s| are all incremented
by |n|.

> $(singletons [d|
>     liftN :: SubstC a => Nat -> Sub a -> Sub a
>     liftN k s = upTo k (s :∘ incN k)
>
>     incN :: SubstC a => Nat -> Sub a
>     incN Z = IdS
>     incN (S n) = (Inc :∘ incN n)

>     upTo :: SubstC a => Nat -> Sub a -> Sub a
>     upTo Z s     = s
>     upTo (S m) s = upTo m (var m :· s)
>   |])

For example, if have a substitution that replaces 0 with |FnTy (BaseTy) (VarTy
0)| and leaves all other types alone, we can lift it by two steps to the
version that leaves variables 0 and 1 alone and replaces variable 2 by
|(FnTy BaseTy (VarTy 2))|.

    ghci> lift 2 ((FnTy BaseTy (VarTy Z)) :· Inc Z)
    VarTy Z :· (VarTy 1 :· ((FnTy BaseTy (VarTy Z) :· Inc Z) :∘ Inc 2))

% Quotation from Pottier:
% "In short, $\uparrow^i t$ is the term obtained by adding $i$ to every variable that
% appears free in the term $t$. The symbol $\uparrow^i$ can be intuitively read as an
% end-of-scope mark: it means that the $i$ most-recently-introduced variables are
% not in scope in the term that follows (Bird and Paterson, 1999, Hendriks and
% van Oostrom, 2003)."

> -}

> $(singletons [d| 
>     fromList :: [a] -> Sub a
>     fromList (t:ts)  = t :· fromList ts
>     fromList []      = IdS
>     |])





