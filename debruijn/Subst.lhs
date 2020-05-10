> {-# LANGUAGE TemplateHaskell #-}
> 
> module Subst where

> import Nat
> import Imports

Next, the representation of substitutions. We use a concrete representation of
substitutions, based on the algebraic data type below. 

> $(singletons [d|
>     data Sub a =
>         Inc Nat                --  increment by n (shift)                
>      |  a  :· Sub a            --  extend a substitution (like cons)
>      |  Sub a :∘  Sub a        --  compose substitutions
>          deriving (Eq, Show)
>     infixr :·    -- like usual cons operator (:)
>     infixr :∘    -- like usual composition  (.)
>    |])


This algebra allows us to construct a number of substitution actions on types
from these primitive operations. Intuitively these operations are:

* |Inc n| - A primitive substitution that increments all free variables that
  appear in a type by |n|. (This substitution is sometimes written as
  |(+n)| or $\uparrow^{n}$.)

For example

        ghci> subst (Inc 2) (FnTy (VarTy Z) (VarTy 1))

* |ty :· s| - Extend a substitution by adding a new definition for
  index Z and shifting everything in |s| one step to the right.
  
For example

        ghci> subst (BaseTy :· Inc Z) (FnTy (VarTy Z) (VarTy 1))
        FnTy BaseTy (VarTy Z)
		

* |s1 :∘ s2| - Compose two substitutions together. This is equivalent to
  first substituting by |s1| and then substituting by |s2|.

These three substitution operations are all that we need.  For example, we can
define an identity substitution by incrementing by zero.

> $(singletons [d|
>     idSub :: Sub a
>     idSub = Inc Z
>     |])

Furthermore, we can use the cons and identity substitutions to define
|fromList| the conversion of a list of types to a substitution. In the result,
the $i$th free variable is replaced by the $i$th type in the list, and all
other free variables are left alone.


> $(singletons [d| 
>     fromList :: [a] -> Sub a
>     fromList (t:ts)  = t :· fromList ts
>     fromList []      = idSub
>     |])


> class Subst a where
>    var   :: Nat -> a 
>    subst :: Sub a -> a -> a 

> -- | Value of the index x in the substitution s
> applyS :: Subst a => Sub a -> Nat -> a
> applyS (Inc n)        x  = var (n + x)           
> applyS (ty :· s)      Z  = ty
> applyS (ty :· s)   (S x) = applyS s x
> applyS (s1 :∘ s2)     x  = subst s2 (applyS s1 x)

Finally, we can define the |lift| substitution, which is exactly what we need
when working with substitutions under binders.  Using the substitution |lift n
s|, all free variables in the range |0..n-1| are left alone, and any free
variables in the range of |s| are all incremented by |n|.

> lift :: Subst a => Nat -> Sub a -> Sub a
> lift k s = upTo k (s :∘ Inc k)

> upTo :: Subst a => Nat -> Sub a -> Sub a
> upTo Z s = s
> upTo (S m) s = upTo m (var m :· s)

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

The main thing we want to do with a substitution |Sub| is apply it to a type.
Below, we define the opeartion |subst| (which applies a substiution to a type)
mutually with an operation |applyS| (which looks up the |nth| type in a
substitution).

The |subst| operation extends the substitution for a single index
throughout the type structure. When this function calls itself recursively
under a binder, it uses `lift` to modify the input substitution.

The |applyS| operation dispatches on the substitution algebra. In the base
case, it increments the index by |n|. For cons, if the index is zero, it
returns the type |ty|. If not, it decrements the index and looks up the value
in the substition in the tail.  For composition, it first determines the value
of the index in the first substitution, then applies the second substitution
to that type.
