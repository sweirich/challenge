# Strongly typed System F in GHC

This project demonstrates how to define a strongly-typed representation for System F terms using the singletons library with GHC.

With a strongly-typed representation, only well-typed terms can be constructed. Language tools that manipulate such datastructures can be sure that certain invariants are maintained by the system. For example, the definition of capture-avoiding substitution is often difficult. Yet, by working with a typed representation, we can be sure that there are no scope-errors in our program. The type system of System F only included well-scoped programs.

This example is based on a de Bruijn representation of variables. What this means is that variables are represented by *indices* that count enclosing binders.

For example, consider

    data Exp = Var Idx | Lam Exp | App Exp Exp

Then the lambda calculus expression `\x y -> x` can be represented with the expression

    Lam (Lam (Var 1))

showing that the variable inside the term resolves to not the closest enclosing lamba (index 0) but the next one (index 1).

Similarly, the lambda calculus expreesion `\x -> (\y -> x y) x` can be represented with the expression

    Lam (App (Lam (App (Var 1) (Var 0))) (Var 0)

showing that the index used for the variable `x` can vary based on where the variable appears in the term. In the first case, it is underneath the binder for `y`, so must be index 1. In the second case, it is not, so must be index 0.

## Outline

1. [Simple](src/Simple.lhs)
