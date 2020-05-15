# Strongly typed System F in GHC (Part I)

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

## Substitution with de Bruijn indices

Reference files [Subst](src/Subst.lhs) and 
   [Simple](src/Simple.lhs)

While *representing* terms using indices is not so difficult, things get a bit more complex when we try to define capture-avoiding substitution for open terms. This is the part where my brain starts to explode.  What is tricky about it?

Consider a beta-reduction for  $(\lambda x. M) N$. We implement this operation via substitution, i.e. $[x |-> N]M$.  But with de Bruijn indices, we have to do *three* things:

1. Find all occurrences of x in M and replace them by N. These start out as "0" but as the operation traverses under binders, the index we are looking for increases.

2. As we go under binders, we are moving N from one scope to another. That means all *free* variables in $N$ need to be *incremented* for each binder that we enter (as they now refer to one more level out).

3. The free variables in $M$, besides $x$, need to be *decremented* by one because we have removed the top level binder.

So when substituting, we often need to do more than just replace one variable --- we often have to *shift* other variables as well.

### Substitutions as functions

To visualize how this works, we will work with parallel substitutions, i.e. we 
can visualize a substitution as a *total function* from indices (e.g. natural numbers) to terms.

    type Sub = Nat -> Exp

Then the substitution operation, takes one of these functions and applies it to all variables found in the term, being sure to increment the free variables in the range of the substition, with an operation called `lift` below.

    subst :: Sub -> Exp -> Exp
    subst s (Var i)     = s i
    subst s (App e1 e2) = App (subst s e1) (subst s e2)
    subst s (Lam e)     = Lam (lift s) e

For example, the identity substitution looks like this: it maps all indices to the corresponding variable.

    idSub = \ i -> Var i

We can have a substitution that *increments* or shifts all variables by adding some amount (k) to each index. (This generalizes the identity substitution above when k is 0).

    inc k = \ i -> Var (k + i)

On the other hand, a substitution that maps index 0 to n and decrements all other variables might look like this:

    single n = \ i -> if i == 0 then n else Var (i - 1) 

We can also think about operations that modify substitutions. For example, we can define a `cons` operation, thus
  
    (|>) :: Exp -> Sub -> Sub 
    n |> s = \i -> if i == 0 then n else s (i - 1)

and use it to define `single n` as

    single n = n :> idSub

Furthermore, because substitutions are functions, we should be able to compose them. We can do this by using the `subst` operation above to apply the second substition to the result of looking up the index with the first substition. 

    (<>) :: Sub -> Sub -> Sub
    s1 <> s2 = \i -> subst s2 (s1 i)

This composition operation allows us to define the `lift` operation above. To lift a substitution at a binder, we need a new substitution that leaves variable 0 alone, but then increments all of the free variables in the range of the original substitution.

    lift s = Var 0 |> (s <> inc 1)  

### Defunctionalized substitutions

The narrative above describes all that we want to do with substitutions. That means that we can "defunctionalize" 
these operations and use a data type to represent them.

    data Sub  =
        Inc Idx        -- primtive increment            
      | Exp :> Sub     -- extend (i.e. cons)
      | Sub :<> Sub     -- compose

    -- apply a substitution to an index
    applyS :: Sub -> Nat -> Exp
    applyS (Inc k)        x  = Var (k + x)
    applyS (ty :> s)      Z  = ty
    applyS (ty :> s)   (S x) = applyS s x
    applyS (s1 :<> s2)     x  = subst s2 (applyS s1 x)

The advantage of the defunctionalized version is that (1) it is easier for us to see what is going on when we work with datatypes than with functions and (2) if we wanted to we could optimize this representation before applying it to an expression. For example `Inc k <> Inc l` is equal to 
`Inc (k + l)`. And if we ever have `subst s1 (subst s2 e)` we can fuse the two traversals into `subst (s1 <> s2) e`.

### Generalized substitutions

The above development specializes the `Sub` datatype and associated operations to `Exp`. However, there are only two places above that depend on this type definition: the use of `Var` in the first line of `applyS` above, and the traversal of the datatype in the definition of `subst`. Therefore, we can defined a type class that generalizes types that have these operations:

    class SubstC a where
       var   :: Idx -> a 
       subst :: Sub a -> a -> a

and then instantiate this class with each datatype that we would like to use with substitution

    instance SubstC Exp where
      var = Var
      subst s (Var i)     = s i
      subst s (App e1 e2) = App (subst s e1) (subst s e2)
      subst s (Lam e)     = Lam (lift s) e

## Type-indexed substitutions

Reference files [SubstTyped](src/SubstTyped.hs) and [SimpleTyped](src/SimpleTyped.hs).

The above AST for expressions is not type-indexed. It can represent nonsensical STLC terms. 

GADTs 