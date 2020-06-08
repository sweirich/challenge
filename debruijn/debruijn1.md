# Part I: A tutorial on substitution with de Bruijn indices

*Reference files:* [Subst](src/Subst.hs) and [Simple](src/Simple.hs)

## Representing binding with de Bruijn indices

This example is based on a de Bruijn representation of variables. What this means is that variables are represented by *indices* that count enclosing binders, i.e. natural numbers.

For example, consider

```haskell
type Idx = Nat -- an index is just a natural number.

data Ty = IntTy | Ty :-> Ty   -- s

data Exp = IntE Int | VarE Idx | LamE Exp | AppE Exp Exp
```

Then the lambda calculus expression `\(x :: Int) (y :: Int) -> x` can be represented with the expression

```haskell
LamE IntTy (LamE IntTy (VarE 1))
```

showing that the variable inside the term resolves to not the closest enclosing lambda (index 0) but the next one (index 1).

Similarly, the lambda calculus expression `\(x :: t1) -> (\(y :: t2) -> x y) x` can be represented with the expression

```haskell
LamE t1 (AppE (LamE t2 (AppE (VarE 1) (VarE 0))) (VarE 0)
```

showing that the index used for the variable `x` can vary based on where the variable appears in the term. In the first case, it is underneath the binder for `y`, so must be index `1`. In the second case, it is not, so must be index `0`.

## Substitution and de Bruijn indices

While *representing* terms using indices is not so difficult, things get a bit more complex when we try to define capture-avoiding substitution for open terms. This is the part where my brain starts to explode.  Why is it so tricky?

Consider a beta-reduction for a lambda calculus expression `(\ x -> M) N`. To reduce this term, we need to substitute, i.e. we need some substitution function, sometimes written `[x |-> N]M`. But what is the definition of this operation when variables are represented as indices?

With de Bruijn indices, the substitution operation must do *three* things [1]:

1. Find all occurrences of `x` in `M` and replace them by `N`. These occurrences start out as `Var 0` but as the operation traverses under binders, the index corresponding to `x` increases.

2. As we go under binders, we are also moving `N` from one scope to another. That means all *free* variables in `N` need to be *incremented* for each binder that we enter (as they now refer to one more level out).

3. The free variables in `M`, besides `x`, also need to be *decremented* by one because we have removed the top level binder.

So when substituting, we often need to do more than just replace one variable --- we often have to *shift* the indices of other variables as well.

### Substitutions as functions

To visualize how this works, we will work with parallel substitutions, i.e. we  can visualize a substitution as a *total function* from indices (e.g. natural numbers) to terms.

```haskell
type Sub = Idx -> Exp
```

Then the substitution operation, called `subst` below, takes a `Sub` and applies it to *all* variable occurrences found in the term, both bound and free.

```haskell
subst :: Sub -> Exp -> Exp
subst s (IntE x)     = IntE x
subst s (VarE i)     = s i
subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)
subst s (LamE ty e)  = LamE ty (lift s) e
```

To make this work, in the context of the the three constraints above, this operation must modify its `Sub` argument whenever it traverses under a binder. This modification is done by the operation `lift`, which we will develop below.  

For example, the identity substitution looks like this---it maps all indices to the corresponding variable. Because this substitution does nothing, we call it `nil`.

```haskell
nil = \ i -> VarE i
```

More generally we can define a substitution that *increments* or shifts all variables by adding some amount (`k`) to each index. (This operation is the identity substitution when `k` is 0).

```haskell
inc k = \ i -> VarE (k + i)
```

Substitutions need not act uniformly on indices. For example, the substitution below maps the variable at index 0 to some term `n` and decrements all other indices.

```haskell
single n = \ i -> if i == 0 then n else VarE (i - 1)
```

We can also think about operations that modify substitutions. For example, the `cons` operation, defined below, generalizes the definition above by generalizing over the result at other indices.
  
```haskell  
(<|) :: Exp -> Sub -> Sub 
n <| s = \i -> if i == 0 then n else s (i - 1)
```

With `<|`, we can define `single` as

```haskell
single n = n <| nil
```

Furthermore, because substitutions are functions, we should be able to compose them. We can do this by using the `subst` operation above to apply the second substitution to the result of looking up the index with the first substitution. 

```haskell
(<>) :: Sub -> Sub -> Sub
s1 <> s2 = \i -> subst s2 (s1 i)
```

This composition operation allows us to define the `lift` operation above. To lift a substitution `s` at a binder, we need a new substitution that leaves variable 0 alone, shifts the indices of the domain of `s` and but increments all of the free variables in the range of `s`.

```haskell
lift s = Var 0 |> (s <> inc 1)  
```

### Defunctionalized substitutions

The narrative above describes all that we want to do with substitutions. That means that we can "defunctionalize" our three primitive substitution operations and use a data type to represent them.

```haskell
data Sub  =
    Inc Idx         -- primitive increment
  | Exp :<| Sub     -- extend (i.e. cons)
  | Sub :<> Sub     -- compose

-- apply a substitution to an index
applySub :: Sub -> Nat -> Exp
applySub (Inc k)         x  = VarE (k + x)
applySub (ty :<| s)      Z  = ty
applySub (ty :<| s)   (S x) = applySub s x
applySub (s1 :<> s2)     x  = subst s2 (applySub s1 x)
```

The advantage of the defunctionalized version is that (1) it is easier for us to see what is going on when we work with datatypes than with functions and (2) if we wanted to we could optimize this representation before applying it to an expression. For example `Inc k <> Inc l` is equal to `Inc (k + l)`. And if we ever have `subst s1 (subst s2 e)` we can fuse the two traversals together into `subst (s1 :<> s2) e`. (See the module [SubstTypedOpt](src/SubstTypedOpt.hs) for more details.

### Generic substitutions

The above development specializes the `Sub` datatype and associated operations to `Exp`. Do we need to repeat this code every time we want to implement lift? Looking closely above, there are only two places that depend on the type `Exp`: the use of `Var` in the first line of `applyS` and the actual traversal of the datatype in the definition of `subst`.

Therefore, we can define a type class to classify all types that have these operations:

```haskell
class SubstDB a where
   var   :: Idx -> a
   subst :: Sub a -> a -> a
```

and then instantiate this class with each datatype that we would like to use with substitution [2].

```haskell
instance SubstDB Exp where
  var = Var
  subst s (IntE x)    = IntE x
  subst s (Var i)     = applySub s i
  subst s (App e1 e2) = AppE (subst s e1)(subst s e2)
  subst s (Lam ty e)  = LamE ty (lift s) e
```

NOTES

[1]: Occasionally, we can work in a setting where we don't need to worry about one or tw of these issues. For example, if we only need to model a small-step operational semantics for closed terms, we don't need to worry about variable capture during substitution and can ignore (2). Alternatively, if we use a locally-nameless representation, we never substitute into terms with free variables, so we can ignore (3).

[2]: We could also use generic programming to automatically derive the definition of `subst`, using techniques such as in the `Unbound` library.*
