# Part II: Type-indexed term representation for STLC

*Reference files [SubstTyped](src/SubstTyped.hs) and [SimpleTyped](src/SimpleTyped.hs).*

## Type-indexed substitutions

The AST for expressions that we developed in the last part is not type-indexed. It can represent nonsensical STLC terms. In this section we'll add type parameters to the datatype definition so that it can only represent well typed terms.

We will also add type parameters to the substitution operation (and reified substitutions) to make sure that as we work with well-typed terms, substitutions stay well-typed.

Note that we won't change the actual code in either the Subst or Simple modules. The implementation of substitution will be exactly the same as before. All of the action will be in the types.

In other words, our goal will be to fill in the `???` in the types below to make the types more informative in the [Subst](src/Subst.hs) module (which gives us a general purpose infrastructure for substitution):

```haskell
-- What context are we indexing into? What do we find?
data Idx ??? where
  Z :: Idx ???
  S :: Idx ??? -> Idx ???

-- How does substitution change the context?
data Sub a ??? where
   Inc   :: ??? -> Sub a ???
   (:<)  :: a ??? -> Sub a ??? -> Sub a ???
   (:<>) :: Sub a ??? -> Sub a ??? -> Sub a ???

-- What type of term do we get when we look up an `Idx` in the substitution? 
applySub :: SubstDB a => Sub a ??? -> Idx ??? -> a ???
applySub (Inc n)       x  = var (add n x)
applySub (ty :< s)     Z  = ty
applySub (ty :< s)  (S x) = applySub s x
applySub (s1 :<> s2)   x  = subst s2 (applySub s1 x)

class SubstDB a where
   var   :: Idx ??? -> a ???
   subst :: Sub a ??? -> a ??? -> ???

-- How does lift modify the substitution?
lift :: SubstDB a => Sub a ??? -> Sub a ???
lift s = var Z :< (s :<> Inc 1)
```

And to continue with our madlibs in the [Simple](src/Simple.hs) module, constraining the implementation to be for the simply typed lambda calculus.

```haskell
data Exp ??? where

 IntE   :: Int -> Exp ???  -- literal int

 VarE   :: Idx ???         -- variable index
        -> Exp ???

 LamE   :: ???             -- type of binder
        -> Exp ???         -- body of abstraction
        -> Exp ???

 AppE   :: Exp ???         -- function
        -> Exp ???         -- argument
        -> Exp ???

-- Same definition as in `Simple`
instance SubstDB Exp where
   var = VarE

   subst s (IntE x)     = IntE x
   subst s (VarE x)     = applySub s x
   subst s (LamE ty e)  = LamE ty (subst (lift s) e)
   subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)
```

## Strongly-typed AST

In the case of STlC, recall the only two forms of types, base types and function types.

```haskell
data Ty = IntTy | Ty :-> Ty
    deriving (Eq,Show)
```

The `Exp` GADT below has two type parameters: 

1. The first (of kind `[Ty]`) is a typing context that provides the types of the free variables in the expression.

   With de Bruijn indices, this context can be represented using a *type-level* list of types where the *i-th* type in the list is the type of the *i-th* free variable.

2. The second (of kind `Ty`) is the type of the entire expression.

In both cases, we are using *datatype promotion*, i.e. the `DataKinds` GHC extension, to use data constructors (like `IntTy`, `:->` and `:`) in the arguments of datatypes.

```haskell
data Exp :: [Ty] -> Ty -> Type where

 IntE   :: Int -> Exp g IntTy
 -- ^ literal ints, valid in any context

 VarE   :: Idx g t
        -> Exp g t
 -- ^ variables, represented by an index into
 -- the context (see below)

 AppE   :: Exp g (t1 :-> t2)
        -> Exp g t1
        -> Exp g t2
 -- ^ application expressions. Requires a function
 -- and an argument of the appropriate type.

 LamE   :: STy t1
        -> Exp (t1:g) t2
        -> Exp g (t1 :-> t2)
 -- ^ abstractions (lambda). Includes a runtime
 -- representation of the type of the binder
 -- and a body that type checks in an extended
 -- context.
```

For lambda expressions, we need to connect the runtime type parameter

### Typed indices

In the last part, we just used natural numbers as our de Bruijn indices. We will do the same here, except that we can give this version of the natural numbers a type that explicitly indicates that they are an index into a (generic) list.

```haskell
data Idx (g::[a]) (t::a) :: Type where
  Z :: Idx (t:g) t
  S :: Idx g t -> Idx (u:g) t
```

Examples:

- A closed expression: `\ x -> x`

    ```haskell
    LamE IntTy (VarE Z) :: Exp '[] (IntTy :-> IntTy)
    ```

- An expression with a single free variable: `\x -> y x`

    ```haskell
    LamE IntTy (AppE (VarE (S Z) Z)) :: Exp '[IntTy :-> b] (IntTy :-> b)
    ```

### Typed substitutions

A typed AST requires a substitution operation that shows that substitution is type preserving, i.e. if an expression has type `t`, then after a substitution has been applied should still have type `t`.  

However, because we are working with open terms, substitution is not only type preserving, but context *transforming*: the initial context used for the expression may not be the same one after the substitution. For example, if we have an expression with one free variable and we replace that variable with a literal integer, the result should be a closed expression.

In other words, the substitution operation should have type, where the context transformation is given by the type indices of the substitution itself.

```haskell
subst :: Sub Exp g g' -> Exp g t -> Exp g' t
```

To make this work, we need to describe the types of the various substitution constructors from the prior section.  

```haskell
data Sub (a :: ([k] -> k -> Type)) (g :: [k]) (g'::[k]) where
   Inc   :: IncBy g1 -> Sub a g (g1 ++ g)
   (:<)  :: a g' t -> Sub a g g' -> Sub a (t:g) g'
   (:<>) :: Sub a g1 g2 -> Sub a g2 g3 -> Sub a g1 g3
```

Before, we just used natural number as the argument of the increment substitution. We would still like to do that, but we need its type to tell us what to add to the context when we increment.

```haskell
data IncBy (g :: [k]) where
   IZ :: IncBy '[]
   IS :: IncBy n -> IncBy (t:n)
```

If we increment by 0, i.e. using `IZ` then our type normalizes to the expected type of the identity substitution. This substitution leaves the context alone. (Haskell can figure out this type for us, but we add it to the source file because that is good style.)

```haskell
-- nil :: Sub a g g
nil = Inc IZ
```

Similarly, the `lift` and `singleSub` operations have inferrable types. The only change is the adoption of the `IncBy` datatype. (NOTE: if we were in Agda, we could overload the data constructors for `Z` and `S`, but then would not be able to infer the type automatically.)

```haskell
--singleSub :: a g t -> Sub a (t:g) g
singleSub t = t :< Inc IZ
```

```haskell
--lift :: SubstDB a => Sub a g g' -> Sub a (t:g) (t:g')
lift s = var Z :< (s :<> Inc (IS IZ))
```

Finally, when we apply the increment substitution to an index, in the `applyS` function, we need a new type for our natural number addition function. This type reflects the fact that we have shifted the index into the context.

```haskell
add :: IncBy g1 -> Idx g t -> Idx (g1 ++ g) t
add IZ i = i
add (IS xs) i = S (add xs i)
```

That is it! We didn't really need to change any code. We only need to add (a lot of) types.

*ADDITIONAL NOTES:*

1. This definition of index is perfect for safely accessing a heterogeneous list: *i.e.* a list where each element may have a different type.

    ```haskell
    data HList (g :: [k]) where
      HNil  :: HList '[]
      HCons :: t -> HList g -> HList (t:g)

    indx :: HList g -> Idx g t -> t
    indx g Z = case g of
       (HCons x xs) -> x
    indx g (S n) = case g of
       (HCons x xs) -> indx xs n
    ```
  
    Note that we index into this heterogeneous list, we never need to include a case for `HNil`.   The   type indices guarantee that the index will be found in the list (and has the appropriate   type).

2. In this example we could skip the definition of the `Ty` datatype by using Haskell types to represent STLC types. But we will need this data structure when we go to System F, so we introduce it here.

3. Our (parallel) substitution operation subsumes all of the context manipulation operations that we expect from the lambda calculus, including substituting for a free variable, weakening (i.e. introducing a new variable into the context somewhere), and exchange.

   For example, weakening is just the increment-by-one substitution.

   ```haskell
   incSub :: forall t a g. Sub a g (t:g)
   incSub = Inc (IS IZ)
   ```

   And exchange swaps the variables at positions 0 and 1.

   ```haskell
   exchange:: forall t1 t2 a g. Sub a (t1:t2:g) (t2:t1:g)
   exchange = var (S Z) :< var Z :< Inc (IS (IS IZ))
   ```
