# Strong types for System F, at last

*Reference files:* [PolyTyped](src/PolyTyped.hs) and [SubstProperties](src/SubstProperties.hs)

Finally, we put *everything* together to develop a strongly-typed AST for System F! 

As in [Poly](src/Poly.hs), we use de Bruijn indices for both term and type variables.  However, this time, in [PolyTyped](src/PolyTyped.hs) we use *weakly-typed* indices for binding at the type level (as defined in [Subst](src/Subst.hs)) and *strongly-typed* indices for binding at the term level (as defined in [SubstTyped](src/SubstTyped.hs)). 

To distinguish these parallel definitions, we qualify the imports in what follows below.

```haskell
import qualified Subst as U         -- for type-level substitution
import qualified SubstTyped as T    -- for term-level substitution
```

So, for this version, we start with the expression datatype that we saw in [Part II](debruijn2.md), but we make two changes.

```haskell
data Exp :: [Ty] -> Ty -> Type where

  IntE   :: Int  -> Exp g IntTy   -- literal integer values

  VarE   :: T.Idx g t -> Exp g t  -- Idx type from SubstTyped

  LamE   :: Π (t1 :: Ty)          -- type of binder
         -> Exp (t1:g) t2         -- body of abstraction
         -> Exp g (t1 :-> t2)

  AppE   :: Exp g (t1 :-> t2)     -- function
         -> Exp g t1              -- argument
         -> Exp g t2
```

**First**, we index this datatype using the System F types that we saw in [Part III](debruijn3.md).

```haskell
data Ty = IntTy | Ty :-> Ty | VarTy U.Idx | PolyTy Ty
```

and **second**, we extend `Exp` with the data constructors for type abstraction `TyLam` and type application `TyApp` as in [Part III](debruijn3.md) (see below).

This part is where we are really "dependently-typed" programming, and you might expect a little [Hasochism](https://dl.acm.org/doi/10.1145/2503778.2503786) to come into play reflecting the differences between Haskell and real dependently-typed languages like Agda or Idris. It does, but maybe not in the way that you might expect.

The good news is that the singletons library means that we don't have to worry about code duplication (i.e. we don't need to write our operations multiple times). The singletons library generates the additional definitions for us. There is still some friction, though, because we do have multiple versions of the "same" definition, so there are a few places
where the code looks a bit strange. 

The more serious issue is that Haskell is not a proof assistant. There will be a few places where type checking requires a proof obligation about a functional program that we cannot satisfy. There isn't really a good solution to this problem, but we will discuss the trade-offs of various alternatives.

## Singleton types and promoted definitions

This example makes heavy use of the [singletons](https://hackage.haskell.org/package/singletons) library. If you go back to the [Subst](src/Subst.hs) and [Poly](src/Poly.hs) modules, you'll see that some definitions are surrounded by Template Haskell brackets. These definitions are processed by the singletons library to generate additional definitions that we can use for dependently-typed programming.

For example, the singletons library automatically derives the "singleton" analogue of the `Ty` datatype, called `STy`. This means that in addition to the `Ty` datatype defined in [Poly](src/Poly.hs)  (and shown above) the library also *generates* the following datatype declaration for us (i.e. we don't have to write it).

```haskell
data STy :: Ty -> Type where
    SIntTy  :: STy IntTy
    (:%->)  :: STy a  -> STy b -> STy (a :-> b)
    SVarTy  :: U.SIdx i -> STy (VarTy i)
    SPolyTy :: STy a  -> STy (PolyTy a)
```

The `STy` type is isomorphic to `Ty`; it includes all the same data constructors, now starting with `S` (or mangled to include a `%`) that each take analogous arguments.  However, each data constructor determines the form of the parameter to `STy`. For example, if we have a value of type

```haskell
x = SIntTy :%-> SIntTY
```
then it *must* have type 

```haskell
x :: STy (IntTy :-> IntTy)
```

The `STy` type allows us to "fake" dependent types. For example, the `LamE` constructor can include a type annotation for the bound variable. This type annotation is present as part of the data structure, but also can be used in the result type of the constructor.

```haskell
LamE :: STy t1 -> Exp g t2 -> Exp g (t1 :-> t2)
```

For convenience, the singletons library defines a type family, called `Sing`, that gathers together all singleton types (like `STy` above) using the same name. That means, we can also write the type of `LamE` using `Sing` and let GHC figure out that we mean the singleton type for `Ty`.

```haskell
LamE :: Sing t1 -> Exp g t2 -> Exp g (t1 :-> t2)
```

Furthermore, if we want to pretend that we are doing dependently-typed programming, we can also define the following type abbreviation.

```haskell
type Π = Sing
```
This abbreviation lets us write the type of `LamE` using a "Π" quantifier.

```haskell
LamE :: Π (t1 :: Ty) -> Exp g t2 -> Exp g (t1 :-> t2)
```

Furthermore, the singletons library generates type-level analogues for the other functions in the file, as well as the `SubstDB` type class and its members, using type families. These analogues let us use the (overloaded) functions in types; we will need them in the types of `TyLam` and `TyApp`, the new data constructors that we will add to `Exp`.

However, there are two main differences between normal expression-level functions and those promoted to type-families by singletons:

  1. Type families must start with a capital letter. So in types, the promoted function `subst` must be referred to as the type family `Subst`.
  2. Type families cannot be partially applied. So if we would like to talk about some partial application such as `subst s`, we need to either give it a new promoted name, or use the *defunctionalization* symbols generated by singletons, and write `SubstSym1 s` instead.

## Functional programming in types

As we saw in [Poly](src/Poly.hs), System F includes two new expression forms: type abstraction (which introduces a new polymorphic type) and type application (which instantiates a term with a polymorphic type).  To represent these expression forms, we add the following new data constructors to the expression type.

### TyLam

```haskell
TyLam  :: Exp (IncList g) t     -- bind a type variable
         -> Exp g (PolyTy t)
```


When we create a new type abstraction with `TyLam`, we bind a new type variable in its argument (the body of the type abstraction). As a result, all of the type variables that appear in the context of this term need to be incremented. We express this behavior that by promoting the following function to be available at the type level (with the name `IncList`).

```haskell
$(singletons [d|
    -- increment all terms in a list 
    incList :: SubstDB a => [a] -> [a]
    incList = map (subst incSub)
  |])
```    

For example, we can represent the polymorphic identity function `/\a. \x -> x`, of type `forall a. a -> a`, with this term. Note that the term is closed so the context `g` is the empty list `'[]`.

```haskell
polyId :: Exp '[] (PolyTy (VarTy U.Z :-> VarTy U.Z))
polyId = TyLam (LamE (SVarTy U.SZ) (VarE T.Z))
``` 
In the definition of this term we first introduce the type variable "a" with `TyLam`. Then the type of the argument to the term abstraction `LamE`, is "a", which we write as `SVarTy U.SZ` the singleton analogue of `VarTy U.Z`. (Recall that type variable indices, such as `U.Z`, comes from the weakly-typed substitution library [Subst](src/Subst.hs).)  Finally, the body of the term abstraction is a term variable, with index `T.Z` (using the definition from the strongly-typed substitution library [SubstTyped](src/SubstTyped.hs)).

### TyApp

The data constructor for type application uses the promoted substitution operations from the library [Subst](src/Subst.hs).

```haskell
TyApp  :: Exp g (PolyTy t1)     -- type function
         -> Π (t2 :: Ty)        -- type argument
         -> Exp g (U.Subst (U.SingleSub t2) t1)
```

In a type instantiation, the first argument of `TyApp` must have a polymorphic type. The second argument, a runtime version of a `Ty`, is the type that we need to use for instantiation. We then instantiate the body `t1` with the type `t2` by applying the substitution function with the single substitution for type variable `U.Z`. 

For example, we can instantiate the polymorphic function `polyId` above at type `IntTy`. 

```haskell
-- intId :: Exp '[] (IntTy :-> IntTy)    -- can be inferred 
intId = TyApp polyId SIntTy
```

GHC can figure out that the System F expression has type `IntTy :-> IntTy`, even if we do not include this type annotation, by simplification. The type of `TyApp` above means that the type expression must be

```haskell
U.Subst (U.SingleSub IntTy) (VarTy U.Z :-> VarTy U.Z)
```

which reduces (at type-checking time) to

```haskell
IntTy :-> IntTy
```

## Term and Type substitutions

In addition to `Exp`, we also must define how term substitution (`subst`) and type substitution (`substTy`) for this AST.

As in [Part II](debruijn2.md), the definition of term substitution in terms uses the definitions from the strongly-typed substitution framework [SubstTyped](src/SubstTyped.hs). This means that the substitution function from the `SubstDB` type class has an expressive type, describing how the environment changes during term substitution. 

```haskell
subst :: T.Sub Exp g g' -> Exp g t -> Exp g' t
```
As before, the definition uses the same code as in the weakly typed version, shown in [Poly](src/Poly.hs). We can reuse the same instance declaration wholesale!  

However, the auxiliary functions that this instance declaration *depends on* differ between the weakly- and strongly- typed versions. In 
particular, in the case of substitution into `TyLam`, we are pushing 
a term substitution into the body of a type abstraction. That means that any free type variables that appear in the expressions in the range of that substitution must be incremented so that they are not captured by this new type binder. The auxiliary function that computes this incremented substitution uses the `substTy` function to apply a type substitution to an expression.

In [Poly](src/Poly.hs), the weakly-typed version of the function has this type.

```haskell
substTy :: Sub Ty -> Exp -> Exp
```

Here, in [PolyTyped](src/PolyTyped.hs), the type of the
analogous function shows that when we substitute for type variables in a term, we also change its System F typing derivation. In other words, the type of this operation is the following.

```haskell
substTy :: forall g s ty.
   Π (s :: U.Sub Ty) -> Exp g t -> Exp (Map (U.SubstSym1 s) g) (U.Subst s t)
```

For example, if the type of an expression, `t` has a free type variable, 

```haskell
t :: Exp [VarTy U.Z] (VarTy U.Z :-> VarTy U.Z)
t = LamE (SVarTy U.SZ) (VarE (T.S T.Z))
```
and we use `substTy` to replace that type variable with `IntTy`, then result of 
`substTy` will be an expression of type `Exp [IntTy] (IntTy :-> IntTy)`. That means that the type of `substTy` needs apply its argument type substitution `s` to both the context and the result type. For the latter, we use use `U.Subst`. However, 
for the former, we need to map this substitution across the context `g`, using the singleton library's `SubstSym1` trick.  In this case, `SubstSym1 s` is equivalent to `Subst s`, but can be given as an argument to the higher-order function `Map`.

## A challenge for the GHC type checker

The first four cases of the definition of `substTy` are the same as in [Part II](debruijn2.md). However, the last two cases, for `TyLam` and `TyApp` are particularly challenging to define. Let's just look at the case for `TyLam`. 

In [Poly](src/Poly.hs), the equivalent definition reads
```haskell
substTy s (TyLam e)    = TyLam (substTy (lift s) e)
```
The type substitution `s` must be `lift`ed because we are going into the body of a type binding.

In [PolyTyped](src/PolyTyped.hs), the strongly-typed version, we would like to just write:

```haskell
substTy s (TyLam e) = TyLam (substTy (U.sLift s) e)
```
Here, we use `U.sLift` which is the singleton analogue of the `lift` definition, necessary because `s` has a singleton type.

However, this code does not type check!

And if we try to type check it, we get a particularly cryptic type error message. (Do not try to understand this error message.)

```
src/PolyTyped.hs:84:15-35: error: …
    • Could not deduce: Map
                          (U.SubstSym1 ('VarTy 'U.Z 'U.:< (s 'U.:<> 'U.Inc ('U.S 'U.Z))))
                          (Map (U.SubstSym1 ('U.Inc ('U.S 'U.Z))) g)
                        ~ Map (U.SubstSym1 ('U.Inc ('U.S 'U.Z))) (Map (U.SubstSym1 s) g)
      from the context: ty ~ 'PolyTy t
```
The problem in this case, is that we have a proof obligation. We need to know how "lifting" and "incrementing" a context commute. 
The expression `e` above has type `Exp (IncList g) t`, so the recursive call `substTy (U.sLift s) e` produces a result of type 
```
Exp (Map (U.Subst (U.Lift s)) (IncList g)) (U.Subst (U.Lift s) t)
```
However, to apply the `TyLam` constructor to this result, it needs to be of the form `Exp (IncList g1)` for some `g1`.

So therefore, we need to know that we can commute these two passes over the list. In otherwords, we need to know that for any `s` and any `g`, the following type equality holds.

```haskell
Map (Subst (Lift s)) (IncList g) ~ IncList (Map (Subst s) g)
```
(This is what the error message above says, but it has expanded the definitions of `Lift` and `IncList`, and uses `SubstSym1` for the partial application of `Subst`.)

This result is a property of how substitution works, and not something that should be obvious to GHC. If we were in a dependently-typed language, we would have to prove this equality as a theorem.

However, in GHC, we do not have a way to express this proof, so what can we do?

## Convincing GHC about a property about substitution

There is no perfect solution to this problem. 

1. Check the property at runtime. 

It is possible to write a function that checks to make sure that the property above holds for the appropriate list, when we need to use the equality. This replaces a general proof with a test case for every instance that we might need to do this reasoning.  
However, not only is this inefficient in terms of time (every time we substitute, we need to check the property) but it is also difficult to add to our code. We *don't* have a runtime version of the typing context around in the expression --- this data structure is only used at compile-time. Furthermore it would take a significant refactoring to make this context available, in addition to the runtime cost of propagating it through computation.

2. Add an axiom that tells GHC to assume this property holds. 

This approach is dangerous, but can be justified. By dangerous, we mean that if we get this axiom wrong, we can introduce a hole into the GHC type system. In otherwords, we could cause a well-typed Haskell program to crash!

That sounds scary, but that is actually the approach taken in the implementation in [PolyTyped](src/PolyTyped.hs). The justification for this axiom is twofold. First, it is derived from properties that follow from a somewhat similar implementation in Coq. Second, we can also use tools like quickcheck to increase our confidence in the property itself. Although quickcheck cannot produce a proof, it can test a property like the one above with many, many examples. And properties involving lists are often easy to test.

3. Extend the GHC type checker

This approach is really an enhanced version of the one above. If we are *very* confident in the correctness of properties like the one above, we can allow experts to develop a type-checker plug-in that captures this sort of reasoning. This version isn't any more safe than the previous (a GHC plug-in is simply a way to tell the typechecker about a LOT of axioms) but it does establish the boundaries of what may and may not be assumed.


