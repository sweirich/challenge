# The Polymorphic lambda calculus

*Reference files:* [Poly](src/Poly.hs) and [Subst](src/Subst.hs)

Now that we know how to implement substitution generically, we can use it *twice* in our implementation of System F --- once for types and once for terms. Let's do it first with simply-typed substitutions. In the next part we will add type indices to make everything strongly typed.

```haskell
data Ty = IntTy | Ty :-> Ty | VarTy Idx | PolyTy Ty
    deriving (Eq, Show)

data Exp :: Type where
 IntE   :: Int
        -> Exp
 VarE   :: Idx
        -> Exp
 LamE   :: Ty       -- type of binder
        -> Exp      -- body of abstraction
        -> Exp
 AppE   :: Exp      -- function
        -> Exp      -- argument
        -> Exp
 TyLam  :: Exp      -- bind a type variable
        -> Exp
 TyApp  :: Exp      -- type function
        -> Ty       -- type argument
        -> Exp
```

We actually need three forms of substitution for this language: types-in-types, types-in-terms, and terms-in-terms.

The first two are generally straightforward and follow directly from the pattern shown in Part I. In particular, they traverse the argument, use `applyS` for variables, and `lift` when going under a binder.

## Types-in-types

```haskell
instance SubstC Ty where
    var = VarTy

    subst s IntTy       = IntTy
    subst s (t1 :-> t2) = subst s t1 :-> subst s t2
    subst s (VarTy x)   = applyS s x
    subst s (PolyTy t)  = PolyTy (subst (lift s) t)
```

## Types-in-terms

```haskell
substTy :: Sub Ty -> Exp -> Exp
substTy s (IntE x)     = IntE x
substTy s (VarE n)     = VarE n
substTy s (LamE t e)   = LamE (subst s t) (substTy s e)
substTy s (AppE e1 e2) = AppE (substTy s e1) (substTy s e2)
substTy s (TyLam e)    = TyLam (substTy (lift s) e)
substTy s (TyApp e t)  = TyApp (substTy s e) (subst s t)
```

## Terms-in-terms

The only part that requires thought is the `TyLam` case of term-in-term substitution.

```haskell
instance SubstC Exp where
   var = VarE

   subst s (IntE x)     = IntE x
   subst s (VarE x)     = applyS s x
   subst s (LamE ty e)  = LamE ty (subst (lift s) e)
   subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)
   subst s (TyLam e)    = TyLam (subst (fmap (substTy incSub) s) e)  
   subst s (TyApp e ty) = TyApp (subst s e) ty
 ```  

In this case, we are going under a binder, but it is a type-variable binder, not a term-variable binder. Because of that difference, we need to shift the type variables in the range of the term substitution, but we don't need to do anything else. Conveniently, substitutions are functors, so we can use `fmap`.
