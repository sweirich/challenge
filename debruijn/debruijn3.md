# The Polymorphic lambda calculus

Now that we know how to implement substitution generically, we can use it *twice* in our implementation of System F --- once for types and once for terms. Let's do it first with simply-typed substitutions. In the next part we will add type indices to make everything strongly typed.

```
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
