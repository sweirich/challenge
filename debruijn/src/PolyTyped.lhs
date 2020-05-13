> {-# LANGUAGE TemplateHaskell #-}
> module PolyTyped where

> import Imports
> -- Note: bug in singletons. Cannot qualify this module import.
> import Subst
> import SubstProperties
> import qualified SubstTyped as T

> $(singletons [d|
>     data Ty = IntTy | Ty :-> Ty | VarTy Idx | PolyTy Ty
>     
>     instance SubstC Ty where
>       var = VarTy
>       subst s IntTy       = IntTy
>       subst s (t1 :-> t2) = subst s t1 :-> subst s t2
>       subst s (VarTy x)   = applyS s x
>       subst s (PolyTy t)  = PolyTy (subst (lift s) t)
>  |])


> data Exp :: [Ty] -> Ty -> Type where
> 
>   IntE   :: Int
>          -> Exp g IntTy
> 
>   VarE   :: T.Idx g t
>          -> Exp g t
> 
>   LamE   :: Sing t1               -- type of binder
>          -> Exp (t1:g) t2         -- body of abstraction
>          -> Exp g (t1 :-> t2)
> 
>   AppE   :: Exp g (t1 :-> t2)     -- function
>          -> Exp g t1              -- argument
>          -> Exp g t2
> 
>   TyLam  :: Exp (IncList g) t     -- bind a type variable
>          -> Exp g (PolyTy t)
> 
>   TyApp  :: Exp g (PolyTy t1)     -- type function
>          -> Sing t2               -- type argument
>          -> Exp g (Subst (SingleSub t2) t1)

* Substitution

> instance T.SubstC Exp where
>    var = VarE
> 
>    subst s (IntE x)     = IntE x
>    subst s (VarE x)     = T.applyS s x
>    subst s (LamE ty e)  = LamE ty (T.subst (T.lift s) e)
>    subst s (AppE e1 e2) = AppE (T.subst s e1) (T.subst s e2)
>    subst s (TyLam e)    = TyLam (T.subst (substTy_Sub SInc s) e)
>    subst s (TyApp e t)  = TyApp (T.subst s e) t


Apply a type substitution in a term
 
> substTy :: forall g s ty.
>    Sing (s :: Sub Ty) -> Exp g ty -> Exp (SubstList s g) (Subst s ty)
> substTy s (IntE x)     = IntE x
> substTy s (VarE n)     = VarE $ substTy_Idx s n
> substTy s (LamE t e)   = LamE (sSubst s t) (substTy s e)
> substTy s (AppE e1 e2) = AppE (substTy s e1) (substTy s e2)
> substTy s (TyLam (e :: Exp (SubstList Inc g) t))    
>     | Refl <- axiom1 @g s = TyLam (substTy (sLift s) e)
> substTy s (TyApp (e :: Exp g (PolyTy t1)) (t :: Sing t2))  
>     | Refl <- axiom2 @t1 @t2 s
>                        = TyApp (substTy s e) (sSubst s t)
 
Apply a type substitution in an index

> -- | Sing s is a proxy
> substTy_Idx :: Sing s -> T.Idx g t -> T.Idx (SubstList s g) (Subst s t)
> substTy_Idx s T.Z     = T.Z
> substTy_Idx s (T.S n) = T.S (substTy_Idx s n)

Apply a type substitution in a term substitution

> substTy_Sub :: Sing s -> T.Sub Exp g g' -> T.Sub Exp (SubstList s g) (SubstList s g')
> substTy_Sub s T.IdS         = T.IdS
> substTy_Sub s T.Inc         = T.Inc
> substTy_Sub s (e T.:· s1)   = substTy s e T.:· substTy_Sub s s1
> substTy_Sub s (s1 T.:<> s2) = substTy_Sub s s1 T.:<> substTy_Sub s s2
