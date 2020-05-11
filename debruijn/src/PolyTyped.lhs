> {-# LANGUAGE TemplateHaskell #-}
> module PolyTyped where

> import Imports
> import Nat
> -- Note: bug in singletons. Cannot qualify this module import.
> import Subst 
> import qualified SubstTyped as ST

> $(singletons [d|
>     data Ty = IntTy | Ty :-> Ty | VarTy Nat | PolyTy Ty
>     
>     instance SubstC Ty where
>       var = VarTy
>       subst s IntTy       = IntTy
>       subst s (t1 :-> t2) = subst s t1 :-> subst s t2
>       subst s (VarTy x)   = applyS s x
>       subst s (PolyTy t)  = PolyTy (subst (lift s) t)
>  |])

> {-
> instance PSubstC Ty where
>  type instance Var n = VarTy n
>  type instance Subst s IntTy       = IntTy
>  type instance Subst s (t1 :-> t2) = (Subst s t1) :-> (Subst s t2)
>  type instance Subst s (VarTy n)   = ApplyS s n
>  type instance Subst s (PolyTy t)  = PolyTy (Subst (Lift s) t)

> instance SSubstC Ty where
>     sVar = SVarTy
>     sSubst s SIntTy = SIntTy
>     sSubst s (t1 :%-> t2) = sSubst s t1 :%-> sSubst s t2
>     sSubst s (SVarTy n) = sApplyS s n
>     sSubst s (SPolyTy t) = SPolyTy (sSubst (sLift s) t) 
> -}


> data Exp :: [Ty] -> Ty -> Type where
>  IntE   :: Int -> Exp g IntTy
>  VarE   :: ST.Var g t
>         -> Exp g t
>  LamE   :: Sing t1       -- type of binder
>         -> Exp (t1:g) t2     -- body of abstraction
>         -> Exp g (t1 :-> t2)         
>  AppE   :: Exp g (t1 :-> t2)     -- function
>         -> Exp g t1     -- argument
>         -> Exp g t2
>  TyLam  :: Exp (IncList g) t     -- bind a type variable
>         -> Exp g (PolyTy t)
>  TyApp  :: Exp g (PolyTy t1)     -- type function
>         -> Sing t2       -- type argument
>         -> Exp g (Subst (SingleSub t2) t1)


> -- Note: this is an instance of a natural transformation with
> -- f = substTy SInc
> incTy_Sub :: ST.Sub Exp g g' -> ST.Sub Exp (IncList g) (IncList g')
> incTy_Sub ST.IdS        = ST.IdS
> incTy_Sub ST.Inc        = ST.Inc
> incTy_Sub (e ST.:· s)   = substTy SInc e ST.:· incTy_Sub s
> incTy_Sub (s1 ST.:∘ s2) = incTy_Sub s1 ST.:∘ incTy_Sub s2

> instance ST.SubstC Exp where
>    var = VarE
> 
>    subst s (IntE x)     = (IntE x)
>    subst s (VarE x)     = ST.applyS s x
>    subst s (LamE ty e)  = LamE ty (ST.subst (ST.lift s) e)
>    subst s (AppE e1 e2) = AppE (ST.subst s e1) (ST.subst s e2)
>    subst s (TyLam e)    = TyLam (ST.subst (incTy_Sub s) e)
>    subst s (TyApp e t)  = TyApp (ST.subst s e) t

> -- | apply a type substitution in a term
> 
> substTy :: forall g s ty.
>    Sing (s :: Sub Ty) -> Exp g ty -> Exp (SubstList s g) (Subst s ty)
> substTy s (IntE x)     = IntE x
> substTy s (VarE n)     = VarE $ substTy_Var s n
> substTy s (LamE t e)   = LamE (sSubst s t) (substTy s e)
> substTy s (AppE e1 e2) = AppE (substTy s e1) (substTy s e2)
> substTy s (TyLam (e :: Exp (SubstList Inc g) t))    
>     | Refl <- lemma1 @g s = TyLam (substTy (sLift s) e)
> substTy s (TyApp (e :: Exp g (PolyTy t1)) (t :: Sing t2))  
>     | Refl <- lemma2 @t1 @t2 s
>                        = TyApp (substTy s e) (sSubst s t)
> 

> -- | Sing s is a proxy
> substTy_Var :: Sing s -> ST.Var g t -> ST.Var (SubstList s g) (Subst s t)
> substTy_Var = undefined

> lemma1 :: forall g s. Sing s ->
>            LiftList s (IncList g) :~: IncList (SubstList s g)
> lemma1 s = undefined


> lemma2 :: forall t1 t2 s . Sing s ->
>              Subst (SingleSub (Subst s t2)) (Subst (Lift s) t1)
>          :~: Subst s (Subst (SingleSub t2) t1)
> lemma2 s = undefined
