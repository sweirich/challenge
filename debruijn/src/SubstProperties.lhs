> module SubstProperties where

> import Imports
> import Nat
> import Subst

> import Test.QuickCheck

> -- cannot test without some instance
> import Simple
>
> 
> prop1 :: Sub Exp -> [Exp] -> Bool
> prop1 s g = liftList s (incList g) == incList (substList s g)

> axiom1 :: forall g s. Sing s ->
>            LiftList s (IncList g) :~: IncList (SubstList s g)
> axiom1 s = undefined

> lemma1 :: forall g s. Sing s -> Sing g ->
>            LiftList s (IncList g) :~: IncList (SubstList s g)
> lemma1 s SNil = Refl
> lemma1 s (SCons x xs)
>    | Refl <- lemma1 s xs = Refl


> aux1 :: forall s x. Sing x -> Subst (Lift s) (Subst Inc x) :~: Subst Inc (Subst s x)
> aux1 = undefined

> axiom2 :: forall t1 t2 s . Sing s ->
>              Subst (SingleSub (Subst s t2)) (Subst (Lift s) t1)
>          :~: Subst s (Subst (SingleSub t2) t1)
> axiom2 s = undefined

> instance Arbitrary Nat where
>   arbitrary = oneof [ return Z, S <$> arbitrary ]
>   shrink n = if n == 0 then [] else [n - 1]


> instance Arbitrary Ty where
>   arbitrary = sized gt where
>    base = return IntTy
>    gt m = 
>      if m <= 1 then base else
>      let m' = m `div` 2 in
>      frequency
>      [(1, base),
>       (1, (:->)    <$> gt m' <*> gt m')]
>
>   shrink IntTy = []
>   shrink (t1 :-> t2) = t1 : t2 : [ t1' :-> t2 | t1' <- shrink t1]
>                       ++ [ t1 :-> t2' | t2' <- shrink t2]


> instance Arbitrary Exp where
>   arbitrary = sized gt where
>    base = oneof [IntE <$> arbitrary, VarE <$> arbitrary]
>    gt m =
>      if m <= 1 then base else
>      let m' = m `div` 2 in
>      frequency
>      [(1, base),
>       (1, LamE    <$> arbitrary <*> gt m'), 
>       (1, AppE    <$> gt m'     <*> gt m')]
>
>   shrink (IntE x) = []
>   shrink (VarE n) = [VarE n' | n' <- shrink n ]
>   shrink (LamE t s)   = s : [ LamE t' s  | t' <- shrink t] ++
>                             [ LamE t  s' | s' <- shrink s]
>   shrink (AppE s1 s2) = s1 : s2 :
>     [AppE s1' s2  | s1' <- shrink s1] ++
>     [AppE s1  s2' | s2' <- shrink s2]                       
     


> instance Arbitrary a => Arbitrary (Sub a) where
>  arbitrary = sized gt where
>    base = elements [IdS, Inc]
>    gt m =
>      if m <= 1 then base else
>      let m' = m `div` 2 in
>      frequency
>      [(1, base),
>       (1, (:·)    <$> arbitrary <*> gt m'), 
>       (1, (:∘)    <$> gt m'     <*> gt m')]
>
>  shrink IdS = []
>  shrink Inc = [IdS]
>  shrink (t :· s)   = s : [t' :· s' | t' <- shrink t, s' <- shrink s]
>  shrink (s1 :∘ s2) = s1 : s2 :
>    [s1' :∘ s2 | s1' <- shrink s1, s2' <- shrink s2]                       
