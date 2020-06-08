> {-# LANGUAGE TemplateHaskell #-}
> module SubstProperties(axiom1, axiom2) where

> import Imports
> import Subst

> import Test.QuickCheck
>
> import Unsafe.Coerce

A simple instance of the SubstC type class for use to test the properties.

> $(singletons [d|
>    data Exp :: Type where
>      VarE   :: Idx  -> Exp 
>      LamE   :: Exp  -> Exp          
>        deriving (Eq, Show)
>    instance SubstC Exp where
>      var = VarE
>      subst s (VarE x)  = applySub s x
>      subst s (LamE e)  = LamE (subst (lift s) e)
> 
>    |])


* Property 1

> prop1 :: Sub Exp -> [Exp] -> Bool
> prop1 s g = liftList s (incList g) == incList (substList s g)

> axiom1 :: forall g s. Sing s ->
>            LiftList s (IncList g) :~: IncList (SubstList s g)
> axiom1 s = unsafeCoerce Refl

> lemma1 :: forall (g :: [Exp]) s. Sing s -> Sing g ->
>            LiftList s (IncList g) :~: IncList (SubstList s g)
> lemma1 s SNil = Refl
> lemma1 s (SCons x xs)
>    | Refl <- lemma1 s xs,
>      Refl <- aux1 s x = Refl


> aux1 :: forall s x. Sing s -> Sing (x::Exp) -> Subst (Lift s) (Subst Inc x) :~: Subst Inc (Subst s x)
> aux1 s (SVarE n) = Refl
> aux1 s (SLamE e)
>  | Refl <- aux1 (sLift s) e
>  = undefined

* Property 2

This property is an analogue about exchanging two substitutions.

> prop2 :: Sub Exp -> Exp -> Exp -> Bool
> prop2 s t2 x = subst s (subst (singleSub t2) x) == 
>      subst (singleSub (subst s t2)) (subst (lift s) x)

> axiom2 :: forall t1 t2 s . Sing s ->
>              Subst s (Subst (SingleSub t2) t1)
>          :~: Subst (SingleSub (Subst s t2)) (Subst (Lift s) t1)
> axiom2 s = unsafeCoerce Refl


* Property (Monoid)

> instance Semigroup (Sub a) where
>   (<>) = (:<>)
> instance Monoid (Sub a) where
>    mempty = IdS


> prop_Assoc :: (Eq a, SubstC a) => Sub a -> Sub a -> Sub a -> Idx -> Bool
> prop_Assoc s1 s2 s3 x = applySub ((s1 <> s2) <> s3) x == applySub (s1 <> (s2 <> s3)) x

> prop_IdL :: (Eq a, SubstC a) => Sub a -> Idx -> Bool
> prop_IdL s x = applySub (s <> IdS) x == applySub s x

> prop_IdR :: (Eq a, SubstC a) => Sub a -> Idx -> Bool
> prop_IdR s x = applySub (IdS <> s) x == applySub s x


* Property 0

This is a property that is true about well-formed instances of SubstC. Say we
view Exp above as a functor, where the argument is 'Idx'

> prop_Id :: (Eq a, SubstC a) => a -> Bool
> prop_Id x = subst IdS x == x 

> prop_Comp :: (Eq a, SubstC a) => Sub a -> Sub a -> a -> Bool
> prop_Comp s1 s2 x = subst s2 (subst s1 x) == subst (s1 <> s2) x


* Arbitrary instances

> instance Arbitrary Idx where
>   arbitrary = oneof [ return Z, S <$> arbitrary ]
>   shrink Z     = []
>   shrink (S n) = [n]

     
> instance Arbitrary a => Arbitrary (Sub a) where
>  arbitrary = sized gt where
>    base = elements [IdS, Inc]
>    gt m =
>      if m <= 1 then base else
>      let m' = m `div` 2 in
>      frequency
>      [(1, base),
>       (1, (:·)    <$> arbitrary <*> gt m'), 
>       (1, (:<>)   <$> gt m'     <*> gt m')]
>
>  shrink IdS = []
>  shrink Inc = [IdS]
>  shrink (t :· s)   = s : [t' :· s' | t' <- shrink t, s' <- shrink s]
>  shrink (s1 :<> s2) = s1 : s2 :
>    [s1' :<> s2 | s1' <- shrink s1, s2' <- shrink s2]                       

> instance Arbitrary Exp where
>   arbitrary = sized gt where
>    base = oneof [VarE <$> arbitrary]
>    gt m =
>      if m <= 1 then base else
>      let m' = m `div` 2 in
>      frequency
>      [(1, base),
>       (1, LamE    <$>  gt m')]
>
>   shrink (VarE n) = [VarE n' | n' <- shrink n ]
>   shrink (LamE s)   = s : [ LamE s' | s' <- shrink s]
