{-# LANGUAGE TemplateHaskell #-}
module SubstProperties(axiom1, axiom2, axiom_map1) where

import Imports
import Subst

import Test.QuickCheck
 
import Unsafe.Coerce

$(singletons [d|
   data Exp :: Type where
     VarE   :: Idx  -> Exp 
     LamE   :: Exp  -> Exp          
       deriving (Eq, Show)

   instance SubstC Exp where
     var = VarE
     subst s (VarE x)  = applyS s x
     subst s (LamE e)  = LamE (subst (lift s) e)

   |])

-------------------------------------------------------------------

axiom_map1 :: forall s g1 g2. Map s (g1 ++ g2) 
                       :~: Map s g1 ++ Map s g2
axiom_map1 = unsafeCoerce Refl                       

-------------------------------------------------------------------

--substList :: SubstC a => Sub a -> [a] -> [a]
    --substList s = map (subst s)
 
    --incList :: SubstC a => [a] -> [a]
    --incList = substList incSub
 
    --liftList :: SubstC a => Sub a -> [a] -> [a]
    --liftList s = substList (lift s)

prop1 :: Sub Exp -> [Exp] -> Bool
prop1 s g = map (subst (lift s)) (map (subst incSub) g) == 
            map (subst incSub) (map (subst s) g)

axiom1 :: forall g s. Sing s ->
           Map (SubstSym1 (LiftSym1 s)) (Map (SubstSym1 IncSub) g) :~: 
           Map (SubstSym1 IncSub) (Map (SubstSym1 s) g)
axiom1 s = unsafeCoerce Refl

lemma1 :: forall (g :: [Exp]) s. Sing s -> Sing g ->
           Map (SubstSym1 (LiftSym1 s)) (Map (SubstSym1 IncSub) g) :~: 
           Map (SubstSym1 IncSub) (Map (SubstSym1 s) g)
lemma1 s SNil = Refl
lemma1 s (SCons x xs)
   | Refl <- lemma1 s xs,
     Refl <- aux1 s x = Refl

aux1 :: forall s x. Sing s -> Sing (x::Exp) -> 
    Subst (Lift s) (Subst IncSub x) :~: Subst IncSub (Subst s x)
aux1 s (SVarE n) = Refl
aux1 s (SLamE e)
 | Refl <- aux1 (sLift s) e
 = undefined

-------------------------------------------------------------------


prop2 :: Sub Exp -> Exp -> Exp -> Bool
prop2 s t2 x = subst s (subst (singleSub t2) x) == 
     subst (singleSub (subst s t2)) (subst (lift s) x)

axiom2 :: forall t1 t2 s . Sing s ->
             Subst s (Subst (SingleSub t2) t1)
         :~: Subst (SingleSub (Subst s t2)) (Subst (Lift s) t1)
axiom2 s = unsafeCoerce Refl

-------------------------------------------------------------------

instance Semigroup (Sub a) where
  (<>)    = (:<>)
instance Monoid (Sub a) where
   mempty = nil

prop_Assoc :: (Eq a, SubstC a) => Sub a -> Sub a -> Sub a -> Idx -> Bool
prop_Assoc s1 s2 s3 x = applyS ((s1 <> s2) <> s3) x == applyS (s1 <> (s2 <> s3)) x

prop_IdL :: (Eq a, SubstC a) => Sub a -> Idx -> Bool
prop_IdL s x = applyS (s <> nil) x == applyS s x

prop_IdR :: (Eq a, SubstC a) => Sub a -> Idx -> Bool
prop_IdR s x = applyS (nil <> s) x == applyS s x

prop_Id :: (Eq a, SubstC a) => a -> Bool
prop_Id x = subst nil x == x 

prop_Comp :: (Eq a, SubstC a) => Sub a -> Sub a -> a -> Bool
prop_Comp s1 s2 x = subst s2 (subst s1 x) == subst (s1 <> s2) x

-------------------------------------------------------------------

instance Arbitrary a => Arbitrary (Sub a) where
 arbitrary = sized gt where
   base = Inc <$> arbitrary
   gt m =
     if m <= 1 then base else
     let m' = m `div` 2 in
     frequency
     [(1, base),
      (1, (:<)    <$> arbitrary <*> gt m'), 
      (1, (:<>)   <$> gt m'     <*> gt m')]
 
 shrink (Inc n) = [Inc n' | n' <- shrink n]
 shrink (t :< s)   = s : [t' :< s' | t' <- shrink t, s' <- shrink s]
 shrink (s1 :<> s2) = s1 : s2 :
   [s1' :<> s2 | s1' <- shrink s1, s2' <- shrink s2]                       

instance Arbitrary Exp where
  arbitrary = sized gt where
   base = oneof [VarE <$> arbitrary]
   gt m =
     if m <= 1 then base else
     let m' = m `div` 2 in
     frequency
     [(1, base),
      (1, LamE    <$>  gt m')]
 
  shrink (VarE n) = [VarE n' | n' <- shrink n ]
  shrink (LamE s)   = s : [ LamE s' | s' <- shrink s]

