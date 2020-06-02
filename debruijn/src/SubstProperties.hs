{-# LANGUAGE TemplateHaskell #-}
module SubstProperties(axiom1, axiom2, axiom_map1) where

import AssertEquality
import Imports
import Nat
import Subst

import Test.QuickCheck

-- To test generic properties, we need to have an instance.
-- Therefore, we define a simple languages with variables and
-- binding to use with quickcheck.
  

data Exp :: Type where
  VarE   :: Idx  -> Exp 
  LamE   :: Exp  -> Exp          
    deriving (Eq, Show)

instance SubstC Exp where
  var = VarE
  subst s (VarE x)  = applyS s x
  subst s (LamE e)  = LamE (subst (lift s) e)




-------------------------------------------------------------------

-- Here is a property that we need about our substitution function.
-- Why should we believe it? Note that if we are *wrong* about this property
-- we could break Haskell.
axiom1 :: forall g s. Sing s ->
           Map (SubstSym1 (LiftSym1 s)) (Map (SubstSym1 IncSub) g) :~: 
           Map (SubstSym1 IncSub) (Map (SubstSym1 s) g)
axiom1 s = assertEquality

-- We could use quickcheck to convince us, by generating a lot of test cases.
prop1 :: Sub Exp -> [Exp] -> Bool
prop1 s g = map (subst (lift s)) (map (subst incSub) g) == 
            map (subst incSub) (map (subst s) g)


-- With effort, we can also check this property at runtime. But this
-- also requires that we keep around more information at runtime.
check1 :: forall a (g ::[a]) (s :: Sub a).
          (TestEquality (Sing :: a -> Type), SSubstC a, SDecide a) =>
          Sing g -> Sing s ->
           Maybe (Map (SubstSym1 (LiftSym1 s)) (Map (SubstSym1 IncSub) g) :~: 
                  Map (SubstSym1 IncSub) (Map (SubstSym1 s) g))
check1 g s = 
  testEquality
  (sMap (SLambda @_ @_ @(SubstSym1 (LiftSym1 s)) (sSubst (sLift s)))
     (sMap (SLambda @_ @_ @(SubstSym1 IncSub) (sSubst sIncSub)) g))
  (sMap (SLambda @_ @_ @(SubstSym1 IncSub) (sSubst sIncSub))
     (sMap (SLambda @_ @_ @(SubstSym1 s) (sSubst s)) g))
  

-------------------------------------------------------------------

prop2 :: Sub Exp -> Exp -> Exp -> Bool
prop2 s t2 x = subst s (subst (singleSub t2) x) == subst (singleSub (subst s t2)) (subst (lift s) x)

axiom2 :: forall t1 t2 s . Sing s ->
             Subst s (Subst (SingleSub t2) t1) :~: Subst (SingleSub (Subst s t2)) (Subst (Lift s) t1)
axiom2 s = assertEquality

prop3 :: Sub Exp -> Sub Exp -> [Exp] -> Bool
prop3 s1 s2 g = map (subst s2) (map (subst s1) g) == map (subst (s1 <> s2)) g

axiom3 :: forall s1 s2 g. Map (SubstSym1 s2) (Map (SubstSym1 s1) g) :~: Map (SubstSym1 (s1 <> s2)) g
axiom3 = assertEquality

prop4 :: Exp -> Sub Exp -> Bool
prop4 t s = Inc (S Z) <> (t :< s) == s

axiom4 :: forall t s. (Inc (S Z)) <> (t :< s) :~: s
axiom4 = assertEquality

prop5 :: [Exp] -> Bool
prop5 g = map (subst (Inc Z)) g == g

axiom5 :: forall g. Map (SubstSym1 (Inc Z)) g :~: g
axiom5 = assertEquality


-------------------------------------------------------------------

instance Semigroup (Sub a) where
  (<>)    = (:<>)
instance Monoid (Sub a) where
   mempty = nilSub

prop_assoc :: Sub Exp -> Sub Exp -> Sub Exp -> Idx -> Bool
prop_assoc s1 s2 s3 x = applyS ((s1 <> s2) <> s3) x == applyS (s1 <> (s2 <> s3)) x

prop_idL :: Sub Exp -> Idx -> Bool
prop_idL s x = applyS (s <> nilSub) x == applyS s x

prop_idR :: Sub Exp -> Idx -> Bool
prop_idR s x = applyS (nilSub <> s) x == applyS s x

prop_id :: Exp -> Bool
prop_id x = subst nilSub x == x 

prop_comp :: Sub Exp -> Sub Exp -> Exp -> Bool
prop_comp s1 s2 x = subst s2 (subst s1 x) == subst (s1 <> s2) x


-------------------------------------------------------------------
-- Properties about lists (maybe these belong in another file?)


prop_map1 :: Fun Int Int -> [Int] -> [Int] -> Bool
prop_map1 s g1 g2 = map (applyFun s) (g1 ++ g2) == map (applyFun s) g1 ++ map (applyFun s) g2

axiom_map1 :: forall s g1 g2. Map s (g1 ++ g2) :~: Map s g1 ++ Map s g2
axiom_map1 = assertEquality

prop_map2 :: [Int] -> Bool 
prop_map2 g = map id g == g

axiom_map2 :: forall g. Map IdSym0 g :~: g
axiom_map2 = assertEquality

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

-------------------------------------------------------------------
--

return []
runTests = $quickCheckAll
