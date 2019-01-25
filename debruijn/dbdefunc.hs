module Defunc where

import Prelude hiding (repeat)
import Test.QuickCheck

data Nat = Z | S Nat deriving (Eq)

data Ctx = CtxEmpty | CtxCons Ctx CrucibleType deriving (Eq)

data CrucibleType = BaseType | VarType Nat | FnType Ctx CrucibleType
  | PolyFnType Nat Ctx CrucibleType deriving (Eq,Show)

data Renaming = Succ | Lift Renaming deriving (Eq,Show)

data Sub = IdSub | ConsSub CrucibleType Sub | LiftSub Sub | TailSub Sub | SuccSub
  deriving (Eq, Show)

----------------------------------------------------------
ctxToList :: Ctx -> [CrucibleType]
ctxToList CtxEmpty = []
ctxToList (CtxCons c ct) = ct : ctxToList c
instance Show Ctx where
  show c = show (ctxToList c)

natToInt :: Nat -> Int
natToInt Z = 0
natToInt (S m) = 1 + natToInt m

instance Show Nat where
  show = show . natToInt

  
----------------------------------------------------------

fi :: Integer -> Nat
fi n = if n == 0 then Z
    else if n < 0 then fi (-n)
    else S (fi (n - 1))

upto :: Nat -> [Nat]
upto Z = []
upto (S m) = m : upto m

plus :: Nat -> Nat -> Nat
plus Z n = n
plus (S m) n = S (plus m n)
  
instance Arbitrary Nat where
  arbitrary = fi <$> arbitrary
  shrink Z = []
  shrink (S n) = [n]

fl :: [CrucibleType] -> Ctx
fl [] = CtxEmpty
fl (x:xs) = CtxCons (fl xs) x

instance Arbitrary Ctx where
  arbitrary = fl <$> arbitrary

instance Arbitrary CrucibleType where
  arbitrary = sized (gt Z) where
    base n = oneof (return BaseType : [return (VarType k) | k <- upto (fi 5) ])
    gl :: Nat -> Int -> Gen Ctx
    gl n m = (gt n m) >>= \ty -> return (CtxCons CtxEmpty ty)
    
    gt :: Nat -> Int -> Gen CrucibleType
    gt n m =
      if m <= 1 then base n
      else
      let m' = m `div` 2 in
      frequency
      [(2, base n),
       (1, FnType <$> gl n m' <*> gt n m'),
       (1, do
           k <- elements [Z, S Z, S (S Z), S (S (S Z))]
           a <- gl (plus n k) m'
           r <- gt (plus n k) m'
           return (PolyFnType k a r))]

instance Arbitrary Renaming where
  arbitrary = gr <$> arbitrary  where
    gr :: Int -> Renaming
    gr 0 = Succ
    gr n = if n < 0 then gr (-n) else Lift (gr (n -1))
  shrink Succ = []
  shrink (Lift n) = [n]

instance Arbitrary Sub where
  arbitrary = sized gt where
    base = elements [IdSub, SuccSub]
    gt m =
      if m <= 1 then base else
      let m' = m `div` 2 in
      frequency
      [(1, base),
       (1, ConsSub <$> arbitrary <*> gt m'), -- always closed? FVs?
       (1, LiftSub <$> gt m'),
       (1, TailSub <$> gt m')]

    
----------------------------------------------------------
  
ctxSize :: Ctx -> Nat
ctxSize CtxEmpty = Z
ctxSize (CtxCons c _) = S (ctxSize c)



applyr :: Renaming -> Nat -> Nat
applyr Succ = S
applyr (Lift r) = \n -> case n of
                          Z -> Z
                          (S n) -> S (applyr r n)

repeat a Z x = x
repeat a (S n) x = a (repeat a n x)
                          
rename :: Renaming -> CrucibleType -> CrucibleType
rename r BaseType = BaseType
rename r (VarType k)= VarType (applyr r k)
rename r (FnType args ret) =
  FnType (renameCtx r args) (rename r ret)
rename r (PolyFnType k args ret) =
  PolyFnType k (renameCtx (repeat Lift k r) args) (rename (repeat Lift k r) ret)
  
renameCtx r CtxEmpty = CtxEmpty
renameCtx r (CtxCons ctx' ty) = CtxCons (renameCtx r ctx') (rename r ty)

applys :: Sub -> Nat -> CrucibleType
applys IdSub = \x -> VarType x
applys (ConsSub e s) = \x -> case x of
  Z -> e
  (S m) -> applys s m
applys (LiftSub s) = \x -> case x of
  Z -> VarType Z
  (S m) -> rename Succ (applys s m)
applys (TailSub s) = \x -> applys s (S x)
applys SuccSub = \x -> VarType (S x)

subst :: Sub -> CrucibleType -> CrucibleType
subst s BaseType = BaseType
subst s (VarType k) = applys s k
subst s (FnType a r) = FnType (substCtx s a) (subst s r)
subst s (PolyFnType k a r) = PolyFnType k
  (substCtx (repeat LiftSub k s) a) (subst (repeat LiftSub k s) r)

substCtx :: Sub -> Ctx -> Ctx
substCtx s CtxEmpty = CtxEmpty
substCtx s (CtxCons c e) = CtxCons (substCtx s c) (subst s e)

composeSub s IdSub = s
composeSub s (ConsSub ty s2) = ConsSub (subst s ty) (composeSub s s2)
composeSub s (LiftSub s2) = ConsSub (applys s Z) (composeSub (TailSub s) s2)
composeSub s SuccSub = TailSub s
composeSub s (TailSub s2) = TailSub (composeSub s s2)


----------------------------------------------------------------------
----------------------------------------------------------------------
prop_repeat_repeat :: Nat -> Nat -> Renaming -> Bool
prop_repeat_repeat n n0 x = 
  repeat Lift n (repeat Lift n0 x) == repeat Lift (plus n n0) x

prop_tail_sub_compose :: Sub -> CrucibleType -> Bool
prop_tail_sub_compose s1 x =
  subst (TailSub s1) x == subst s1 (rename Succ x)

prop_subterm_equiv ct =
  rename Succ ct == subst SuccSub ct

prop_compose_lemma x s1 s2 =
  subst (composeSub s1 s2) x == subst s1 (subst s2 x)

-- fails (as expected)
prop_compose_tail_sub_2 k2 k1 x n =
    applys (composeSub (repeat TailSub n k1) k2) x ==
    repeat (rename Succ) n (applys (composeSub k1 k2) x)

-- fails (as expected)
prop_lift_rename k n0 n =
   rename (repeat Lift n Succ) (rename (repeat Lift n0 Succ) k) ==
   rename (Lift (repeat Lift n0 Succ)) (rename (repeat Lift n Succ) k)

prop_bar n0 k1 n =
  rename Succ (rename (repeat Lift n0 Succ) (applys (repeat LiftSub n0 k1) n)) ==
  rename (Lift (repeat Lift n0 Succ))(rename Succ (applys (repeat LiftSub n0 k1) n))

prop_foo n n0 k1 =
  applys (repeat LiftSub n0 (LiftSub k1)) (applyr (repeat Lift n0 Succ) n) ==
  rename (repeat Lift n0 Succ) (applys (repeat LiftSub n0 k1) n)

prop_lift_subst_rename c n k1 =
  subst (repeat LiftSub n (LiftSub k1)) (rename (repeat Lift n Succ) c) ==
             rename (repeat Lift n Succ) (subst (repeat LiftSub n k1) c)

prop_rename_compose k2 k1 n =
  applys (composeSub (TailSub (LiftSub k1)) k2) n == 
  rename Succ (applys (composeSub k1 k2) n)

prop_baz n0 n r1 r2 =
  applys (repeat LiftSub n0 (composeSub r1 r2)) n ==
  applys (composeSub (repeat LiftSub n0 r1) (repeat LiftSub n0 r2)) n

prop_rename_succ_tail c s =
   subst (TailSub s) c == subst s (subst SuccSub c)

prop_cons_sub ty ss tt =
  subst (ConsSub ty ss) (subst SuccSub tt) == subst ss tt

qc :: Testable prop => prop -> IO ()
qc = quickCheckWith (stdArgs { maxSuccess = 500 })
