
\begin{code}
data ESub g g' where
  EIncSub   :: Proxy tys -> Sing (Length g1) -> ESub g (g1 ++ g)
  EConsSub  :: Exp g' ty -> ESub g g' -> ESub (ty:g) g'
  ECompSub  :: ESub g1 g2 -> ESub g2 g3 -> ESub g1 g3


--eLiftSub    :: forall g1 g g'. Sing (Length g1) -> ESub g g' -> ESub (g1++g) (g1++g')
--eLiftSub n s = eUpTo @g1 n (ECompSub s (EIncSub (Proxy :: Proxy g1) n))
{-
eUpTo :: forall g1 g g'. Sing (Length g1) -> ESub g g' -> ESub (g1 ++ g) g'
eUpTo SZ s
  |  Refl <- axiom_LengthZIsNil (undefined :: Sing g1) = s
eUpTo (SS m) s
  |  MkIsCons ty g1' <- axiom_LengthSIsCons (undefined :: Sing g1) m
  =  undefined -- eUpTo m (EVar m `EConsSub` s)

lemma_LengthZIsNil :: (Length g1 ~ Z) => Sing g1 -> (g1 :~: '[])
lemma_LengthZIsNil SNil = Refl

axiom_LengthZIsNil :: (Length g1 ~ Z) => Sing g1 -> (g1 :~: '[])
axiom_LengthZIsNil _ = unsafeCoerce Refl

data IsCons g m where
  MkIsCons :: (Length g' ~ m) => Sing ty -> Sing g' -> IsCons (ty ': g') m

lemma_LengthSIsCons :: (Length g1 ~ S m) => Sing g1 -> Sing m -> IsCons g1 m
lemma_LengthSIsCons (SCons ty g) _ = MkIsCons ty g

axiom_LengthSIsCons :: (Length g1 ~ S m) => Sing g1 -> Sing m -> IsCons g1 m
axiom_LengthSIsCons _ _ = unsafeCoerce (MkIsCons undefined undefined)
-}

{-
incESub k (EIncSub (p :: Proxy g1) n)
   -- g' is (g1 ++ g)
   -- n is Length g1
   -- WTP ESub (IncList k g) (IncList k (g1 ++ g))
   -- where n is Length (IncList k g1)
  |  Refl <- axiom_LengthIncList k (undefined :: Sing g1)
  ,  Refl <- axiom_IncListAppend k (undefined :: Sing g1) (undefined:: Sing g) =
      EIncSub (Proxy :: Proxy (IncList k g1)) n
-}


{-
axiom_LengthIncList :: forall n tys.
  Sing n -> Sing tys ->
  Length (IncList n tys) :~: Length tys
axiom_LengthIncList _ _ = unsafeCoerce Refl  

axiom_IncListAppend :: forall k t1 t2.
  Sing k -> Sing t1 -> Sing t2 ->
  IncList k (t1 ++ t2) :~: IncList k t1 ++ IncList k t2
axiom_IncListAppend _ _ = unsafeCoerce Refl  
-}

--applyESub (EIncSub (p :: Proxy g1) n)  v
--  | Refl <- axiom_IdxPlus (undefined :: Sing g1) (undefined :: Sing g) v
--  = EVar (sPlus n v)

{- applyESub (ETailSub s)   v = applyESub s (SS v)

applyESub (ELiftSub s)   v = case v of
                                SZ -> EVar SZ
                                (SS m) -> substE EIncSub (applyESub s m) -}

axiom_IdxPlus :: forall ty g g1 k.
  (Idx g k ~ Just ty) =>
  Sing g1 -> Sing g -> Sing k ->
  Idx (g1 ++ g) (Plus (Length g1) k) :~: Just ty
axiom_IdxPlus _ _ _ = unsafeCoerce Refl


\end{code}
