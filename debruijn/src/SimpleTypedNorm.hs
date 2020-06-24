module SimpleTypedNorm where

import Imports
import SubstTyped
import SimpleTyped

import qualified Control.Category as C

-----------------------------------------------------------------------
-- Evaluation to normal form

-- The key take away is that this is mostly boilerplate.

-- Yet another variant of 'Exp'.
--
-- How handy that Neutral and Normal start with letter N.
--
newtype Norm g t = Norm (GenNorm Norm g t)
type Neut = GenNeut Norm

-- We define more generic version of 'Norm' and 'Neut',
-- so we can define WHNF.
--
data GenNeut :: ([Ty] -> Ty -> Type) -> [Ty] -> Ty -> Type where
 VarN   :: Idx g t               -- variable index
        -> GenNeut norm g t

 AppN   :: GenNeut norm g (t1 :-> t2)     -- function
        -> norm      g t1              -- argument
        -> GenNeut norm g t2

 FstN   :: GenNeut norm g (t1 :* t2)
        -> GenNeut norm g t1

 SndN   :: GenNeut norm g (t1 :* t2)
        -> GenNeut norm g t2

data GenNorm :: ([Ty] -> Ty -> Type) -> [Ty] -> Ty -> Type where
 IntN   :: Int
        -> GenNorm norm g IntTy

 LamN   :: Π (t1 :: Ty)           -- type of binder
        -> norm (t1:g) t2         -- body of abstraction
        -> GenNorm norm g (t1 :-> t2)

 PairN  :: norm g t1
        -> norm g t2
        -> GenNorm norm g (t1 :* t2)

 UnitN  :: GenNorm norm g UnitTy

 NeutN  :: GenNeut norm g t -> GenNorm norm g t

-- | Like 'reduce' but using 'Norm' as result.
--
-- We can remove the equation
--
--     reduce (AppE (LamE t e1) e2) = ...
--
-- from the definition of 'reduce' - and we won't notice the cheat.
-- with 'Norm' type-check is unforgiving.
--
-- (In fact, I think that 'reduce'  some redexes)
--
reduceN :: Exp g t -> Norm g t
reduceN (IntE x)      = Norm (IntN x)
reduceN (VarE x)      = Norm (NeutN (VarN x))
reduceN (LamE t e)    = Norm (LamN t (reduceN e))
reduceN (PairE e1 e2) = Norm (PairN (reduceN e1) (reduceN e2))
reduceN UnitE         = Norm UnitN
reduceN (AppE e1 e2) = case evalW e1 of
  NeutN e1'  -> Norm (NeutN (AppN (reduceW e1') (reduceN e2)))
  LamN t e1' ->
      -- here we have various reduction strategies
      -- The following is easiest without any additional machinery,
      -- substitute terms as is. This most likely duplicates work.
      --
      --   reduceN (subst (singleSub e2) e1')
      --
      -- or we can do
      --
      --  reduceN (subst (singleSub (norm2exp (reduceN e2))) (norm2exp (reduceN e1')))
      --  ^ I think the reduceN after subst is missing from 'reduce' on 'Exp'.
      --
      -- or we can define substitution on 'Norm'!
      --
      subst (singleSub (reduceN e2)) (reduceN e1')

      -- these three strategies reduce differenty, but
      -- the types tell that we get a normal form at the end.
      -- (And the meta-theory tells that it will be the same).

reduceN (FstE e) = case evalW e of
   NeutN e'   -> Norm (NeutN (FstN (reduceW e')))
   PairN e' _ -> reduceN e'

reduceN (SndE e) = case evalW e of
   NeutN e'   -> Norm (NeutN (SndN (reduceW e')))
   PairN _ e' -> reduceN e'

-- again, (almost) the same instance definition as before.
--
-- keyword: hereditary substitutions
instance SubstDB Norm where
   var = Norm . NeutN . VarN

   subst s (Norm (IntN x))         = Norm (IntN x)
   subst s (Norm (LamN ty e))      = Norm (LamN ty (subst (lift s) e))
   subst s (Norm (NeutN (VarN x))) = applySub s x
   subst s (Norm UnitN)            = Norm UnitN
   subst s (Norm (PairN e1 e2))    = Norm (PairN (subst s e1) (subst s e2))

   -- substitution in application causes evaluation,
   -- i.e. recursive substitutions.
   subst s (Norm (NeutN (AppN e1 e2))) = case subst s (Norm (NeutN e1)) of
     Norm (NeutN e1')   -> Norm (NeutN (AppN e1' e2'))
     Norm (LamN ty e1') -> subst (singleSub e2') e1'
     where
       e2' = subst s e2

   subst s (Norm (NeutN (FstN e))) = case subst s (Norm (NeutN e)) of
     Norm (NeutN e')   -> Norm (NeutN (FstN e'))
     Norm (PairN e' _) -> e'

   subst s (Norm (NeutN (SndN e))) = case subst s (Norm (NeutN e)) of
     Norm (NeutN e')   -> Norm (NeutN (SndN e'))
     Norm (PairN _ e') -> e'

-- | A helper for 'reduceN', fully evaluate
reduceW :: GenNeut Exp g t ->  GenNeut Norm g t
reduceW (VarN n)     = VarN n
reduceW (AppN e1 e2) = AppN (reduceW e1) (reduceN e2)
reduceW (FstN e)     = FstN (reduceW e)
reduceW (SndN e)     = SndN (reduceW e)

norm2exp :: Norm g t -> Exp g t
norm2exp (Norm (IntN x))      = IntE x
norm2exp (Norm (LamN t x))    = LamE t (norm2exp x)
norm2exp (Norm (NeutN e))     = neut2exp e
norm2exp (Norm (PairN e1 e2)) = PairE (norm2exp e1) (norm2exp e2)
norm2exp (Norm UnitN)         = UnitE

neut2exp :: Neut g t -> Exp g t
neut2exp (VarN x)     = VarE x
neut2exp (AppN e1 e2) = AppE (neut2exp e1) (norm2exp e2)
neut2exp (FstN e)     = FstE (neut2exp e)
neut2exp (SndN e)     = SndE (neut2exp e)

-- | A term in WHNF is normal form where
-- non-head positions (lambda body, application argument) aren't
-- evaluated, i.e. are 'Exp'.
type WHNF = GenNorm Exp

-- | Like 'evalW but in any context.
evalW :: Exp g t -> WHNF g t
evalW (IntE x)      = IntN x
evalW (VarE n)      = NeutN (VarN n)
evalW (LamE t e)    = LamN t e
evalW (PairE e1 e2) = PairN e1 e2
evalW UnitE         = UnitN
evalW (AppE e1 e2)  = case evalW e1 of
  LamN t e1' -> evalW $ subst (singleSub e2) e1'
  NeutN e1'  -> NeutN (AppN e1' e2)
evalW (FstE e)      = case evalW e of
  PairN e' _ -> evalW e'
  NeutN e'   -> NeutN (FstN e')
evalW (SndE e)      = case evalW e of
  PairN _ e' -> evalW e'
  NeutN e'   -> NeutN (SndN e')

-------------------------------------------------------------------------------
-- Curry-Howard-Lambek isomorphism
-------------------------------------------------------------------------------

-- First we define a type-class for cartesian closed categories.
--
-- Implementation note:
-- In theory, SingI could/should be on every type variable
-- In practice, that would make writing instance below quite painful,
-- so we require only the `SingI` where we really need one: in LamE.
--
class C.Category cat => CCC cat where
    -- product
    exl   :: cat (a :* b) a
    exr   :: cat (a :* b) b
    (***) :: cat a b -> cat a c -> cat a (b :* c)

    -- unit
    uni   :: cat a UnitTy

    -- exponential object
    eval :: cat ((a :-> b) :* a) b
    transpose :: SingI b => cat (a :* b) c -> cat a (b :-> c)

    -- because our STLC has an IntE values, we add it too,
    -- so we get
    --
    -- CCC with integer object.
    --
    int :: Int -> cat a IntTy

-- We can interpret any @Exp g ty@ term as CCC

type family PairCtx (g :: [Ty]) :: Ty where
    PairCtx '[]   = UnitTy
    PairCtx (t:g) = PairCtx g :* t -- to fit `transpose

idxToCCC :: CCC cat => Idx g t -> cat (PairCtx g) t
idxToCCC Z     = exr
idxToCCC (S s) = idxToCCC s C.<<< exl

expToCCC :: CCC cat => Exp g ty -> cat (PairCtx g) ty
expToCCC (VarE e)      = idxToCCC e
expToCCC UnitE         = uni
expToCCC (IntE x)      = int x
expToCCC (PairE e1 e2) = expToCCC e1 *** expToCCC e2
expToCCC (FstE e)      = exl C.<<< expToCCC e
expToCCC (SndE e)      = exr C.<<< expToCCC e
expToCCC (AppE e1 e2)  =
  let f = expToCCC e1
      g = expToCCC e2
  in eval C.<<< f *** g
expToCCC (LamE t e)    =
  let f = expToCCC e -- :: cat (PairCtx (t1:g)) t2
                      -- ~  cat (PairCtx g :* t1) t2
  in withSingI t $ transpose f

-- | We can also turn 'Exp' into a category:
--
-- By picking morphisms to be "a |- b" proofs (and not e.g. |- a :-> b)
-- we make our life a lot easier.
--
newtype Morphism a b = M { getMorphism :: Exp '[a] b }

instance C.Category Morphism where
    id = M $ VarE Z
    M f . M g = M $ subst (s1 :<> s2) (VarE Z)
      where
        s1 = f :< nilSub
        s2 = g :< incSub

instance CCC Morphism where
    exl         = M $ FstE (VarE Z)
    exr         = M $ SndE (VarE Z)
    M f *** M g = M $ subst (f :< g :< nilSub) (PairE (VarE Z) (VarE (S Z)))

    eval = M $ AppE (FstE (VarE Z)) (SndE (VarE Z))
    transpose (M f) = M $ LamE sing $ subst s f
      where
        s = PairE (VarE (S Z)) (VarE Z) :< Inc (IS (IS IZ))

    uni   = M $ UnitE
    int n = M $ IntE n

-- functional completeness, we can omit UnitTy from the context.
funcomp :: Exp '[UnitTy] t -> Exp '[] t
funcomp = subst (UnitE :< nilSub)

-- This is a function which maps closed Exp to CCC (arrow UnitTy -> t) and back.
roundtripExp :: Exp '[] t -> Exp '[] t
roundtripExp = funcomp . getMorphism . expToCCC

roundtripNorm :: Norm '[] t -> Norm '[] t
roundtripNorm = reduceN . roundtripExp . norm2exp

-- |
--
-- If we start with a value
--
-- >>> norm2exp $ curryExp @IntTy @IntTy @IntTy
-- LamE (SIntTy :%-> (SIntTy :%-> SIntTy)) (LamE (SIntTy :%* SIntTy) (AppE (AppE (VarE (S Z)) (FstE (VarE Z))) (SndE (VarE Z))))
--
-- we can interpret that STLC expression in any CCC.
-- For example Morphism, which is an instance of CCC.
-- If we roundtrip our example expression
--
-- >>> norm2exp $ roundtripNorm $ curryExp @IntTy @IntTy @IntTy
-- LamE (SIntTy :%-> (SIntTy :%-> SIntTy)) (LamE (SIntTy :%* SIntTy) (AppE (AppE (VarE (S Z)) (FstE (VarE Z))) (SndE (VarE Z))))
--
-- we get what we started with.
--
-- This illustrates by example the Curry-Howard-Lambek isomorphism,
-- which say (among other things)
--
--     roundtripNorm = id
--
-- Some comments:
--
-- - I'm not sure if in this direction one could construct an example
--   which would require eta-expansion/reduction.
--   We don't case on types, so nothing is expanded nor reduced.
--   Yet, types don't tell us that.
--
-- - One could implement a CCC instance which draws diagrams
--   (= generates code which draws diagrams).
--   It would be fun to visualise (function type) expressions in that way.
--
curryExp
  :: (SingI a, SingI b, SingI c)
  =>  Norm '[] ((a :-> (b :-> c)) :-> ((a :* b) :-> c))
curryExp = reduceN $ LamE sing $ LamE sing $ AppE (AppE (VarE (S Z)) (FstE (VarE Z))) (SndE (VarE Z))
