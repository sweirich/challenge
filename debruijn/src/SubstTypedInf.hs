 {-# LANGUAGE TemplateHaskell #-}
module SubstTypedInf
  (
   Sub,
   Idx(..), idxToInt,
   applySub,  
   nilSub,    
   weakSub,   
   singleSub, 
   lift,      
   SubstDB(..),
   IncI(..),
   ) where

import qualified Nat (Nat(..),SNat(..),Length,length,LengthSym0)
import Imports

-- we need some "axioms" to make this version type check
import Unsafe.Coerce

-- An index: (i.e. just a natural number)
-- This is sometimes called `elem` as it is a proof
-- that t is contained in the list g
data Idx (g :: [k]) (t::k) :: Type where
  Z :: Idx (t:g) t
  S :: Idx g t -> Idx (u:g) t


idxToInt :: Idx g t -> Int
idxToInt Z = 0
idxToInt (S m) = 1 + idxToInt m
  

-- Another form of natural number, indexed by a list
-- of that length
data IncBy (g :: [k]) where
   IZ :: IncBy '[]
   IS :: Proxy t -> IncBy n -> IncBy (t:n)

append :: IncBy g -> IncBy g' -> IncBy (g ++ g')
append IZ i = i
append (IS p n) i = IS p (append n i)

-- An implicit version of the above. If we have a static list
-- we can get the class system to determine its length.
class IncI g where incBy :: IncBy g
instance IncI '[] where incBy = IZ
instance IncI g => IncI (t:g) where incBy = IS Proxy incBy

-- Supply an explicit argument where an implicit one is expected.
withIncI :: IncBy g -> (IncI g => a) -> a
withIncI = unsafeCoerce (flip ($) :: IncBy a -> (IncBy a -> r) -> r)


incIdx :: Idx g t -> Idx (u:g) t
incIdx Z     = (S Z)
incIdx (S n) = S (incIdx n)

weakIdx :: forall g1 g t. Idx g t -> Idx (g ++ g1) t
weakIdx Z     = Z
weakIdx (S n) = S (weakIdx @g1 n)

add :: IncBy g1 -> Idx g t -> Idx (g1 ++ g) t
add IZ      i = i
add (IS _ xs) i = S (add xs i)



-- Given a list of length n, create the substitution
-- var (0 of n) : var (1 of n) : var (2 of n) ... : Nil
-- note: g ~ (g' ++ g1) doesn't change in this recursion, and it is a finite list
-- g' starts at [] and increases while g1 starts at g and decreases.
go :: forall g' g1 a.
      (SubstDB a, IncI g1) =>
      IncBy g' -> Sub a g1 g1 -> Sub a (g' ++ g1) (g' ++ g1)
go IZ s = s
go (IS (_ :: Proxy u) (n :: IncBy g)) s =
  withIncI (append n (incBy @g1)) $
      (lift (go @g n s) :: Sub a (u : g ++ g1) (u : g ++ g1)) 


axiom1 :: forall g. (g ++ '[]) :~: g
axiom1 = unsafeCoerce Refl

 
data Sub a g g' where
  Cons :: a g' t -> Sub a g g' -> Sub a (t:g) g'
  -- have to add this
  Nil  :: Sub a '[] '[]

applySub :: SubstDB a => Sub a g g' -> Idx g t -> a g' t
applySub (Cons t _)     Z = t
applySub (Cons _ s) (S n) = applySub s n
applySub Nil            x = var x

tailSub :: Sub a (t:g) g' -> Sub a g g'
tailSub (Cons _ s) = s
-- no need for tailSub Nil, cannot happen

-- identity substitution, leaves all variables alone
nilSub :: forall a g. (SubstDB a, IncI g) => Sub a g g
nilSub = case axiom1 @g of
    Refl -> go (incBy @g) Nil


-- increment everything by 1
weakSub :: (SubstDB a, IncI g) => Sub a g (t:g)
weakSub = tailSub nilSub

-- singleton, replace 0 with t, leave everything
-- else alone
singleSub :: (SubstDB a, IncI g) => a g t -> Sub a (t:g) g
singleSub t = t `consSub` nilSub

consSub :: a g' t -> Sub a g g' -> Sub a (t:g) g'
consSub = Cons

-- General class for terms that support substitution
class SubstDB a where
   -- variable data constructor
   var   :: Idx g t -> a g t
   -- term traversal
   subst :: IncI g' => Sub a g g' -> a g t -> a g' t


-- Used in substitution when going under a binder
lift :: (SubstDB a, IncI g') => Sub a g g' -> Sub a (t:g) (t:g')
lift s = var Z `Cons` (s `composeSub` weakSub)

composeSub :: forall a g1 g2 g3.
  (IncI g3, SubstDB a) => Sub a g1 g2 -> Sub a g2 g3 -> Sub a g1 g3
composeSub (Cons x s1') s2 = Cons (subst s2 x) (composeSub s1' s2)
composeSub Nil          s2 = s2 
