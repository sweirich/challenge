module SubstTypedFun where

import qualified Nat (Nat(..),SNat(..),Length,length,LengthSym0)
import Imports
import Unsafe.Coerce

import qualified Control.Category as C

-- | Variable reference in a context
-- This type is isomorphic to the natural numbers
data Idx (g :: [k]) (t::k) :: Type where
  Z :: Idx (t:g) t
  S :: Idx g t -> Idx (u:g) t

-- | "Environment" heterogenous list
-- indexed by a list 

data HList (g :: [k]) where
  HNil  :: HList '[]
  HCons :: t -> HList g -> HList (t:g)


-- Access a list element by its index
-- Never fails, so no need for Maybe
indx :: HList g -> Idx g t -> t
indx g Z = case g of 
   (HCons x xs) -> x
indx g (S n) = case g of 
   (HCons x xs) -> indx xs n

-- Access a list of Singletons by its index.
-- Never fails, so no need for Maybe
singIndx :: Sing g -> Idx g t -> Sing t
singIndx g Z = case g of
   (SCons x _) -> x
singIndx g (S n) = case g of 
   (SCons _ xs) -> singIndx xs n


-- For increment, we need a proxy that gives us the type of the extended context, 
-- but is computationally a natural number
data IncBy (g :: [k]) where
   IZ :: IncBy '[]
   IS :: IncBy n -> IncBy (t:n)


-- A substitution is a map from indices to terms
type Sub (a :: ([k] -> k -> Type)) (g :: [k]) (g'::[k]) = forall t. Idx g t -> a g' t

applySub :: Sub a g g' -> Idx g t -> a g' t
applySub s x = s x

nilSub :: forall k (a :: [k] -> k -> Type) (g :: [k]). SubstDB a => Sub a g g
nilSub = var

incSub :: SubstDB a => IncBy g1 -> Sub a g (g1 ++ g)
incSub n x = var (add n x)

consSub :: a g' t -> Sub a g g' -> Sub a (t:g) g'
consSub tm1 _    Z  = tm1
consSub  _  s (S n) = s n 

composeSub :: SubstDB a => Sub a g1 g2 -> Sub a g2 g3 -> Sub a g1 g3
composeSub s1 s2 x = subst s2 (s1 x)

weakSub :: forall a1 (a2 :: [a1] -> a1 -> Type) (g :: [a1]) (t :: a1). SubstDB a2 => Sub a2 g (t : g)
weakSub = incSub (IS IZ)

add :: IncBy g1 -> Idx g t -> Idx (g1 ++ g) t
add IZ i = i
add (IS xs) i = S (add xs i)

class SubstDB (a :: [k] -> k -> Type) where
   var   :: Idx g t -> a g t
   subst :: Sub a g g' -> a g t -> a g' t


singleSub :: SubstDB a => a g t -> Sub a (t:g) g
singleSub t = t `consSub` nilSub

lift :: SubstDB a => Sub a g g' -> Sub a (t:g) (t:g')
lift s = var Z `consSub` (s `composeSub` incSub (IS IZ))

mapIdx :: forall s g t. Idx g t -> Idx (Map s g) (Apply s t)
mapIdx Z = Z
mapIdx (S n) = S (mapIdx @s n)

mapInc :: forall s g. IncBy g -> IncBy (Map s g)
mapInc IZ = IZ
mapInc (IS n) = IS (mapInc @s n)


exchange :: forall t1 t2 a g. SubstDB a => Sub a (t1:t2:g) (t2:t1:g)
exchange = var (S Z) `consSub` ((var Z) `consSub` (incSub (IS (IS IZ))))



