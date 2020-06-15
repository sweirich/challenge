module SubstTyped where

import qualified Nat (Nat(..),SNat(..),Length,length,LengthSym0)
import Imports
import Unsafe.Coerce

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
-- Never fails, so no need for Maybeß
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

data Sub (a :: ([k] -> k -> Type)) (g :: [k]) (g'::[k]) where
   Inc   :: IncBy g1 -> Sub a g (g1 ++ g)                 --  increment by n (shift)                
   (:<)  :: a g' t -> Sub a g g' -> Sub a (t:g) g'        --  extend a substitution (like cons)
   (:<>) :: Sub a g1 g2 -> Sub a g2 g3 -> Sub a g1 g3 

--nil :: Sub a g g 
nilSub :: forall k (a :: [k] -> k -> Type) (g :: [k]). Sub a g g
nilSub = Inc IZ

--incSub :: forall t a g. Sub a g (t:g)
incSub :: forall a1 (a2 :: [a1] -> a1 -> Type) (g :: [a1]) (t :: a1). Sub a2 g (t : g)
incSub = Inc (IS IZ)

infixr :<    -- like usual cons operator (:)
infixr :<>   -- like usual composition  (.)

add :: IncBy g1 -> Idx g t -> Idx (g1 ++ g) t
add IZ i = i
add (IS xs) i = S (add xs i)

class SubstDB (a :: [k] -> k -> Type) where
   var   :: Idx g t -> a g t
   subst :: Sub a g g' -> a g t -> a g' t

-- | Value of the index x in the substitution s
applySub :: SubstDB a => Sub a g g' -> Idx g t -> a g' t
applySub (Inc n)       x  = var (add n x)            
applySub (ty :< s)     Z  = ty
applySub (ty :< s)  (S x) = applySub s x
applySub (s1 :<> s2)   x  = subst s2 (applySub s1 x)

singleSub :: a g t -> Sub a (t:g) g
singleSub t = t :< Inc IZ

lift :: SubstDB a => Sub a g g' -> Sub a (t:g) (t:g')
lift s = var Z :< (s :<> Inc (IS IZ))

mapIdx :: forall s g t. Idx g t -> Idx (Map s g) (Apply s t)
mapIdx Z = Z
mapIdx (S n) = S (mapIdx @s n)

mapInc :: forall s g. IncBy g -> IncBy (Map s g)
mapInc IZ = IZ
mapInc (IS n) = IS (mapInc @s n)


exchange :: forall t1 t2 a g. SubstDB a => Sub a (t1:t2:g) (t2:t1:g)
exchange = var (S Z) :< var Z :< Inc (IS (IS IZ))



