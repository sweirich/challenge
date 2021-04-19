module SubstTyped where

import qualified Nat (Nat(..),SNat(..),Length,length,LengthSym0)
import Imports
import qualified Control.Category as C

-- | Variable reference in a context
-- This type is isomorphic to the natural numbers
data Idx (g :: [k]) (t::k) :: Type where
  Z :: Idx (t:g) t
  S :: Idx g t -> Idx (u:g) t

-- | convert to int
idxToInt :: Idx g t -> Int
idxToInt Z = 0
idxToInt (S m) = 1 + idxToInt m


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
   Id    :: Sub a g g                                     -- identity substitution
   (:<)  :: a g' t -> Sub a g g' -> Sub a (t:g) g'        --  extend a substitution (like cons)
   Lift  :: Sub a n m -> Sub a (t:n) (t:m)         --  Used in Substitution when going under a binder


nilSub :: Sub a g g 
nilSub = Id

-- weakSub :: forall t a g. Sub a g (t:g)
-- weakSub = Inc (IS IZ)

infixr :<    -- like usual cons operator (:)

comp :: SubstDB a => Sub a n m -> Sub a m p -> Sub a n p
comp Id          s2         = s2
comp (tm :< s1)  s2         = subst s2 tm :< comp s1 s2
comp (Lift s1)   Id         = Lift s1
comp (Lift s1)   (tm :< s2) = tm :< comp s1 s2
comp (Lift s1)   (Lift s2)  = Lift (comp s1 s2)



instance SubstDB a => C.Category (Sub (a :: [k] -> k -> Type)) where
    id = nilSub
    (.) = flip comp

add :: IncBy g1 -> Idx g t -> Idx (g1 ++ g) t
add IZ i = i
add (IS xs) i = S (add xs i)

-- | Type preserving renaming
--
-- In fact, only renaming used are
-- weakening (S) and lifts (liftRename)
type Rename g g' = forall t. Idx g t -> Idx g' t

liftRename :: Rename g g' -> Rename (t:g) (t:g')
liftRename f Z     = Z
liftRename f (S x) = S (f x)

class SubstDB (a :: [k] -> k -> Type) where
   var    :: Idx g t -> a g t
   subst  :: Sub a g g' -> a g t -> a g' t
   rename :: Rename g g' -> a g t -> a g' t

-- | Value of the index x in the substitution s
applySub :: SubstDB a => Sub a g g' -> Idx g t -> a g' t
applySub Id         x     = var x
applySub (ty :< _)  Z     = ty
applySub (_  :< s)  (S x) = applySub s x
applySub (Lift s)   Z     = var Z
applySub (Lift s)   (S x) = rename S (applySub s x)

-- | An alternative to 'applySub' which (always) renames once.
applySub' :: SubstDB a => Sub a g g' -> Idx g t -> a g' t
applySub' = go id where
    go :: SubstDB a => Rename g' g'' -> Sub a g g' -> Idx g t -> a g'' t
    go r Id        x     = var (r x)
    go r (ty :< _) Z     = rename r ty
    go r (_  :< s) (S x) = go r s x
    go r (Lift s)  Z     = var (r Z)
    go r (Lift s)  (S x) = go (r . S) s x

singleSub :: a g t -> Sub a (t:g) g
singleSub t = t :< nilSub

lift :: SubstDB a => Sub a g g' -> Sub a (t:g) (t:g')
lift = Lift

mapIdx :: forall s g t. Idx g t -> Idx (Map s g) (Apply s t)
mapIdx Z = Z
mapIdx (S n) = S (mapIdx @s n)

mapInc :: forall s g. IncBy g -> IncBy (Map s g)
mapInc IZ = IZ
mapInc (IS n) = IS (mapInc @s n)

-- exchange is renaming.
-- Should Sub have renaming constructor?
--
-- exchange :: forall t1 t2 a g. SubstDB a => Sub a (t1:t2:g) (t2:t1:g)
-- exchange = var (S Z) :< var Z :< Inc (IS (IS IZ))



