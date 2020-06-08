-- | Typed version of the de Bruijn substiution infrastructure
-- This version makes two optimizations:
--   1. It suspends substiutions at binders (hidden behind a new abstract type)
--   2. When two subs meet at binder, it combines them with a "smart constructor" for composition
module SubstTypedOpt(
   -- * -- Abstract type for binding locations
   Bind, bind, unbind, instantiate, substBind,
   -- * -- Substitution class & constructors
   Idx(..), Sub(..), IncBy(..), SubstC(..), 
   nilSub, incSub, single, comp, 
   applySub, mapIdx, mapInc, addBy, singIndx
 ) where

import qualified Nat (Nat(..),SNat(..),Length,length,LengthSym0)
import Imports
import Unsafe.Coerce(unsafeCoerce)

-- Binding type ---------

-- morally "a (t1:g) t2"
-- but may also contain a hidden suspended substitution
data Bind a t1 g t2 = forall g'. Bind (Sub a g' (t1:g)) (a g' t2)

-- introdue a binder
bind :: SubstC a => a (t1:g) t2 -> Bind a t1 g t2
bind = Bind (Inc IZ)
{-# INLINABLE bind #-}

-- expose the body of the binder
unbind :: SubstC a => Bind a t1 g t2 -> a (t1:g) t2
unbind (Bind s a) = subst s a
{-# INLINABLE unbind #-}

-- replace the variable bound at the binder
instantiate :: SubstC a => Bind a t1 g t2 -> a g t1 -> a g t2
instantiate (Bind s a) b = subst (comp s (single b)) a
{-# INLINABLE instantiate #-}

-- apply a substitution to a binder
substBind :: SubstC a => Sub a g1 g2 -> Bind a t1 g1 t2 -> Bind a t1 g2 t2
substBind s2 (Bind s1 e) = Bind (comp s1 (lift s2)) e
{-# INLINABLE substBind #-}

-- Substitution infrastructure ----------------

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
   Inc   :: IncBy g1 -> Sub a g (g1 ++ g)                 --  weaken the context (shifting all variables over)                
   (:<)  :: a g' t -> Sub a g g' -> Sub a (t:g) g'        --  extend a substitution (like cons)
   (:<>) :: Sub a g1 g2 -> Sub a g2 g3 -> Sub a g1 g3 

-- | Identity substitution
nilSub :: Sub a g g 
nilSub = Inc IZ

-- | Weaken
incSub :: forall t a g. Sub a g (t:g)
incSub = Inc (IS IZ)

-- | single substitution for index 0
single :: a g t -> Sub a (t:g) g
single t = t :< nilSub

infixr :<    -- like usual cons operator (:)
infixr :<>   -- like usual composition  (.)

-- | weaken an index
add :: IncBy g1 -> Idx g t -> Idx (g1 ++ g) t
add IZ i = i
add (IS xs) i = S (add xs i)

class SubstC (a :: [k] -> k -> Type) where
   var   :: Idx g t -> a g t
   subst :: Sub a g g' -> a g t -> a g' t

-- | Value of the index x in the substitution s
applySub :: SubstC a => Sub a g g' -> Idx g t -> a g' t
applySub (Inc n)       x  = var (add n x)            
applySub (ty :< s)     Z  = ty
applySub (ty :< s)  (S x) = applySub s x
applySub (s1 :<> s2)   x  = subst s2 (applySub s1 x)

--singleSub :: a g t -> Sub a (t:g) g
singleSub t = t :< Inc IZ

--lift :: SubstC a => Sub a g g' -> Sub a (t:g) (t:g')
lift s = var Z :< (s :<> Inc (IS IZ))

mapIdx :: forall s g t. Idx g t -> Idx (Map s g) (Apply s t)
mapIdx Z = Z
mapIdx (S n) = S (mapIdx @s n)

mapInc :: forall s g t. IncBy g -> IncBy (Map s g)
mapInc IZ = IZ
mapInc (IS n) = IS (mapInc @s n)


exchange :: forall t1 t2 a g. SubstC a => Sub a (t1:t2:g) (t2:t1:g)
exchange = var (S Z) :< var Z :< Inc (IS (IS IZ))

addBy :: IncBy g1 -> IncBy g2 -> IncBy (g1 ++ g2) 
addBy IZ      i = i
addBy (IS xs) i = IS (addBy xs i)

comp :: SubstC a => Sub a g1 g2 -> Sub a g2 g3 -> Sub a g1 g3 
-- comp (Inc (k1 :: IncBy g1)) (Inc (k2 :: IncBy g2)) 
--  | Refl <- assoc @g1 @g2  = Inc (addBy k1 k2)
comp (Inc IZ) s       = s
comp (Inc (IS n)) (t :< s) = comp (Inc n) s
comp s (Inc IZ)   = s
comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
comp (t :< s1) s2 = subst s2 t :< comp s1 s2
comp s1 s2 = s1 :<> s2

-- assoc :: forall g1 g2 g3. g1 ++ (g2 ++ g3) :~: (g1 ++ g2) ++ g3
-- assoc = unsafeCoerce Refl