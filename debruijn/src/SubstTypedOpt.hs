-- | Typed version of the de Bruijn substiution infrastructure
-- This version makes two major optimizations:
--   1. It suspends substiutions at binders (hidden behind a new abstract type)
--   2. When two subs meet at binder, it combines them with a "smart constructor" for composition

module SubstTypedOpt(
   -- * -- Abstract type for binding locations
   Bind, bind, unbind, instantiate, substBind,
   
   -- * -- Substitution class & constructors
   Idx(..), Sub(..), IncBy(..), SubstDB(..), 
   nilSub, incSub, singleSub, comp, 
   applySub, mapIdx, mapInc, addBy, 
 ) where

import qualified Nat (Nat(..),SNat(..),Length,length,LengthSym0)
import Imports


-- 'Bind' type ---------

-- | When defining an AST, use this type in the data type definition
-- to indicate the binding location of a variable.
-- Morally this type is equivalent to "a (t1:g) t2", i.e. an 'a' of type
-- t2 where the context 'g' has been extended with variable t1
data Bind a t1 g t2 = forall g'. Bind (Sub a g' (t1:g)) (a g' t2)

-- | introduce a binder
bind :: SubstDB a => a (t1:g) t2 -> Bind a t1 g t2
bind = Bind (Inc IZ)
{-# INLINABLE bind #-}

-- | expose the body of the binder
unbind :: SubstDB a => Bind a t1 g t2 -> a (t1:g) t2
unbind (Bind s a) = subst s a
{-# INLINABLE unbind #-}

-- | replace the variable bound at the binder with a term
instantiate :: SubstDB a => Bind a t1 g t2 -> a g t1 -> a g t2
instantiate (Bind s a) b = subst (comp s (singleSub b)) a
{-# INLINABLE instantiate #-}

-- | substitute through the binder
substBind :: SubstDB a => Sub a g1 g2 -> Bind a t1 g1 t2 -> Bind a t1 g2 t2
substBind s2 (Bind s1 e) = Bind (comp s1 (lift s2)) e
{-# INLINABLE substBind #-}

-- Substitution infrastructure ----------------

-- | Variable reference in a context
-- This type is isomorphic to the natural numbers
data Idx (g :: [k]) (t::k) :: Type where
  Z :: Idx (t:g) t
  S :: !(Idx g t) -> Idx (u:g) t

-- For increment, we need a proxy that gives us the type of the extended context, 
-- but is computationally a natural number
data IncBy (g :: [k]) where
   IZ :: IncBy '[]
   IS :: !(IncBy n) -> IncBy (t:n)

data Sub (a :: [k] -> k -> Type) (g :: [k]) (g'::[k]) where
   Inc   :: !(IncBy g1) -> Sub a g (g1 ++ g)                 -- weaken the context (shifting all variables over)                
   (:<)  :: a g' t -> !(Sub a g g') -> Sub a (t:g) g'        -- extend a substitution (like cons)
   (:<>) :: !(Sub a g1 g2) -> !(Sub a g2 g3) -> Sub a g1 g3     -- composition 

-- | Identity substitution
nilSub :: Sub a g g 
nilSub = Inc IZ

-- | Weaken
incSub :: forall t a g. Sub a g (t:g)
incSub = Inc (IS IZ)

-- | Single substitution (for index 0)
singleSub :: a g t -> Sub a (t:g) g
singleSub t = t :< nilSub

infixr :<    -- like usual cons operator (:)
infixr :<>   -- like usual composition  (.)

-- | weaken an index
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

lift :: SubstDB a => Sub a g g' -> Sub a (t:g) (t:g')
lift s = var Z :< (s :<> Inc (IS IZ))

-- | Apply a substitution to the context and type in an Idx
mapIdx :: forall s g t. Idx g t -> Idx (Map s g) (Apply s t)
mapIdx Z = Z
mapIdx (S n) = S (mapIdx @s n)

mapInc :: forall s g t. IncBy g -> IncBy (Map s g)
mapInc IZ = IZ
mapInc (IS n) = IS (mapInc @s n)


exchange :: forall t1 t2 a g. SubstDB a => Sub a (t1:t2:g) (t2:t1:g)
exchange = var (S Z) :< var Z :< Inc (IS (IS IZ))

addBy :: IncBy g1 -> IncBy g2 -> IncBy (g1 ++ g2) 
addBy IZ      i = i
addBy (IS xs) i = IS (addBy xs i)

-- | "smart constructor" for substitution. Performs some optimizations
-- if possible
comp :: SubstDB a => Sub a g1 g2 -> Sub a g2 g3 -> Sub a g1 g3 
comp (Inc IZ) s       = s
comp (Inc (IS n)) (t :< s) = comp (Inc n) s
comp s (Inc IZ)   = s
comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
comp (t :< s1) s2 = subst s2 t :< comp s1 s2
comp s1 s2 = s1 :<> s2

