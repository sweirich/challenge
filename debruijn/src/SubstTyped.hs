
module SubstTyped where

import qualified Nat (Nat(..),SNat(..),Length,length,LengthSym0)
import Imports

-- | Variable reference in a context
-- This type is isomorphic to the natural numbers
data Idx g t where
  Z :: Idx (t:g) t
  S :: Idx g t -> Idx (u:g) t

-- | "Environment" heterogenous list
-- indexed by a list 

data Env (g :: [k]) where
  Nil  :: Env '[]
  Cons :: t -> Env g -> Env (t:g)


-- Access a list element by its index
-- Never fails, so no need for Maybe
indx :: Env g -> Idx g t -> t
indx g Z = case g of 
   (Cons x xs) -> x
indx g (S n) = case g of 
   (Cons x xs) -> indx xs n

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
   (:>)  :: a g' t -> Sub a g g' -> Sub a (t:g) g'        --  extend a substitution (like cons)
   (:<>) :: Sub a g1 g2 -> Sub a g2 g3 -> Sub a g1 g3 

idSub :: Sub a g g 
idSub = Inc IZ

incSub :: forall t a g. Sub a g (t:g)
incSub = Inc (IS IZ)

infixr :>    -- like usual cons operator (:)
infixr :<>   -- like usual composition  (.)

add :: IncBy g1 -> Idx g t -> Idx (g1 ++ g) t
add IZ i = i
add (IS xs) i = S (add xs i)

class SubstC (a :: [k] -> k -> Type) where
   var   :: Idx g t -> a g t
   subst :: Sub a g g' -> a g t -> a g' t

-- | Value of the index x in the substitution s
applyS :: SubstC a => Sub a g g' -> Idx g t -> a g' t
--applyS IdS           x  = var x
applyS (Inc n)       x  = var (add n x)            
applyS (ty :> s)     Z  = ty
applyS (ty :> s)  (S x) = applyS s x
applyS (s1 :<> s2)   x  = subst s2 (applyS s1 x)

singleSub :: a g t -> Sub a (t:g) g
singleSub t = t :> Inc IZ

lift :: SubstC a => Sub a g g' -> Sub a (t:g) (t:g')
lift s = var Z :> (s :<> Inc (IS IZ))

mapIdx :: forall s g t. Idx g t -> Idx (Map s g) (Apply s t)
mapIdx Z = Z
mapIdx (S n) = S (mapIdx @s n)

mapInc :: forall s g t. IncBy g -> IncBy (Map s g)
mapInc IZ = IZ
mapInc (IS n) = IS (mapInc @s n)

-- A general purpose transformation of a substitution
-- This is way to weedy for the talk, but it does mean that 
-- the implementation details of sub need to leak in to PolyTyped
{-
class SubTrans (a :: [k] -> k -> Type) tag where
   type Sym tag :: k ~> k 
   fg :: forall g. Sing tag -> Sing g -> Sing (Map (Sym tag) g)
   f :: Sing tag -> a g t -> a (Map (Sym tag) g) (Apply (Sym tag) t)

mapSub :: forall tag a g g'. (SubTrans a tag) => Sing tag ->
       Sub a g g' -> Sub a (Map (Sym tag) g) (Map (Sym tag) g')
mapSub tag (Inc s1) 
  | Refl <- lemma @g' @g @tag   = Inc (fg tag s1)
mapSub tag (e :> s1)   = f tag e :> mapSub tag s1
mapSub tag (s1 :<> s2) = mapSub tag s1 :<> mapSub tag s2

lemma :: forall g g1 tag. Map (Sym tag) g1 ++ Map (Sym tag) g :~: Map (Sym tag) (g1 ++ g)
lemma = undefined
-}




