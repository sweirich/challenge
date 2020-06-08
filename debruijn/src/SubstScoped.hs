-- | Indexing the substitution by a scope, i.e. binding depth
module SubstScoped where

import Imports
import Nat 

-- In this file, we will call nats "Scopes". I.e. they 
-- are used to describe the number of free variables allowed in 
-- a term.    


-- | An "indexed" index: (still isomorphic to a natural number)
-- The index is valid in a certain "scope" i.e. must be bounded.
-- (This type is often called Fin.)
data Idx :: Nat -> Type where
    FZ :: Idx (S n)
    FS :: Idx n -> Idx (S n)

instance Eq (Idx n) where
    FZ == FZ = True
    (FS n) == (FS m) = n == m
    _ == _ = False

instance Show (Idx n) where
    show FZ = "FZ"
    show (FS n) = "(FS " ++ show n ++ ")"

-- A list indexed by its length
data Vec (n :: Nat) (a :: Type) where
    VNil  :: Vec Z a
    VCons :: a -> Vec n a -> Vec (S n) a

-- Access a list element by its index
-- Never fails because we know the index will be
-- in range.
index :: Vec n a -> Idx n -> a
index v FZ = case v of 
    (VCons x _) -> x
index v (FS n) = case v of 
    (VCons _ xs) -> index xs n

-- A substitution Algebra
-- The parameter 'a' is scope-indexed (i.e. the type 
-- describes the number of free variables allowed to 
-- appear in the term.)
-- Substitution takes terms from scope n to scope m 
data Sub (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
--    IdS   :: Sub a n n                             --  identity subst
    Inc   :: Sing m -> Sub a n (Plus m n)               --  increment by 1 (shift)                
    (:<)  :: a m -> Sub a n m -> Sub a (S n) m       --  extend a substitution (like cons)
    (:<>) :: Sub a m n -> Sub a n p -> Sub a m p     --  compose substitutions

infixr :<     -- like usual cons operator (:)
infixr :<>    -- like usual composition  (.)

nilSub :: Sub a n n 
nilSub = Inc SZ

incSub :: Sub a n (S n)
incSub = Inc (SS SZ)

-- The var construction must bound the index by the scope
-- for the term
class SubstC (a :: Nat -> Type) where
   var   :: Idx n -> a n
   subst :: Sub a n m -> a n -> a m

add :: Sing m -> Idx n -> Idx (Plus m n)
add SZ x = x
add (SS m) x = FS (add m x)

--  Value of the index x in the substitution s
applySub :: SubstC a => Sub a n m -> Idx n -> a m
--applySub IdS            x  = var x
applySub (Inc m)        x  = var (add m x)
applySub (ty :< s)     FZ  = ty
applySub (ty :< s)  (FS x) = applySub s x
applySub (s1 :<> s2)    x  = subst s2 (applySub s1 x)

singleSub :: a n -> Sub a (S n) n
singleSub t = t :< nilSub

lift :: SubstC a => Sub a n m -> Sub a (S n) (S m)
lift s = var FZ :< (s :<> incSub)














