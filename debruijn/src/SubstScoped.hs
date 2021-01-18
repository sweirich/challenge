-- | Indexing the substitution by a scope, i.e. binding depth
module SubstScoped where

import Imports
import Nat 

import qualified Control.Category as C

-- In this file, we will call Nats "Scopes". I.e. they 
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

-- | A substitution 
-- The parameter 'a' is scope-indexed (i.e. the type 
-- describes the number of free variables allowed to 
-- appear in the term.)
-- Substitution takes terms from scope n to scope m 
data Sub (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
    Id    :: Sub a n n                              --  identity substitution
    (:<)  :: a m -> Sub a n m -> Sub a (S n) m      --  extend a substitution (like cons)
    Lift  :: Sub a n m -> Sub a (S n) (S m)         --  Used in Substitution when going under a binder

infixr :<     -- like usual cons operator (:)

comp :: SubstDB a => Sub a n m -> Sub a m p -> Sub a n p
comp Id          s2         = s2
comp (tm :< s1)  s2         = subst s2 tm :< comp s1 s2
comp (Lift s1)   Id         = Lift s1
comp (Lift s1)   (tm :< s2) = tm :< comp s1 s2
comp (Lift s1)   (Lift s2)  = Lift (comp s1 s2)

-- s1 :<> Id           = s1
-- s1 :<> (tm :< s2)   = subst s1 tm :< (s1 :<> s2)
-- Id :<> Lift s       = Lift s
-- (tm :< s1) :<> s2   = tm :< (s1 :<> s2)
-- Lift s1 :<> Lift s2 = Lift undefined


instance SubstDB a => C.Category (Sub a) where
    id  = nilSub
    (.) = flip comp

-- | Identity substitution, leaves all variables alone
nilSub :: Sub a n n 
nilSub = Id

-- | Increment, shifts all variables by one
-- weakSub :: Sub a n (S n)
-- weakSub = Inc (SS SZ)

-- | Singleton, replace 0 with t, leave everything else alone
singleSub :: a n -> Sub a (S n) n
singleSub t = t :< nilSub

-- | A renaming
type Rename n m = Idx n -> Idx m

-- | General class for terms that support substitution
-- The var construction must bound the index by the scope for the term
-- The subst operation changes the scope of an expression
class SubstDB (a :: Nat -> Type) where
   var    :: Idx n -> a n
   subst  :: Sub a n m -> a n -> a m
   rename :: Rename n m -> a n -> a m

add :: Sing m -> Idx n -> Idx (Plus m n)
add SZ x = x
add (SS m) x = FS (add m x)

-- | Value of the index x in the substitution s
applySub :: SubstDB a => Sub a n m -> Idx n -> a m
applySub Id         x      = var x
applySub (ty :< s)  FZ     = ty
applySub (ty :< s)  (FS x) = applySub s x
applySub (Lift s)   FZ     = var FZ
applySub (Lift s)   (FS x) = rename FS (applySub s x)


liftRename :: Rename n m -> Rename (S n) (S m)
liftRename f FZ     = FZ
liftRename f (FS x) = FS (f x)

-- | Used in a substitution when going under a binder
lift :: SubstDB a => Sub a n m -> Sub a (S n) (S m)
lift = Lift
