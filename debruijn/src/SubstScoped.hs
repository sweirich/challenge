-- | Indexing the substitution by a scope, i.e. binding depth
{-# LANGUAGE TemplateHaskell #-}
module SubstScoped where

import Imports
import Nat

import Control.Monad.Trans.Class
import Data.Singletons.TH
import Data.Singletons.TH.Options


-- In this file, we will call Nats "Scopes". I.e. they 
-- are used to describe the number of free variables allowed in 
-- a term.    

$(withOptions defaultOptions{genSingKindInsts = False} $
  singletons $ lift [d|
  
     data Idx :: Nat -> Type where
         FZ :: Idx (S n)
         FS :: Idx n -> Idx (S n)

     instance Eq (Idx n) where
         FZ == FZ = True
         (FS n) == (FS m) = n == m
         _ == _ = False

     -- A substitution 
     -- The parameter 'a' is scope-indexed (i.e. the type 
     -- describes the number of free variables allowed to 
     -- appear in the term.)
     -- Substitution takes terms from scope n to scope m 
     data Sub (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
         Inc   :: Sing m -> Sub a n (Plus m n)          
         (:<)  :: a m -> Sub a n m -> Sub a (S n) m     
         (:<>) :: Sub a m n -> Sub a n p -> Sub a m p   

     infixr :<     -- like usual cons operator (:)
     infixr :<>    -- like usual composition  (.)

     --  Identity substitution, leaves all variables alone
     nilSub :: Sub a n n 
     nilSub = Inc SZ

     -- Increment, shifts all variables by one
     incSub :: Sub a n (S n)
     incSub = Inc (SS SZ)

     -- Singleton, replace 0 with t, leave everything else alone
     singleSub :: a n -> Sub a (S n) n
     singleSub t = t :< nilSub

     -- General class for terms that support substitution
     -- The var construction must bound the index by the scope for the term
     -- The subst operation changes the scope of an expression
     class SubstDB (a :: Nat -> Type) where
        var   :: Idx n -> a n
        subst :: Sub a n m -> a n -> a m

     add :: Sing m -> Idx n -> Idx (Plus m n)
     add SZ x = x
     add (SS m) x = FS (add m x)

     -- Value of the index x in the substitution s
     applySub :: SubstDB a => Sub a n m -> Idx n -> a m
     applySub (Inc m)        x  = var (add m x)
     applySub (ty :< s)     FZ  = ty
     applySub (ty :< s)  (FS x) = applySub s x
     applySub (s1 :<> s2)    x  = subst s2 (applySub s1 x)

     -- Used in a substitution when going under a binder
     lift :: SubstDB a => Sub a n m -> Sub a (S n) (S m)
     lift s = var FZ :< (s :<> incSub)
  |])


instance Show (Idx n) where
   show FZ = "FZ"
   show (FS n) = "(FS " ++ show n ++ ")"











