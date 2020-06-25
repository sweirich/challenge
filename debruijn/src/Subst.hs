 {-# LANGUAGE TemplateHaskell #-}
module Subst
  (type Idx,
   type Nat(..), type SNat(..),  ZSym0, SSym0,
   type Sub(..), type SSub(..),

   applySub,  type ApplySub,  sApplySub,  ApplySubSym0,  ApplySubSym1,
   nilSub,    type NilSub,    sNilSub,    NilSubSym0, 
   weakSub,   type WeakSub,   sWeakSub,   WeakSubSym0,
   singleSub, type SingleSub, sSingleSub, SingleSubSym0, SingleSubSym1,
   lift,      type Lift,      sLift,      LiftSym0,      LiftSym1,

   SubstDB(..),PSubstDB(..),SSubstDB(..),
   VarSym0, SubstSym0, SubstSym1,

   ) where

import Nat
import Imports

$(singletons [d|

    -- An index: (i.e. just a natural number)
    type Idx = Nat

   -- A substitution (represented by a datatype)
    data Sub a =
       Inc Idx              --  increment by an index amount                
     | a :< Sub a           --  extend a substitution (like cons)
     | Sub a :<> Sub a      --  compose substitutions
        deriving (Eq, Show, Functor) 

    infixr :<     -- like usual cons operator (:)
    infixr :<>    -- like usual composition  (.)
 
   --  Value of the index x in the substitution
    applySub :: SubstDB a => Sub a -> Idx -> a
    applySub (Inc k)        x  = var (plus k x)
    applySub (ty :< s)      Z  = ty
    applySub (ty :< s)   (S x) = applySub s x
    applySub (s1 :<> s2)    x  = subst s2 (applySub s1 x)


    -- identity substitution, leaves all variables alone
    nilSub :: Sub a 
    nilSub = Inc Z

    -- increment, shifts all variables by one
    weakSub :: Sub a 
    weakSub = Inc (S Z) 

    -- singleton, replace 0 with t, leave everything
    -- else alone
    singleSub :: a -> Sub a
    singleSub t = t :< nilSub

    -- General class for terms that support substitution
    class SubstDB a where
       -- variable data constructor
       var   :: Idx -> a 
       -- term traversal
       subst :: Sub a -> a -> a

    
    -- Used in substitution when going under a binder
    lift :: SubstDB a => Sub a -> Sub a
    lift s = var Z :< (s :<> weakSub)


 |])

-- | Note, the <> for this Sub
-- is in different order than Category's . for SubstTyped or SubstScoped,
instance Semigroup (Sub a) where
  (<>)   = (:<>)
instance Monoid (Sub a) where
  mempty = nilSub
