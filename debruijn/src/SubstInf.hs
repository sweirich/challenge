-- This is an alternative implementation of the 'Subst' interface that
-- implements Sub using a lazy list.  Applying the substitution is looking
-- up the definition at a particular place in that list.

{-# LANGUAGE TemplateHaskell #-}
module SubstInf
  (
   Sub,      
   Idx,      
   applySub,  
   nilSub,    
   weakSub,   
   singleSub, 
   lift,      

   ) where

import Nat
import Imports

-- | An index
type Idx = Nat

-- | A substitution, infinite list of terms
newtype Sub a = Sub [a]

-- | General class for terms that support substitution
class SubstDB a where
   -- variable data constructor
   var   :: Idx -> a 
   -- term traversal
   subst :: Sub a -> a -> a

-- | lookup the term at a particular index
applySub :: Sub a -> Idx -> a
applySub (Sub s) i = s Nat.!! i

-- | identity substitution, leaves all variables alone
nilSub :: SubstDB a => Sub a 
nilSub =  Sub $ var <$> [Z ..]

-- | compose two substitutions together
composeSub :: SubstDB a => Sub a -> Sub a -> Sub a
composeSub (Sub s1) s2 = Sub $ map (subst s2) s1


-- | Used in substitution when going under a binder
lift :: SubstDB a => Sub a -> Sub a
lift s = var Z `consSub` (s `composeSub` weakSub)



-- | singleton, replace 0 with t, leave everything
-- else alone
singleSub :: SubstDB a => a -> Sub a
singleSub t = t `consSub` nilSub

-- | increment everything by 1
weakSub :: SubstDB a => Sub a 
weakSub = tailSub nilSub


consSub :: a -> Sub a -> Sub a
consSub x (Sub s) = Sub $ x:s

tailSub :: Sub a -> Sub a
tailSub (Sub s) = Sub $ tail s

