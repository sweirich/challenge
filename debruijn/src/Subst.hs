 {-# LANGUAGE TemplateHaskell #-}
module Subst where

import Imports
import GHC.Exts

$(singletons [d|

    -- An index: (i.e. just a natural number)
    data Idx where
       Z :: Idx
       S :: Idx -> Idx
        deriving (Eq, Show)

    -- Access a list element by its index
    -- Fails if the index is longer than the length of the list
    indx :: [a] -> Idx -> Maybe a
    indx [] Z = Nothing
    indx (x:xs) Z = Just x
    indx (x:xs) (S n)= indx xs n

   -- A substitution Algebra
    data Sub a =
       IdS                  --  identity subst
     | Inc                  --  increment by 1 (shift)                
     | a :· Sub a           --  extend a substitution (like cons)
     | Sub a :<> Sub a      --  compose substitutions
            deriving (Eq, Show, Functor) 

    infixr :·     -- like usual cons operator (:)
    infixr :<>    -- like usual composition  (.)
 
    class SubstC a where
       var   :: Idx -> a 
       subst :: Sub a -> a -> a

    

    --  Value of the index x in the substitution s
    applyS :: SubstC a => Sub a -> Idx -> a
    applyS IdS            x  = var x
    applyS Inc            x  = var (S x)
    applyS (ty :· s)      Z  = ty
    applyS (ty :· s)   (S x) = applyS s x
    applyS (s1 :<> s2)    x  = subst s2 (applyS s1 x)
 
    singleSub :: a -> Sub a
    singleSub t = t :· IdS

    lift :: SubstC a => Sub a -> Sub a
    lift s = var Z :· (s :<> Inc)
 
    substList :: SubstC a => Sub a -> [a] -> [a]
    substList s = map (subst s)
    --substList s [] = []
    --substList s (t:g) = subst s t : substList s g
 
    incList :: SubstC a => [a] -> [a]
    incList = substList Inc
 
    liftList :: SubstC a => Sub a -> [a] -> [a]
    liftList s = substList (lift s)

    --fromList :: [a] -> Sub a
    --fromList = foldr (:·) IdS

 |])


{- NOTE: optimization for above. Won't do it now.
applyS s x | Just f <- isIncN s = var (f x)
isIncN :: Sub a -> Maybe (Nat -> Nat)
isIncN IdS        = Just id
isIncN (Inc :∘ s) = (S .) <$> isIncN s
isIncN _          = Nothing

$(singletons [d|
    liftN :: SubstC a => Nat -> Sub a -> Sub a
    liftN k s = upTo k (s :∘ incN k)
 
    incN :: SubstC a => Nat -> Sub a
    incN Z = IdS
    incN (S n) = (Inc :∘ incN n)

    upTo :: SubstC a => Nat -> Sub a -> Sub a
    upTo Z s     = s
    upTo (S m) s = upTo m (var m :· s)
  |])

-}