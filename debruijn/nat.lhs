\begin{code}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns -Wno-redundant-constraints #-}
module Nat where

import Prelude hiding ((!!),(>>), take, drop, length)
import Data.Singletons
import Data.Singletons.Prelude
   hiding (Drop,Take,Length,
          sDrop,sTake,sLength,
          DropSym0,DropSym1,DropSym2,
          TakeSym0,TakeSym1,TakeSym2)
import Data.Singletons.TH
   hiding (Drop,Take,Length,
          sDrop,sTake,sLength,
          DropSym0,DropSym1,DropSym2,
          TakeSym0,TakeSym1,TakeSym2)

import Data.Kind(Type)

import Data.Type.Equality
import Test.QuickCheck((==>))

import Unsafe.Coerce(unsafeCoerce)

$(singletons [d|
    data Nat = Z | S Nat deriving (Eq, Ord)

    plus :: Nat -> Nat -> Nat
    plus Z     x = x
    plus (S y) x  = S (plus y x)

    mul :: Nat -> Nat -> Nat
    mul Z     x = Z
    mul (S y) x = plus x (mul y x)

    minus :: Nat -> Nat -> Nat
    minus x     Z = x
    minus (S x) (S y) = minus x y

    applyN :: Nat -> (a -> a) -> a -> a
    applyN Z     f x = x
    applyN (S n) f x = f (applyN n f x)

    idx :: [a] -> Nat -> Maybe a
    idx (x:_)  Z     = Just x
    idx (_:xs)(S n)  = idx xs n
    idx []    n      = Nothing


    length :: [a] -> Nat
    length [] = Z
    length (_:xs) = S (length xs)

    take :: Nat -> [a] -> [a]
    take Z     xs      = []
    take (S n) (x:xs)  = (x:take n xs)
    take n     []      = [] 
                            
    drop :: Nat -> [a] -> [a]
    drop Z xs          = xs
    drop (S n) (_:xs)  = drop n xs
    drop n     []      = []                           
 
    |])

type a + b = Plus a b
type a - b = Minus a b
--type a * b = Mul a b

instance Num Nat where
  fromInteger 0 = Z
  fromInteger n | n < 0 = error "Cannot represent negative numbers"
  fromInteger n = S (fromInteger (n - 1))

  (+) = plus
  (*) = mul
  (-) = minus

  negate x = error "Negative number"
  abs x    = x
  signum Z = 0
  signum x = 1

instance Enum Nat where
  toEnum :: Int -> Nat
  toEnum = fromInteger . toInteger
  fromEnum :: Nat -> Int
  fromEnum = natToInt

natToInt :: Nat -> Int
natToInt Z = 0
natToInt (S m) = 1 + natToInt m

instance Show Nat where
  show = show . natToInt

class Index a where
  type Element a
  (!!) :: a -> Nat -> Element a

instance Index [a] where
  type Element [a] = a
  (x:_)   !!  Z     = x
  (_:xs)  !! (S n)  = xs !! n
  []      !! n      = error "(!!): too few elements in index"

------------------------------------------------------





------------------------------------------------------

prop_natLength_take k xs =
  k <= length xs ==>
  length (take k xs) == k

ax_Length_Take :: forall k xs.
  ((k <= Length xs) ~ True) => Length (Take k xs) :~: k
ax_Length_Take = unsafeCoerce Refl

-- Can't do the proof without knowing the definition
-- of <= 
proof_Length_Pred :: forall k x xs.
  Sing k -> Sing xs ->
  ((S k <= Length (x ': xs)) ~ True) =>
     (k <= Length xs) :~: True
proof_Length_Pred = undefined
-- UGH another example of error if present, warning if missing
--proof_Length_Pred (SS j) SNil = undefined
  
proof_Length_Take :: forall k xs.
  ((k <= Length xs) ~ True) =>
  Sing k -> Sing xs -> Length (Take k xs) :~: k
proof_Length_Take SZ SNil = Refl
proof_Length_Take SZ (SCons x ys) = Refl
proof_Length_Take (SS n) (SCons x ys) 
  | Refl <- proof_Length_Pred n ys
  , Refl <- proof_Length_Take n ys
  = Refl

\end{code}
