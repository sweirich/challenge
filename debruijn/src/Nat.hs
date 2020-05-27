{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -Wno-redundant-constraints #-}
-- | A simple module of natural numbers (with associated singletons)
module Nat (
  -- * Nat type, its singleton, and symbols
  Nat(..),SNat(..),SSym0,ZSym0,Sing(..),

  -- * standard arithmetic (+),(-),(*)
  plus,Plus(..),sPlus,PlusSym0,
  mul,Mul(..),sMul,MulSym0,
  minus,Minus(..),sMinus,MinusSym0,

  -- * list operations 
  length,Length(..),sLength,LengthSym0,
  
  -- unsafe indexing
  (!!), type (!!), (%!!), type (!!@#@$),

  -- safe indexing
  indx, Indx, sIndx, IndxSym0,


) where

import Prelude hiding ((!!), take, drop, length)
import Imports hiding (length, Length, sLength, LengthSym0)
import Test.QuickCheck((==>),Property,Arbitrary(..),oneof)

$(singletons [d|
    data Nat = Z | S Nat deriving (Eq,Ord)

    plus :: Nat -> Nat -> Nat
    plus Z     x = x
    plus (S y) x  = S (plus y x)

    mul :: Nat -> Nat -> Nat
    mul Z     x = Z
    mul (S y) x = plus x (mul y x)

    minus :: Nat -> Nat -> Nat
    minus x     Z = x
    minus (S x) (S y) = minus x y

    length :: [a] -> Nat
    length [] = Z
    length (_:xs) = S (length xs)

    (!!)                :: [a] -> Nat -> a
    []     !! _         =  error "Data.Singletons.List.!!: index too large"
    (x:xs) !! Z         =  x
    (x:xs) !! (S n)     =  xs !! n
    infixl 9 !!

    indx :: [a] -> Nat -> Maybe a
    indx (x:_)  Z     = Just x
    indx (_:xs)(S n)  = indx xs n
    indx []    n      = Nothing
    
    |])

instance Num Nat where
  fromInteger 0 = Z
  fromInteger n | n < 0 = error "Cannot represent negative numbers"
  fromInteger n = S (fromInteger (n - 1))

  (+) = plus
  (*) = mul
  (-) = minus

  negate x = error "negate: Nat cannot represent negative numbers"
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

instance Arbitrary Nat where
  arbitrary = oneof [ return Z, S <$> arbitrary ]
  shrink Z     = []
  shrink (S n) = [n]