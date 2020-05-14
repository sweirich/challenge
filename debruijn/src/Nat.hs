{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -Wno-redundant-constraints #-}
module Nat (
  -- * Nat type, its singleton, and symbols
  Nat(..),SNat(..),SSym0,ZSym0,

  -- * standard arithmetic (+),(-),(*)
  plus,Plus(..),sPlus,PlusSym0,
  type(+),(%+),type(+@#@$),
  mul,Mul(..),sMul,MulSym0,
  type(*),(%*),type(*@#@$),
  minus,Minus(..),sMinus,MinusSym0,
  type(-),(%-),type(-@#@$),

  -- * list operations 
  length,Length(..),sLength,LengthSym0,
  take,Take(..),sTake,TakeSym0,
  drop,Drop(..),sDrop,DropSym0,

  -- unsafe indexing
  (!!), type (!!), (%!!), type (!!@#@$),

  -- safe indexing
  idx, Idx, sIdx, IdxSym0,

  prop_natLength_take,
  ax_Length_Take,
  proof_Length_Pred,
  proof_Length_Take,

) where

import Prelude hiding ((!!), take, drop, length)
import Imports 

import Test.QuickCheck((==>))
import Unsafe.Coerce(unsafeCoerce)

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

    take :: Nat -> [a] -> [a]
    take Z     xs      = []
    take (S n) (x:xs)  = (x:take n xs)
    take n     []      = [] 
                            
    drop :: Nat -> [a] -> [a]
    drop Z xs          = xs
    drop (S n) (_:xs)  = drop n xs
    drop n     []      = []                           

    (!!)                :: [a] -> Nat -> a
    []     !! _         =  error "Data.Singletons.List.!!: index too large"
    (x:xs) !! Z         =  x
    (x:xs) !! (S n)     =  xs !! n
    infixl 9 !!

    idx :: [a] -> Nat -> Maybe a
    idx (x:_)  Z     = Just x
    idx (_:xs)(S n)  = idx xs n
    idx []    n      = Nothing
    
    |])

type a + b = Plus a b
type a - b = Minus a b
type a * b = Mul a b

type (+@#@$) = PlusSym0
type (-@#@$) = MinusSym0
type (*@#@$) = MulSym0

(%+) = sPlus
(%-) = sMinus
(%*) = sMul

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
  show = show . natToInt  where

{-
Here is a simple proof about the take operation. If the argument k is smaller
than the length of the list, we'll get back a result of length k.
    
-}

proof_Length_Take :: forall k xs. ((k <= Length xs) ~ True) =>
  Sing k -> Sing xs -> Length (Take k xs) :~: k
proof_Length_Take SZ     SNil = Refl
proof_Length_Take SZ     (SCons x ys) = Refl
proof_Length_Take (SS n) (SCons x ys) 
  | Refl <- proof_Length_Pred n ys
  , Refl <- proof_Length_Take n ys
  = Refl

{-

However, the above proof is terrible for two reasons. First, we need to have
the two singleton values around to do the proof, as it pattern matches on
them. Second, if we ever use this proof we need to run it. And that can take
a long time.

-}

ax_Length_Take :: forall k xs.
  ((k <= Length xs) ~ True) => Length (Take k xs) :~: k
ax_Length_Take = unsafeCoerce Refl



prop_natLength_take k xs =
  k <= length xs ==> length (take k xs) == k




-- This example exceeds the ability of GHC's exhaustiveness checker
-- there is a warning if the last line is missing and
-- a warning if it is present
proof_Length_Pred :: forall k x xs.
  Sing k -> Sing xs ->
  ((S k <= Length (x ': xs)) ~ True) => (k <= Length xs) :~: True     
proof_Length_Pred _ = unsafeCoerce Refl
-- proof_Length_Pred SZ (SCons x xs) = Refl
-- proof_Length_Pred (SS j) (SCons x xs) = proof_Length_Pred j xs
-- proof_Length_Pred (SS j) SNil = error "impossible"
  

compile_test1 :: 'Z + n :~: n
compile_test1 = Refl

