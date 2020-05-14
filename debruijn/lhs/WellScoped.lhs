\begin{code}
{-# LANGUAGE TypeInType #-}
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
module WellScoped where

import Prelude hiding ((!!),(>>), take, drop, length)
import Data.Singletons
import Data.Singletons.Prelude
   hiding (Drop,Take,Length,
          sDrop,sTake,sLength,
          DropSym0,DropSym1,DropSym2,
          TakeSym0,TakeSym1,TakeSym2)
import Data.Singletons.TH
import Data.Kind(Type)

import Data.Type.Equality
import Test.QuickCheck((==>))

import Nat

-- Can we make a singleton for this???
data Fin :: Nat -> Type where
   FZ :: Fin n
   FS :: Fin n -> Fin (S n)
data Ty :: Nat -> Type where
   BaseTy :: Ty n
   VarTy  :: Fin n -> Ty n
   FnTy   :: Ty n -> Ty n -> Ty n
   PolyTy :: Ty (S n) -> Ty n

data instance Sing (m :: Fin n) :: Type where
   SFZ :: Sing FZ  
   SFS :: Sing n -> Sing (FS n)

data instance Sing (m :: Ty n) ::  Type where
   SBaseTy :: Sing (BaseTy :: Ty n)
   SVarTy  :: Sing m -> Sing (VarTy m)            
   SFnTy   :: Sing t1 -> Sing t1 -> Sing (FnTy t1 t2)
   SPolyTy :: Sing t1 -> Sing (PolyTy t1)


data Sub :: Nat -> Nat -> Type where
    Id   :: Sub n n
    Inc  :: Sub n (S n)    
    (:>) :: (Ty n)  -> Sub n m -> Sub (S n) m
    (:*) :: Sub m n -> Sub n k -> Sub m k

infixr :>    -- like usual cons operator (:)
infixr :*    -- like usual composition  (.)


\end{code}
