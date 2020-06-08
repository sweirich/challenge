{-# OPTIONS_GHC -fwarn-incomplete-patterns -Wno-redundant-constraints #-}
 
module Imports(

  type Π, 

  module Data.Singletons,
  module Data.Singletons.Prelude,
  module Data.Singletons.Prelude.Eq,
  module Data.Singletons.Prelude.Enum,
  module Data.Singletons.Prelude.Num,
  module Data.Singletons.TH,

  -- Data.Kind
  type Type,

  -- * The equality types
  (:~:)(..), type (~~),
  (:~~:)(..),

  -- * Working with equality
  sym, trans, castWith, gcastWith, apply, inner, outer,

  -- * Inferring equality from other types
  TestEquality(..)

) where

import Data.Singletons
import Data.Singletons.Prelude.Eq
import Data.Singletons.Prelude.Enum
import Data.Singletons.Prelude.Num
import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Kind(Type)
import Data.Type.Equality

type Π = Sing
