-- | Assert that a type equality holds.  Be *very* careful with using this
-- function.  It is unsafe! If the equality does not hold, then the function
-- can be used to subvert the type system of GHC, and potentially cause GHC to
-- crash.
module AssertEquality (assertEquality) where

import Data.Type.Equality
import Unsafe.Coerce

assertEquality :: a :~: b
assertEquality = unsafeCoerce Refl

