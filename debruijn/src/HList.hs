module HList where

import Imports

data HList (l::[Type]) :: Type where
    HNil  :: HList '[]
    HCons :: e -> HList l -> HList (e ': l)

hHead :: HList (t : ts) -> t
hHead (HCons x _) = x

hTail :: HList (e ': l) -> HList l
hTail (HCons _ xs) = xs

hLast :: reverse xs ~ (e : l) => HList xs -> e
hLast = undefined

hAppend :: HList l1 -> HList l2 -> HList (l1 ++ l2)
hAppend HNil ys = ys
hAppend (HCons x xs) ys = HCons x (hAppend xs ys)

