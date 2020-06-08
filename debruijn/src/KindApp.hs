import Data.Kind

type family Bar a b where
  Bar Int Bool = Int

data Foo a b (c :: Bar a b) where

x :: Foo a b c -> Int
x = undefined
  
data Baz :: forall a b . Bar a b -> Type where

y :: Baz c -> Int
y = undefined

z :: forall a b c. Baz @a @b c -> Int
z = undefined

  
