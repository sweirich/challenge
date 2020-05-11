> {-# LANGUAGE TemplateHaskell #-}
> 
> module SubstTyped where

> import Nat
> import Imports

> data Sub (a :: ([k] -> k -> Type)) (g :: [k]) (g'::[k]) where
>    IdS  :: Sub a g g              
>    Inc  :: Sub a g (t ': g)
>    (:·) :: a g' t -> Sub a g g' -> Sub a (t:g) g'
>    (:∘) :: Sub a g1 g2 -> Sub a g2 g3 -> Sub a g1 g3

> infixr :·    -- like usual cons operator (:)
> infixr :∘    -- like usual composition  (.)

> singleSub :: a g t -> Sub a (t:g) g
> singleSub t = t  :· IdS

> -- | Variable reference in a context
> data Var g t where
>   VZ :: Var (t:g) t
>   VS :: Var g t -> Var (t':g) t

> {-
> -- | "Environment" heterogenous list
> data Env g where
>   Nil  :: Env '[]
>   Cons :: t -> Env g -> Env (t:g)

> -- fromList :: Env g' -> Sub a (g' ++ g) g
> fromList (Cons t ts)  = t :· fromList ts
> fromList Nil          = idSub
> -}

> class SubstC (a :: [k] -> k -> Type) where
>    var   :: Var g t -> a g t
>    subst :: Sub a g g' -> a g t -> a g' t

> -- | Value of the index x in the substitution s
> applyS :: SubstC a => Sub a g g' -> Var g t -> a g' t
> applyS IdS            x  = var x
> applyS Inc            x  = var (VS x)           
> applyS (ty :· s)     VZ  = ty
> applyS (ty :· s)  (VS x) = applyS s x
> applyS (s1 :∘ s2)     x  = subst s2 (applyS s1 x)

> lift :: SubstC a => Sub a g g' -> Sub a (t:g) (t:g')
> lift s = var VZ :· (s :∘ Inc)

> {-
> 
> liftN :: SubstC a => Nat -> Sub a -> Sub a
> liftN k s = upTo k (s :∘ Inc k)

> upTo :: SubstC a => Nat -> Sub a -> Sub a
> upTo Z s = s
> upTo (S m) s = upTo m (var m :· s)
> 
> -}
