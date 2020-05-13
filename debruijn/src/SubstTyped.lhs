> {-# LANGUAGE TemplateHaskell #-}
> 
> module SubstTyped where

> import Imports

> data Sub (a :: ([k] -> k -> Type)) (g :: [k]) (g'::[k]) where
>    IdS   :: Sub a g g                                     --  identity subst
>    Inc   :: Sub a g (t ': g)                              --  increment by 1 (shift)                
>    (:·)  :: a g' t -> Sub a g g' -> Sub a (t:g) g'        --  extend a substitution (like cons)
>    (:<>) :: Sub a g1 g2 -> Sub a g2 g3 -> Sub a g1 g3     --  compose substitutions

> infixr :·    -- like usual cons operator (:)
> infixr :<>   -- like usual composition  (.)


> -- | Variable reference in a context
> -- This type is isomorphic to the natural numbers
> data Idx g t where
>   Z :: Idx (t:g) t
>   S :: Idx g t -> Idx (t':g) t

> class SubstC (a :: [k] -> k -> Type) where
>    var   :: Idx g t -> a g t
>    subst :: Sub a g g' -> a g t -> a g' t

> -- | Value of the index x in the substitution s
> applyS :: SubstC a => Sub a g g' -> Idx g t -> a g' t
> applyS IdS           x  = var x
> applyS Inc           x  = var (S x)           
> applyS (ty :· s)     Z  = ty
> applyS (ty :· s)  (S x) = applyS s x
> applyS (s1 :<> s2)   x  = subst s2 (applyS s1 x)


> singleSub :: a g t -> Sub a (t:g) g
> singleSub t = t :· IdS

> lift :: SubstC a => Sub a g g' -> Sub a (t:g) (t:g')
> lift s = var Z :· (s :<> Inc)


> {-
> -- | "Environment" heterogenous list
> data Env g where
>   Nil  :: Env '[]
>   Cons :: t -> Env g -> Env (t:g)

> -- fromList :: Env g' -> Sub a (g' ++ g) g
> fromList (Cons t ts)  = t :· fromList ts
> fromList Nil          = idSub
> -}

> {-
> 
> liftN :: SubstC a => Nat -> Sub a -> Sub a
> liftN k s = upTo k (s :∘ Inc k)

> upTo :: SubstC a => Nat -> Sub a -> Sub a
> upTo Z s = s
> upTo (S m) s = upTo m (var m :· s)
> 
> -}
