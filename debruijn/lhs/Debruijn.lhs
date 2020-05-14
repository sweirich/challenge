> module Debruijn where
>
> import Nat
> import Text.Leijen.PrettyPrint (Pretty(..))
> import qualified Text.Leijen.PrettyPrint as PP
>
> data Ty where
>   Base  :: Ty
>   (:->) ::  Ty -> Ty -> Ty
> 
> data Exp where
>   BaseE :: Exp
>   VarE  :: Nat -> Exp
>   LamE  :: Exp -> Exp -> Exp
>   AppE  :: Exp -> Exp -> Exp




> instance Pretty Ty where
>   pretty Base = PP.text "o"
>   pretty (t1 :-> t2) = pretty t1 <+> PP.text "->" <+> pretty t2

> instance Pretty Exp where
>   pretty BaseE = PP.text "()"
>   pretty (VarE n) = PP.text $ "v" ++ show (fromInteger n)

