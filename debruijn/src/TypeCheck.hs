-- | Example demonstrating a type checker.
-- A conversion from a weakly-typed AST to strongly-typed AST
module TypeCheck where

import Prelude hiding ((!!),(>>),drop,take,length)
import Test.QuickCheck hiding ((===))

import Imports
import qualified Nat   as W
import qualified Subst as W
import qualified Poly  as W
import qualified SubstProperties as W

import Poly (Ty(..),STy(..)) -- types are shared between the two languages.
import PolyTyped

import SubstTyped


-- | The result type of the type checker. Either the term type checks in
-- the given context or there is some sort of type error.
data TcResult f g where
  Errors :: String -> TcResult f g  
  Checks :: Sing t -> f g t -> TcResult f g

-- Type checking a variable occurrence (i.e. a natural number)
-- producing an index into the context.
tcVar :: Sing g -> W.Idx -> TcResult Idx g
tcVar (SCons t _ )   W.Z     = Checks t Z
tcVar (SCons _ ts)  (W.S m)  =
  case tcVar ts m of
   Checks t v -> Checks t (S v)
   Errors s   -> Errors s
tcVar SNil          _     = Errors "unbound variable"

-- Type checking a term                            
tcExp :: Sing g -> W.Exp -> TcResult Exp g
tcExp g (W.IntE x) = Checks sing (IntE x)
tcExp g (W.VarE k) =
  case tcVar g k of
    Checks t v -> Checks t (VarE v)
    Errors s   -> Errors s 
tcExp g (W.LamE t1 u) 
  | SomeSing sT1 <- toSing t1
  = case tcExp (SCons sT1 g) u of
      Checks sT2 e -> Checks (sT1 W.:%-> sT2) (LamE sT1 e)
      Errors s     -> Errors s
tcExp g (W.AppE u1 u2) =
  case tcExp g u1 of
    Checks t1 e1 -> case tcExp g u2 of
      Checks t2 e2 ->
        case t1 of
          t11 :%-> t12 ->
            case testEquality t11 t2 of
              Just Refl -> Checks t12 (AppE e1 e2)
              Nothing -> Errors "Types don't match"
          _ -> Errors "Not a function type"
      Errors s -> Errors s
    Errors s -> Errors s
tcExp g (W.TyLam u1)
  = case tcExp (W.sIncList g) u1 of
      Checks t1 e1 -> Checks (W.SPolyTy t1) (TyLam e1)
      Errors s     -> Errors s
tcExp g (W.TyApp u1 ty)
  | SomeSing sTy <- toSing ty
  = case tcExp g u1 of
      Checks t e1 ->
        case t of
          (SPolyTy t1) ->
            Checks (W.sSubst (W.sSingleSub sTy) t1) (TyApp e1 sTy)
          _ -> Errors "Wrong type in tyapp"
      Errors s -> Errors s
    
