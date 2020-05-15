
module TypeCheck where

import Prelude hiding ((!!),(>>),drop,take,length)
import Test.QuickCheck hiding ((===))

import Imports
import qualified Nat as P
import qualified Subst as P
import qualified Poly as P
import SubstTyped
import PolyTyped 


data TcResult f ctx where
  Checks :: Sing t -> f ctx t -> TcResult f ctx
  Errors :: String -> TcResult f ctx

--seq :: TcResult f ctx -> (Sing t -> f ctx t -> TcResult f ctx) -> TcResult f ctx

tcVar :: Sing ctx -> P.Idx -> TcResult Idx ctx
tcVar (SCons t _ )   P.Z     = Checks t Z
tcVar (SCons _ ts)  (P.S m)  =
  case tcVar ts m of
   Checks t v -> Checks t (S v)
   Errors s   -> Errors s
tcVar SNil          _     = Errors "unbound variable"
   
tcExp :: Sing ctx -> P.Exp -> TcResult Exp ctx
tcExp g (P.IntE x) = Checks sing (IntE x)
tcExp g (P.VarE k) =
  case tcVar g k of
    Checks t v -> Checks t (VarE v)
    Errors s   -> Errors s 
tcExp g (P.LamE t1 u) 
  | SomeSing sT1 <- toSing t1
  = case tcExp (SCons sT1 g) u of
      Checks sT2 e -> Checks (sT1 P.:%-> sT2) (LamE sT1 e)
      Errors s     -> Errors s
tcExp g (P.AppE u1 u2) =
  case tcExp g u1 of
    Checks t1 e1 -> case tcExp g u2 of
      Checks t2 e2 ->
        case t1 of
          t11 P.:%-> t12 ->
            case testEquality t11 t2 of
              Just Refl -> Checks t12 (AppE e1 e2)
              Nothing -> Errors "Types don't match"
          _ -> Errors "Not a function type"
      Errors s -> Errors s
    Errors s -> Errors s
tcExp g (P.TyLam u1)
  = case tcExp (P.sIncList g) u1 of
      Checks t1 e1 -> Checks (P.SPolyTy t1) (TyLam e1)
      Errors s     -> Errors s
tcExp g (P.TyApp u1 ty)
  | SomeSing sTy <- toSing ty
  = case tcExp g u1 of
      Checks t e1 ->
        case t of
          (P.SPolyTy t1) ->
            Checks (P.sSubst (P.sSingleSub sTy) t1) (TyApp e1 sTy)
          _ -> Errors "Wrong type in tyapp"
      Errors s -> Errors s
    