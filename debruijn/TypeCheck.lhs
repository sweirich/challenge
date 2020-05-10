\begin{code}
module TypeCheck where

import Prelude hiding ((!!),(>>),drop,take,length)
import Test.QuickCheck hiding ((===))

import Imports
import Nat
import SysF

import Debug.Trace


\end{code}


Example -- a System F type checker

\begin{code}
data UExp =
    UVar Nat
  | ULam Ty UExp
  | UApp UExp UExp
  | UTyLam Nat UExp
  | UTyApp UExp [Ty]
\end{code}

Untyped version
\begin{code}
utc :: [Ty] -> UExp -> Maybe Ty
utc g (UVar j)    = idx g j
utc g (ULam t1 e) = do
  t2 <- utc (t1:g) e
  return (FnTy t1 t2)
utc g (UApp e1 e2) = do
  t1 <- utc g e1
  t2 <- utc g e2
  case t1 of
    FnTy t12 t22
      | t12 == t2 -> Just t22
    _ -> Nothing
utc g (UTyLam k e) = do
  ty <- utc (incList k g) e
  return (PolyTy k ty)
utc g (UTyApp e tys) = do
  ty <- utc g e
  case ty of
    PolyTy k ty1
      | k == length tys
      -> Just (subst (fromList tys) ty1)
    _ -> Nothing
\end{code}


Type checker

\begin{code}
data TcResult f ctx where
  Checks :: Sing t -> f ctx t -> TcResult f ctx
  Errors :: String -> TcResult f ctx

--seq :: TcResult f ctx -> (Sing t -> f ctx t -> TcResult f ctx) -> TcResult f ctx
  
tcVar :: Sing ctx -> Nat -> TcResult Var ctx
tcVar (SCons t _ )   Z     = Checks t (V SZ)
tcVar (SCons _ ts)  (S m)  =
  case tcVar ts m of
   Checks t (V v) -> Checks t (V (SS v))
   Errors s   -> Errors s
tcVar SNil          _     = Errors "unbound variable"
   
tcExp :: Sing ctx -> UExp -> TcResult Exp ctx
tcExp g (UVar k) =
  case tcVar g k of
    Checks t (V v) -> Checks t (VarE v)
    Errors s   -> Errors s 
tcExp g (ULam t1 u)
  | SomeSing sT1 <- toSing t1
  = case (tcExp (SCons sT1 g) u) of
      Checks sT2 e -> Checks (SFnTy sT1 sT2) (LamE sT1 e)
      Errors s     -> Errors s
tcExp g (UApp u1 u2) =
  case (tcExp g u1) of
    Checks t1 e1 -> case (tcExp g u2) of
      Checks t2 e2 ->
        case t1 of
          SFnTy t11 t12 ->
            case testEquality t11 t2 of
              Just Refl -> Checks t12 (AppE e1 e2)
              Nothing -> Errors "Types don't match"
          _ -> Errors "Not a function type"
      Errors s -> Errors s
    Errors s -> Errors s
tcExp g (UTyLam k u1)
  | SomeSing sK <- toSing k
  = case (tcExp (sIncList sK g) u1) of
      Checks t1 e1 -> Checks (SPolyTy sK t1) (TyLam sK e1)
      Errors s     -> Errors s
tcExp g (UTyApp u1 tys)
  | SomeSing sTys <- toSing tys
  = case (tcExp g u1) of
      Checks t e1 ->
        case t of
          (SPolyTy sK t1) ->
            case testEquality sK (sLength sTys) of
              Just Refl -> Checks (sSubst (sFromList sTys) t1) (TyApp e1 sTys)
              Nothing -> Errors "Wrong number of type args"
          _ -> Errors "Wrong type in tyapp"
      Errors s -> Errors s
      
\end{code}
