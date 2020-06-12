module PolyTyped where

import Imports

-- We use Subst for type-level indices and substitutions and SubstTyped for
-- expression-level indices and substitution. To be clear which is which, we
-- qualify the imports.
import qualified Subst as U
import qualified SubstTyped as T

import SubstProperties 

-- We import the definition of System F types from the weakly-typed version of
-- the AST. This will allow us to write a type checker that shares these
-- types. (See TypeCheck.hs).

import Poly (Ty(..), STy(..))


-- | The well-typed AST for System F
data Exp :: [Ty] -> Ty -> Type where

  IntE   :: Int
         -> Exp g IntTy

  VarE   :: T.Idx g t
         -> Exp g t

  LamE   :: Π (t1 :: Ty)          -- type of binder
         -> Exp (t1:g) t2         -- body of abstraction
         -> Exp g (t1 :-> t2)

  AppE   :: Exp g (t1 :-> t2)     -- function
         -> Exp g t1              -- argument
         -> Exp g t2

  TyLam  :: Exp (IncList g) t     -- bind a type variable
         -> Exp g (PolyTy t)

  TyApp  :: Exp g (PolyTy t1)     -- type function
         -> Π (t2 :: Ty)          -- type argument
         -> Exp g (U.Subst (U.SingleSub t2) t1)

-- Example, the polymorphic identity function
polyId :: Exp '[] (PolyTy (VarTy U.Z :-> VarTy U.Z))
polyId = TyLam (LamE (SVarTy U.SZ) (VarE T.Z))

-- Example, an instance of the polymorphic identity function
intId :: Exp '[] (IntTy :-> IntTy)
intId = TyApp polyId SIntTy


-- Example, an instance of the polymorphic identity function
alphaId :: Exp '[] (VarTy U.Z :-> VarTy U.Z)
alphaId = TyApp polyId (SVarTy U.SZ)




-- Although the types are *much* more explicit, the actual code of the
-- instance definition is unchanged from [Poly.hs](Poly.hs)
instance T.SubstDB Exp where

   var :: T.Idx g t -> Exp g t
   var = VarE

   subst :: T.Sub Exp g g' -> Exp g t -> Exp g' t
   subst s (IntE x)     = IntE x
   subst s (VarE x)     = T.applySub s x
   subst s (LamE ty e)  = LamE ty (T.subst (T.lift s) e)
   subst s (AppE e1 e2) = AppE (T.subst s e1) (T.subst s e2)
   subst s (TyLam e)    = TyLam (T.subst (incTy s) e)
   subst s (TyApp e t)  = TyApp (T.subst s e) t

-- | Apply a type substitution to an expression
substTy :: forall g s ty.
   Π (s :: U.Sub Ty) -> Exp g ty -> Exp (Map (U.SubstSym1 s) g) (U.Subst s ty)
substTy s (IntE x)     = IntE x
substTy s (VarE n)     = VarE $ T.mapIdx @(U.SubstSym1 s)  n
substTy s (LamE t e)   = LamE (U.sSubst s t)   (substTy s e)
substTy s (AppE e1 e2) = AppE (substTy s e1) (substTy s e2)
substTy s (TyLam (e :: Exp (IncList g) t))    
    | Refl <- axiom1 @g s 
     = TyLam (substTy (U.sLift s) e)
substTy s (TyApp (e :: Exp g (PolyTy t1)) (t :: STy t2))  
    | Refl <- axiom2 @t1 @t2 s
     = TyApp (substTy s e) (U.sSubst s t)

-- | Increment all types in a term substitution
--  IncList ~ Map (SubstSym1 IncSub)
incTy :: forall s g g'. T.Sub Exp g g'
      -> T.Sub Exp (IncList g) (IncList g')
incTy (T.Inc (x :: T.IncBy g1)) 
  | Refl <- axiom_map1 @(U.SubstSym1 U.IncSub) @g1 @g
  = T.Inc (T.mapInc @(U.SubstSym1 U.IncSub)  x) 
incTy (e T.:< s1)   = substTy U.sIncSub e T.:< incTy s1
incTy (s1 T.:<> s2) = incTy s1 T.:<> incTy s2


-------------------------------------------------------------------

-- | Small-step evaluation of closed terms
step :: Exp '[] t -> Maybe (Exp '[] t)
step (IntE x)     = Nothing
step (VarE n)     = case n of {}  
step (LamE t e)   = Nothing
step (AppE e1 e2) = Just $ stepApp e1 e2
step (TyLam e)    = Nothing
step (TyApp e t)  = Just $ stepTyApp e t

-- | Helper function for the AppE case. This function proves that we will
-- *always* take a step if a closed term is an application expression.
stepApp :: Exp '[] (t1 :-> t2) -> Exp '[] t1  -> Exp '[] t2
--stepApp (IntE x)       e2 = error "Type error"
stepApp (VarE n)       e2 = case n of {}
stepApp (LamE t e1)    e2 = T.subst (T.singleSub e2) e1
stepApp (AppE e1' e2') e2 = AppE (stepApp e1' e2') e2
--stepApp (TyLam e)      e2 = error "Type error"
stepApp (TyApp e1 t1)  e2 = AppE (stepTyApp e1 t1) e2

-- | Helper function for the TyApp case. This function proves that we will
-- *always* take a step if a closed term is a type application expression.
stepTyApp :: Exp '[] (PolyTy t1) -> Π t -> Exp '[] (U.Subst (U.SingleSub t) t1)
--stepTyApp (IntE x)       e2 = error "Type error"
stepTyApp (VarE n)       t1 = case n of {}
--stepTyApp (LamE t e1)    t1 = error "Type error"
stepTyApp (AppE e1' e2') t1 = TyApp (stepApp e1' e2') t1
stepTyApp (TyLam e1)     t1 = substTy (U.sSingleSub t1) e1
stepTyApp (TyApp e1 t2)  t1 = TyApp (stepTyApp e1 t2) t1

-- | open reduction
reduce :: forall g t. Exp g t -> Exp g t
reduce (IntE x)   = IntE x
reduce (VarE n)   = VarE n
reduce (LamE t e) = LamE t (reduce e)
reduce (AppE (LamE t e1) e2) = T.subst (T.singleSub (reduce e2)) (reduce e1)
--reduce (AppE (IntE x)     e2) = error "Type error"
--reduce (AppE (TyLam e1)   e2) = error "Type error"
reduce (AppE e1 e2)          = AppE (reduce e1) (reduce e2)
reduce (TyLam e)             = TyLam (reduce e)
reduce (TyApp (TyLam e) (t1 :: STy t1))
      | Refl <- axiom6 @t1 @g
      = substTy (U.sSingleSub t1) (reduce e)
--reduce (TyApp (IntE x)     t) = error "Type error"
--reduce (TyApp (LamE t1 e2) t) = error "Type error"    
reduce (TyApp e t)           = TyApp (reduce e) t


