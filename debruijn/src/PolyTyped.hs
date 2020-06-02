module PolyTyped where

import Nat
import Imports
-- Note: due to a limitation of singletons, we cannot qualify this module import.
import Subst
import SubstProperties 
import qualified SubstTyped as T

-- We import the definition of types from the "untyped" AST so that we can
-- later write a type checker that shares these types. (See TypeCheck.hs).
import Poly (Ty(..),STy(..))


-- | The well-typed AST for System F
data Exp :: [Ty] -> Ty -> Type where

  IntE   :: Int
         -> Exp g IntTy

  VarE   :: T.Idx g t
         -> Exp g t

  LamE   :: Sing t1               -- type of binder
         -> Exp (t1:g) t2         -- body of abstraction
         -> Exp g (t1 :-> t2)

  AppE   :: Exp g (t1 :-> t2)     -- function
         -> Exp g t1              -- argument
         -> Exp g t2

  TyLam  :: Exp (IncList g) t     -- bind a type variable
         -> Exp g (PolyTy t)

  TyApp  :: Exp g (PolyTy t1)     -- type function
         -> Sing t2               -- type argument
         -> Exp g (Subst (SingleSub t2) t1)

-- Although the types are much more explicit, the actual code of the instance
-- definition is unchanged from [Poly.hs](Poly.hs)
instance T.SubstC Exp where
   var = VarE

   subst s (IntE x)     = IntE x
   subst s (VarE x)     = T.applyS s x
   subst s (LamE ty e)  = LamE ty (T.subst (T.lift s) e)
   subst s (AppE e1 e2) = AppE (T.subst s e1) (T.subst s e2)
   subst s (TyLam e)    = TyLam (T.subst (substSubTy sIncSub s) e)
   subst s (TyApp e t)  = TyApp (T.subst s e) t

substTy :: forall g s ty.
   Sing (s :: Sub Ty) -> Exp g ty -> Exp (Map (SubstSym1 s) g) (Subst s ty)
substTy s (IntE x)     = IntE x
substTy s (VarE n)     = VarE $ T.mapIdx @(SubstSym1 s)  n
substTy s (LamE t e)   = LamE (sSubst s t) (substTy s e)
substTy s (AppE e1 e2) = AppE (substTy s e1) (substTy s e2)
substTy s (TyLam (e :: Exp (IncList g) t))    
    | Refl <- axiom1 @g s = TyLam (substTy (sLift s) e)
substTy s (TyApp (e :: Exp g (PolyTy t1)) (t :: Sing t2))  
    | Refl <- axiom2 @t1 @t2 s
                       = TyApp (substTy s e) (sSubst s t)

substSubTy :: forall s g g'. Sing s -> T.Sub Exp g g' -> T.Sub Exp (Map (SubstSym1 s) g) (Map (SubstSym1 s) g')
substSubTy s (T.Inc (x :: T.IncBy g1)) 
  | Refl <- axiom_map1 @(SubstSym1 s) @g1 @g = T.Inc (T.mapInc @(SubstSym1 s)  x) 
substSubTy s (e T.:< s1)   = substTy s e T.:< substSubTy s s1
substSubTy s (s1 T.:<> s2) = substSubTy s s1 T.:<> substSubTy s s2

---------------------------------------------------------------------------------



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
stepTyApp :: Exp '[] (PolyTy t1) -> Sing t -> Exp '[] (Subst (SingleSub t) t1)
--stepTyApp (IntE x)       e2 = error "Type error"
stepTyApp (VarE n)       t1 = case n of {}
--stepTyApp (LamE t e1)    t1 = error "Type error"
stepTyApp (AppE e1' e2') t1 = TyApp (stepApp e1' e2') t1
stepTyApp (TyLam e1)     t1 = substTy (sSingleSub t1) e1
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
reduce (TyApp (TyLam e) (t1 :: Sing t1))
    | Refl <- axiom3 @(Inc (S Z)) @(t1 :< Inc Z) @g   -- because the context is not empty
    , Refl <- axiom4 @t1 @(Inc Z)                     -- there are some facts we need to know
    , Refl <- axiom5 @g                                
      = substTy (sSingleSub t1) (reduce e)
--reduce (TyApp (IntE x)     t) = error "Type error"
--reduce (TyApp (LamE t1 e2) t) = error "Type error"    
reduce (TyApp e t)           = TyApp (reduce e) t


