{-# LANGUAGE TemplateHaskell #-} 
module Poly where

import Imports
import Nat
import Subst

$(singletons [d|

  data Ty = IntTy | Ty :-> Ty | VarTy Idx | PolyTy Ty
    deriving (Eq, Show)

  instance SubstC Ty where
    var = VarTy

    subst s IntTy       = IntTy
    subst s (t1 :-> t2) = subst s t1 :-> subst s t2
    subst s (VarTy x)   = applyS s x
    subst s (PolyTy t)  = PolyTy (subst (lift s) t)
  
    |])

data Exp :: Type where
 IntE   :: Int
        -> Exp
 VarE   :: Idx
        -> Exp 
 LamE   :: Ty       -- type of binder
        -> Exp      -- body of abstraction
        -> Exp          
 AppE   :: Exp      -- function
        -> Exp      -- argument
        -> Exp 
 TyLam  :: Exp      -- bind a type variable
        -> Exp
 TyApp  :: Exp      -- type function
        -> Ty       -- type argument
        -> Exp

instance SubstC Exp where
   var = VarE

   subst s (IntE x)     = IntE x
   subst s (VarE x)     = applyS s x
   subst s (LamE ty e)  = LamE ty (subst (lift s) e)
   subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)
   subst s (TyLam e)    = TyLam (subst (fmap (substTy incSub) s) e)  
   subst s (TyApp e t)  = TyApp (subst s e) t

substTy :: Sub Ty -> Exp -> Exp
substTy s (IntE x)     = IntE x
substTy s (VarE n)     = VarE n
substTy s (LamE t e)   = LamE (subst s t) (substTy s e)
substTy s (AppE e1 e2) = AppE (substTy s e1) (substTy s e2)
substTy s (TyLam e)    = TyLam (substTy (lift s) e)
substTy s (TyApp e t)  = TyApp (substTy s e) (subst s t)


---------------------------------------------------------------------------------

-- | Small-step evaluation of closed terms
step :: Exp -> Maybe Exp
step (IntE x)     = Nothing
step (VarE n)     = error "Unbound Variable"
step (LamE t e)   = Nothing
step (AppE e1 e2) = Just $ stepApp e1 e2
step (TyLam e)    = Nothing
step (TyApp e t)  = Just $ stepTyApp e t

-- | Helper function for the AppE case. 
stepApp :: Exp  -> Exp  -> Exp
stepApp (IntE x)       e2 = error "Type error"
stepApp (VarE n)       e2 = error "Unbound variable"
stepApp (LamE t e1)    e2 = subst (singleSub e2) e1
stepApp (AppE e1' e2') e2 = AppE (stepApp e1' e2') e2
stepApp (TyLam e)      e2 = error "Type error"
stepApp (TyApp e1 t1)  e2 = AppE (stepTyApp e1 t1) e2

-- | Helper function for the TyApp case. 
stepTyApp :: Exp -> Ty -> Exp 
stepTyApp (IntE x)       e2 = error "Type error"
stepTyApp (VarE n)       t1 = error "Unbound variable"
stepTyApp (LamE t e1)    t1 = error "Type error"
stepTyApp (AppE e1' e2') t1 = TyApp (stepApp e1' e2') t1
stepTyApp (TyLam e1)     t1 = substTy (singleSub t1) e1
stepTyApp (TyApp e1 t2)  t1 = TyApp (stepTyApp e1 t2) t1


-- | open reduction
reduce :: Exp -> Exp
reduce (IntE x)   = IntE x
reduce (VarE n)   = VarE n
reduce (LamE t e) = LamE t (reduce e)
reduce (AppE (LamE t e1)  e2) = subst (singleSub (reduce e2)) (reduce e1)
reduce (AppE (IntE x)     e2) = error "Type error"
reduce (AppE (TyLam e1)   e2) = error "Type error"
reduce (AppE e1 e2)           = AppE (reduce e1) (reduce e2)
reduce (TyLam e)              = TyLam (reduce e)
reduce (TyApp (TyLam e)    t) = substTy (singleSub t) (reduce e)
reduce (TyApp (IntE x)     t) = error "Type error"
reduce (TyApp (LamE t1 e2) t) = error "Type error"
reduce (TyApp e            t) = TyApp (reduce e) t

---------------------------------------------------------------------------------
-- | Type checker
typeCheck :: [Ty] -> Exp -> Maybe Ty
typeCheck g (IntE i)    = return IntTy
typeCheck g (VarE j)    = indx g j
typeCheck g (LamE t1 e) = do
  t2 <- typeCheck (t1:g) e
  return (t1 :-> t2)
typeCheck g (AppE e1 e2) = do
  t1 <- typeCheck g e1
  t2 <- typeCheck g e2
  case t1 of
    t12 :-> t22
      | t12 == t2 -> Just t22
    _ -> Nothing
typeCheck g (TyLam e) = do
  ty <- typeCheck (map (subst incSub) g) e
  return (PolyTy ty)
typeCheck g (TyApp e ty) = do
  ty0 <- typeCheck g e
  case ty0 of
    PolyTy ty1 -> Just (subst (singleSub ty) ty1)
    _ -> Nothing
