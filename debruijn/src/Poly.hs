{-# LANGUAGE TemplateHaskell #-} 
module Poly where

import Imports
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
   subst s (TyLam e)    = TyLam (subst (substTySub Inc s) e)    --- note, this line is hard to motivate
   subst s (TyApp e t)  = TyApp (subst s e) t

substTy :: Sub Ty -> Exp -> Exp
substTy s (IntE x)     = IntE x
substTy s (VarE n)     = VarE n
substTy s (LamE t e)   = LamE (subst s t) (substTy s e)
substTy s (AppE e1 e2) = AppE (substTy s e1) (substTy s e2)
substTy s (TyLam e)    = TyLam (substTy (lift s) e)
substTy s (TyApp e t)  = TyApp (substTy s e) (subst s t)

substTySub :: Sub Ty -> Sub Exp -> Sub Exp 
substTySub s IdS         = IdS
substTySub s Inc         = Inc
substTySub s (e   :· s1) = substTy s e :· substTySub s s1
substTySub s (s1 :<> s2) = substTySub s s1 :<> substTySub s s2

-- | is an expression a value?
value :: Exp -> Bool
value (IntE x)   = True
value (LamE t e) = True
value (TyLam e)  = True
value _          = False

-- | Small-step evaluation
step :: Exp -> Maybe Exp
step (IntE x)   = Nothing
step (VarE n)   = error "Unbound Variable"
step (LamE t e) = Nothing
step (AppE (LamE t e1) e2)   = Just $ subst (singleSub e2) e1
step (AppE e1 e2) | value e1 = error "Type error!"
step (AppE e1 e2) = do e1' <- step e1
                       return $ AppE e1' e2
step (TyLam e)  = Nothing
step (TyApp (TyLam e) t)   = Just $ substTy (singleSub t) e
step (TyApp e t) | value e = error "Type error!"
step (TyApp e t) = do e' <- step e
                      return $ TyApp e' t

-- | open reduction
reduce :: Exp -> Exp
reduce (IntE x)   = IntE x
reduce (VarE n)   = VarE n
reduce (LamE t e) = LamE t (reduce e)
reduce (AppE (LamE t e1) e2)   = subst (singleSub (reduce e2)) (reduce e1)
reduce (AppE e1 e2) | value e1 = error "Type error!"
reduce (AppE e1 e2) = AppE (reduce e1) (reduce e2)
reduce (TyLam e)    = TyLam (reduce e)
reduce (TyApp (TyLam e) t)   = substTy (singleSub t) (reduce e)
reduce (TyApp e t) | value e = error "Type error!"
reduce (TyApp e t) = TyApp (reduce e) t


-- | Type checker
utc :: [Ty] -> Exp -> Maybe Ty
utc g (IntE i)    = return IntTy
utc g (VarE j)    = indx g j
utc g (LamE t1 e) = do
  t2 <- utc (t1:g) e
  return (t1 :-> t2)
utc g (AppE e1 e2) = do
  t1 <- utc g e1
  t2 <- utc g e2
  case t1 of
    t12 :-> t22
      | t12 == t2 -> Just t22
    _ -> Nothing
utc g (TyLam e) = do
  ty <- utc (map (subst Inc) g) e
  return (PolyTy ty)
utc g (TyApp e ty) = do
  ty0 <- utc g e
  case ty0 of
    PolyTy ty1 -> Just (subst (singleSub ty) ty1)
    _ -> Nothing