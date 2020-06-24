{-# LANGUAGE TemplateHaskell #-} 
module Poly where

import Imports
import Nat
import Subst
import Test.QuickCheck

$(singletons [d|

  data Ty = IntTy | Ty :-> Ty | VarTy Idx | PolyTy Ty
    deriving (Eq, Show)

  instance SubstDB Ty where
    var = VarTy

    subst s IntTy       = IntTy
    subst s (t1 :-> t2) = subst s t1 :-> subst s t2
    subst s (VarTy x)   = applySub s x
    subst s (PolyTy t)  = PolyTy (subst (lift s) t)
  
    |])




-- | An AST for System F
-- Adds data constructors for type abstraction and type application
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

    deriving (Eq, Show)

-- Example, the polymorphic identity function
polyId :: Exp 
polyId = TyLam (LamE (VarTy Z) (VarE Z))

-- Example, an instance of the polymorphic identity function
intId :: Exp
intId = TyApp polyId IntTy

-- Substitution for expressions in expressions
instance SubstDB Exp where

   var :: Idx -> Exp
   var = VarE

   subst :: Sub Exp -> Exp -> Exp
   subst s (IntE x)     = IntE x
   subst s (VarE x)     = applySub s x
   subst s (LamE ty e)  = LamE ty (subst (lift s) e)
   subst s (AppE e1 e2) = AppE (subst s e1) (subst s e2)
   subst s (TyLam e)    = TyLam (subst (incTy s) e)  
   subst s (TyApp e t)  = TyApp (subst s e) t

-- | Apply  a type substitution to an expression
substTy :: Sub Ty -> Exp -> Exp
substTy s (IntE x)     = IntE x
substTy s (VarE n)     = VarE n
substTy s (LamE t e)   = LamE (subst s t) (substTy s e)
substTy s (AppE e1 e2) = AppE (substTy s e1) (substTy s e2)
substTy s (TyLam e)    = TyLam (substTy (lift s) e)
substTy s (TyApp e t)  = TyApp (substTy s e) (subst s t)


-- | Increment all types in an expression substitution
incTy :: Sub Exp -> Sub Exp
incTy = fmap (substTy incSub)



----------------------------------------------------------------

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


-- | Open, parallel reduction (i.e. reduce under lambda expressions)
-- This doesn't fully reduce the lambda term to normal form in one step
-- (but is guaranteed to terminate, even on ill-typed terms)
reduce :: Exp -> Exp
reduce (IntE x)     = IntE x
reduce (VarE n)     = VarE n
reduce (LamE t e)   = LamE t (reduce e)
reduce (TyLam e)    = TyLam (reduce e)
reduce (AppE e1 e2) = case reduce e1 of
  IntE x     -> error "type error" -- don't have to observe this type error, but we can
  TyLam e    -> error "type error"
  LamE t e1' -> subst (singleSub (reduce e2)) e1'
  e1'        -> AppE e1' (reduce e2)
reduce (TyApp e1 t) = case reduce e1 of
  IntE x    -> error "type error" -- don't have to observe this type error, but we can
  LamE t e1 -> error "type error" -- don't have to observe this type error, but we can
  TyLam e1' -> substTy (singleSub t) e1'
  e1'       -> TyApp e1' t


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


-------------------------------------------------------------------

instance Arbitrary Ty where
  arbitrary = sized gt where
   base = oneof [VarTy <$> arbitrary, return IntTy]
   gt m =
     if m <= 1 then base else
     let m' = m `div` 2 in
     frequency
     [(1, base),
      (1, (:->) <$> gt m' <*> gt m'),
      (1, PolyTy    <$>  gt m')]

  shrink IntTy       = []
  shrink (VarTy n)   = [VarTy n' | n' <- shrink n ]
  shrink (PolyTy s)  = s : [ PolyTy s' | s' <- shrink s]
  shrink (t1 :-> t2) = t1 : t2 : [t1' :-> t2 | t1' <- shrink t1] ++ [t1 :-> t2' | t2' <- shrink t2]


instance Arbitrary Exp where
  arbitrary = sized gt where
   base = oneof [VarE <$> arbitrary]
   gt m =
     if m <= 1 then base else
     let m' = m `div` 2 in
     frequency
     [(1, base),
      (1, AppE    <$> gt m' <*> gt m'),
      (1, LamE    <$> arbitrary <*> gt m'),
      (1, TyLam   <$> gt m'),
      (1, TyApp   <$> gt m' <*> arbitrary)]

  shrink (IntE _)      = []
  shrink (VarE n)      = [VarE n' | n' <- shrink n ]
  shrink (LamE t s)    = s : [ LamE t s' | s' <- shrink s] ++ [ LamE t' s | t' <- shrink t]
  shrink (AppE t1 t2)  = t1 : t2 : [AppE t1' t2 | t1' <- shrink t1] ++ [AppE t1 t2' | t2' <- shrink t2]
  shrink (TyLam s)     = s : [ TyLam s' | s' <- shrink s]  
  shrink (TyApp t1 t2) = t1 : [TyApp t1' t2 | t1' <- shrink t1] ++ [TyApp t1 t2' | t2' <- shrink t2]

