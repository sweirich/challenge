\section{Extended example: CPS conversion}

%if False
\begin{code}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Cps where

import Prelude hiding ((!!),(>>),drop,take,length)
import Test.QuickCheck hiding ((===))
import Unsafe.Coerce
import Debug.Trace

import Imports
import Nat
import SysF
\end{code}
%endif

In this section, we demonstrate this typed abstract syntax by working through
the example of polymorphic CPS-conversion~\cite{cps}.

In CPS conversion, all functions and polymorphic types are modified to take an
additional argument, \emph{continuation}.  Furthermore, functions don't
return; they invoke their continuations instead.  So the result type of the
function is \emph{void}, i.e. $\forall a.a$, expressed in System F as:

\begin{code}
$(singletons
  [d|
    voidTy = PolyTy (S Z) (VarTy Z)
    |])
\end{code}

The type transformation is an injective function. Haskell can observe such
things if we tell it to do so. Therefore, we define this transformation, not
using the singletons library, but as a closed type family with an injectivity
constraint. (The result `r` determines the input `a`).

\begin{code}
type family CpsTy a = r | r -> a where
  CpsTy (VarTy i)      = VarTy i
  CpsTy BaseTy         = BaseTy
  CpsTy (FnTy t1 t2)   =
    FnTy (CpsTy t1) (FnTy (ContTy t2) VoidTy)
  CpsTy (PolyTy k t1)  =
    PolyTy k (FnTy (ContTy t1) VoidTy)

type family ContTy a = r | r -> a where
  ContTy t = FnTy (CpsTy t) VoidTy

type family CpsList g = r | r -> g where
   CpsList '[] = '[]
   CpsList (t : g) = (CpsTy t : CpsList g)
\end{code}

The singletons library does not support injectivity constraints, so we are
forced in this case to explicitly write these functions three times. (This
code is omitted.)

%if False
\begin{code}
cpsTy :: Ty -> Ty
cpsTy (VarTy i)      = VarTy i
cpsTy BaseTy         = BaseTy
cpsTy (FnTy t1 t2)   = FnTy (cpsTy t1) (FnTy (contTy t2) voidTy)
cpsTy (PolyTy k t1)  = PolyTy k (FnTy (contTy t1) voidTy)

contTy :: Ty -> Ty
contTy t = FnTy (cpsTy t) voidTy

cpsList :: [Ty] -> [Ty]
cpsList [] = []
cpsList (t:ts) = cpsTy t : cpsList ts

sCpsTy :: Sing t -> Sing (CpsTy t)
sCpsTy (SVarTy i)      = SVarTy i
sCpsTy SBaseTy         = SBaseTy
sCpsTy (SFnTy t1 t2)   = SFnTy (sCpsTy t1) (SFnTy (sContTy t2) sVoidTy)
sCpsTy (SPolyTy k t1)  = SPolyTy k (SFnTy (sContTy t1) sVoidTy)

sContTy :: Sing t -> Sing (ContTy t)
sContTy t = SFnTy (sCpsTy t) sVoidTy

sCpsList :: Sing ts -> Sing (CpsList ts)
sCpsList SNil = SNil
sCpsList (SCons t ts) = SCons (sCpsTy t) (sCpsList ts)
\end{code}
%endif


The CPS transform is tricky with this representation for two reasons.

First, an efficient one pass transformation requires the use of both object
and \emph{meta} level continuations. (Without meta continuations, the
transform introduces additional $\beta$-redexes.) Usually, these
meta-continuations are represented by functions in the host language. This
works well for HOAS-based variable representations, but doesn't work with
debruijn indices.

For that reason, we follow Pottier~\cite{pottier}, and define meta
continuations as expressions with dedicated holes.

\begin{code}
data Cont g t where
  Obj   :: Exp g (FnTy t VoidTy)  -> Cont g t
  Meta  :: Exp (t : g) VoidTy     -> Cont g t

applyCont :: Cont g t -> Exp g t -> Exp g VoidTy
applyCont (Obj o)  v  = AppE o v
applyCont (Meta k) v  = (substE (ConsE v IdE)) k

reifyCont :: Sing t -> Cont g t -> Exp g (FnTy t VoidTy)
reifyCont t (Obj o)   = o
reifyCont t (Meta k)  = LamE t k
\end{code}

Because this representation of continuations is first-order, we can easily
define substitution operations for both type and expression variables.

\begin{code}
substTyCont :: Sing s -> Cont g t -> Cont (SubstList s g) (Subst s t)
substTyCont s (Obj o)   = Obj (substTy s o)
substTyCont s (Meta k)  = Meta (substTy s k)

substCont :: SubE g g' -> Cont g t -> Cont g' t
substCont s (Obj o)   = Obj (substE s o)
substCont s (Meta k)  = Meta (substE (liftE1 s) k)
\end{code}


The other difficulty with this transformation is that, by introducing new
continuation arguments in the transformation of functions and polymorphic
expressions, it modifies the context. As a result, when we transform
expression variables, we need to shift their indices.

Most versions of this transformation mark these newly introduced assumptions
with a special purpose ``continuation type'' so that it is easy to define the
relationship between in the input and output contexts.

However, here we do not specialize our language to the
transformation. Instead, we include the following information
 
\begin{code}
data CpsCtx g g' where
  
  CpsStart  :: CpsCtx Nil Nil
  -- Empty context

  CpsLamE   :: Sing t1 -> proxy t2 -> CpsCtx g g'
            -> CpsCtx (t1 : g) (ContTy t2 : CpsTy t1 : g')
  -- Context in the body of LamE. The input has the type
  -- of the parameter and the output has both its converted
  -- type and a continuation. 

  CpsTyLam  :: Sing t1 -> CpsCtx g g'
            -> CpsCtx g (ContTy t1 : g')
  -- Context in the body of a TyLam. The output includes
  -- a continuation for the polymorphic term.

  CpsMetaE   :: Sing t1 -> CpsCtx g g'
            -> CpsCtx (t1 : g) (CpsTy t1  : g')
  -- Context in the body of Meta. The input has the type
  -- of the parameter and the output has the converted type.
            
\end{code}

We use this data structure when transforming expression variables. We need to
convert the input variable of the correct type in the input context to be
appropriate for the output context, with the converted type.

\begin{code}
cpsVar :: CpsCtx g g' -> Var g t -> Var g' (CpsTy t)
cpsVar CpsStart v = case v of {}
cpsVar (CpsLamE t1 t2 gg) (V SZ)      =  V (SS SZ)
cpsVar (CpsLamE t1 t2 gg) (V (SS v))  =
  case cpsVar gg (V v) of
    V v' -> V (SS (SS v'))
cpsVar (CpsTyLam t1 gg)   v           =
  case cpsVar gg v of
    V v' -> V (SS v')
cpsVar (CpsMetaE t1 gg)    (V SZ)      =  V SZ
cpsVar (CpsMetaE t1 gg)    (V (SS v))  =
  case cpsVar gg (V v) of
    V v' -> V (SS v')
\end{code}

Furthermore, the CPS transformation needs information about the types of
sub-expressions during the transformation so that it can annotate the output
with the appropriate types for the introduced continuations. We can use
`typeOf` above to find these types as long as we know the context.  (NOTE:
this is inefficient. Can we pass this type information into the program? But
then how to reconstruct it in an application? Maybe CPS should be
bidirectional...)

\begin{code}
cpsExp :: forall t g g'.
          CpsCtx g g' 
       -> Exp g t
       -> Cont g' (CpsTy t) 
       -> Exp g' VoidTy
cpsExp g (VarE v)      k =
  case cpsVar g (V v) of
         V v' -> applyCont k (VarE v')
cpsExp g BaseE         k =
  applyCont k BaseE
cpsExp g (LamE t1 e1)  k =
  case typeOf (fstCtx g) (LamE t1 e1) of
   (SFnTy _t1 t2) ->
      let
        e'  = LamE (sCpsTy t1)
               $ LamE (sContTy t2)
                 $ cpsExp (CpsLamE t1 t2 g) e1 k'

        k'  = Obj $ VarE SZ

      in
        applyCont k e'    
cpsExp g (TyLam n e) k   = 
  case typeOf (fstCtx g) (TyLam n e) of
    SPolyTy _n t1 -> 
      applyCont k
      $ TyLam n 
      $ LamE (sContTy t1) 
      $ cpsExp (CpsTyLam t1
                (sIncCpsCtx n g)) e (Obj $ VarE SZ)
 
cpsExp g (AppE e1 e2)  k =
  case typeOf (fstCtx g) e1 of
   (SFnTy (t1 :: Sing t1) (t2 :: Sing t2)) ->
     let
        
        k1 :: Cont g' (CpsTy (FnTy t1 t2))
        k1 = Meta $ cpsExp (CpsMetaE (SFnTy t1 t2) g)
                       (substE IncE e2) k2

        k2 :: Cont (CpsTy (FnTy t1 t2) ': g') (CpsTy t1)
        k2 =  Meta $ AppE (AppE (VarE (SS SZ)) (VarE SZ))
               (reifyCont (sCpsTy t2)
                (substCont IncE (substCont IncE k)))

     in
       cpsExp g e1 k1
 
cpsExp (g :: CpsCtx g g') (TyApp e1 (tys :: Sing tys)) k =
  case typeOf (fstCtx g) e1 of
    SPolyTy (n :: Sing n) (t1 :: Sing t1)
      | Refl <- cpsCommutes2 @tys @t1
      , Refl <- cpsLength @tys
      ->
      let 
          k1 :: Cont g' (CpsTy (PolyTy n t1))
          k1 = Meta $ AppE (TyApp (VarE SZ)
                             (sCpsList tys)) (reifyCont t1' k2)

          k2 :: Cont (CpsTy (PolyTy n t1) ': g') 
                     (Subst (FromList (CpsList tys)) (CpsTy t1))
          k2 = substCont IncE k

          t1' :: Sing (Subst (FromList (CpsList tys))  (CpsTy t1))
          t1' = sSubst (sFromList (sCpsList tys)) (sCpsTy t1)
      in
        cpsExp g e1 k1
\end{code}

\begin{code}
cpsCommutes :: forall n ty.
               CpsTy (Subst (Inc n) ty) :~: Subst (Inc n) (CpsTy ty)
cpsCommutes = unsafeCoerce Refl

cps_commutes n ty =
  cpsTy (subst (Inc n) ty) == subst (Inc n) (cpsTy ty)

cpsCommutes2 :: forall tys ty.
               CpsTy (Subst (FromList tys) ty) :~:
               Subst (FromList (CpsList tys)) (CpsTy ty)
cpsCommutes2 = unsafeCoerce Refl

cps_commutes2 tys ty =
  cpsTy (subst (fromList tys) ty) ==
  subst (fromList (cpsList tys)) (cpsTy ty)

cpsLength :: forall tys. Length tys :~: Length (CpsList tys)
cpsLength = unsafeCoerce Refl

cps_length tys =
  length tys == length (cpsList tys)
  
\end{code}



\begin{code}
sIncCpsCtx  :: forall n g g'.
              Sing n
            -> CpsCtx g g'
            -> CpsCtx (IncList n g) (IncList n g')
sIncCpsCtx n CpsStart = CpsStart
sIncCpsCtx n (CpsLamE (t1 :: Sing t1) (t2 :: p t2) g)
  | Refl <- cpsCommutes @n @t1
  , Refl <- cpsCommutes @n @t2
  = CpsLamE (sSubst (SInc n) t1)
     (Proxy :: Proxy (Subst (Inc n) t2)) (sIncCpsCtx n g)
sIncCpsCtx n (CpsMetaE (t1 :: Sing t1) g)
  | Refl <- cpsCommutes @n @t1
  = CpsMetaE (sSubst (SInc n) t1) (sIncCpsCtx n g)
sIncCpsCtx n (CpsTyLam (t1 :: Sing t1) g)
  | Refl <- cpsCommutes @n @t1
  = CpsTyLam (sSubst (SInc n) t1) (sIncCpsCtx n g)
  
fstCtx :: CpsCtx g g' -> Sing g
fstCtx CpsStart = SNil
fstCtx (CpsLamE t1 t2 g) = SCons t1 (fstCtx g)
fstCtx (CpsMetaE t1 g)    = SCons t1 (fstCtx g)
fstCtx (CpsTyLam t1 g)   = fstCtx g
\end{code}
