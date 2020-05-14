\begin{code}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE AllowAmbiguousTypes #-}

module RegInterp where

import Prelude hiding ((!!),(>>),drop,take,length)
import Test.QuickCheck hiding ((===))
import Data.Singletons
import Data.Singletons.Prelude
   hiding (Drop,Take,Length,
          sDrop,sTake,sLength,
          DropSym0,DropSym1,DropSym2,
          TakeSym0,TakeSym1,TakeSym2)

import Data.Singletons.TH
   hiding (Drop,Take,Length,
          sDrop,sTake,sLength,
          DropSym0,DropSym1,DropSym2,
          TakeSym0,TakeSym1,TakeSym2)

import Data.Kind(Type)

import Data.Type.Equality

import Debug.Trace
import Nat
import SysF
\end{code}

\subsection{Regular Interpretation}

A \emph{regular substitution} is one of the form

  | t1 :· t2 :· .. :· tk :· Inc n |

that is, a finite sequence of types followed by |Inc n|, for some |n|.

All ground substitutions are equivalent to regular substitutions.  We
represent a regular substitution by the list of types and the amount to
increment at the end.

\begin{code}
data RSub = Reg [Ty] Nat deriving (Eq,Show)

-- indexing is just looking up one of the types or
-- shifting by the appropriate amount
instance Index RSub where
  type Element RSub = Ty
  (Reg ts n) !! x = if x < length ts then
                      ts !! x 
                   else VarTy (n + (x - length ts))

-- We can convert to/from regular substitutions
fromReg :: RSub -> Sub
fromReg (Reg []     x) = Inc x
fromReg (Reg (t:ts) x) = t :· fromReg (Reg ts x)

toReg :: Sub -> RSub
toReg (Inc n)  = Reg [] n
toReg (x :· y)    = Reg (x : xs) n
  where Reg xs n  = toReg y
--toReg (Lift n s) = toReg (liftDef n s)
toReg (s1 :∘ s2) = compReg (toReg s1) (toReg s2)

-- Compose two regular substitutions
compReg :: RSub -> RSub -> RSub
compReg (Reg [] Z) r2
  = r2
compReg (Reg [] xn)    (Reg [] yn)
  = Reg [] (yn + xn)
compReg (Reg [] (S n)) (Reg (y:ys) yn)
  = compReg (Reg [] n) (Reg ys yn)
compReg (Reg (x:xs) xn) r2
  = Reg (x':xs') xn'
     where 
        x'  = subst (fromReg r2) x
        Reg xs' xn' = compReg (Reg xs xn) r2

prop_fromReg rs x = rs !! x == fromReg rs !! x
prop_toReg s x = s !! x == toReg s !! x
prop_compReg r1 r2 x =
  compReg r1 r2 !! x == (fromReg r1 :∘ fromReg r2) !! x


-- Note: just comparing regular forms isn't coarse enough.
-- We could have an "index" in the tail of the list of types.
-- We need to get rid of them somehow
-- But we can still get a derivable, but inefficient equivalence algorithm

eqSubst s1 s2 = all (\k -> r1 !! k == r2 !! k) [0 .. m]
  where
     r1 = toReg s1
     r2 = toReg s2
     m  = max (extent r1) (extent r2)

extent :: RSub -> Nat
extent (Reg ts _) = length ts


-- Question: do we need a type for regular substitutions?
-- can we just use this for "simplifying" substitutions instead?
\end{code}
%endif

\subsection{Axiomatization for substitutions}

Sh\"afer et al. give eight axioms about the equivalence of substitions.  The
first follow directly from our definition of |subst| above.

\begin{code}
(===) :: Sub -> Sub -> Property
s1 === s2 = forAll arbitrary $ \x -> applys s1 x == applys s2 x
\end{code}


The remainder are extensional equalities about substitutions:
\begin{code}
-- IdL
prop_IdL s =
  (Inc Z :∘ s) === s 
  
prop_ShiftCons n t s =
  (Inc (S n) :∘ (t :· s)) === (Inc n :∘ s) 

prop_IdR s =
  (s :∘ Inc Z) === s

prop_Ass s1 s2 s3 =
  ((s1 :∘ s2) :∘ s3) === (s1  :∘ (s2 :∘ s3))

prop_Map t s1 s2 =
  ((t :· s1) :∘ s2) === ((subst s2 t) :· (s1 :∘ s2))

-- New for this representation
prop_Plus m n = 
   (Inc m :∘ Inc n) === Inc (n + m)
\end{code}


\subsection{Making these identities available to Haskell}

Even if we just assume these equivalences as axioms, what is the
best way to make them useful for programming?

Option 1: 
\begin{code}
ax_Shift0 :: forall s t. Subst (Inc Z :∘ s) t :~: Subst s t
ax_Shift0 = unsafeCoerce Refl

ax_ShiftCons :: forall n t1 s t.
  Subst (Inc (S n) :∘ (t1 :· s)) t :~: Subst (Inc n :∘ s) t
ax_ShiftCons = unsafeCoerce Refl

ax_SubstList :: forall s1 s2 ts.
  (forall t. Subst s1 t :~: Subst s2 t) ->
  SubstList s1 ts :~: SubstList s1 ts
ax_SubstList _ = unsafeCoerce Refl
\end{code}


%if False
Option 2: Simplification?

Unfortunately, we cannot normalize terms containing substitution expressions
because we don't have "explicit" substitutions. In otherwords we cannot write
type-level functions that dispatch on what substitutions have been applied to
|Ty| expressions.

It's actually a good thing that we can't do that because we want to have
unique forms for types. 

Also, writing a substitution simplification function that we can
promote is a PITA.

We have to write out the 5*5 cases in the composition branch. Ugh.

\begin{code}
-- Simplifications
$(singletons [d|
    asimpl :: Sub -> Sub

    asimpl (t :· s)       = (t :· asimpl s)  
               
    asimpl (Inc  n)       = Inc n               

    asimpl (s1 :∘ s2)     =
        case (asimpl s1, asimpl s2) of
             -- IdL
             (Inc Z , s2') -> s2'

             -- Plus
             (Inc (S n), Inc m) -> Inc (S (plus n m))
        
             -- ShiftCons
             (Inc (S n), (t :· s)) -> asimpl (Inc n :∘ s)

             -- (no change)
             (s1'@(Inc (S n)), s2'@(_ :∘ _)) -> (s1' :∘ s2')

             -- Map
             ((t1 :· s1'), s2') -> asimpl ((subst s2' t1) :· (s1' :∘ s2'))
             
             -- Assoc
             ((s11 :∘ s12), s2') -> asimpl (s11 :∘ (s12 :∘ s2'))

    |])
  
prop_asimpl s = s === asimpl s


--ax_Asimpl :: forall s t. Subst s t :~: Subst (Asimpl s) t
--ax_Asimpl = unsafeCoerce Refl
\end{code}

\paragraph{Interlude: Lemmas from autosubst}

In this representation,
substitutions are usually defined as functions from (natural number) indices
to types. This makes sense, in general, because these substitutions are
"infinite" --- they apply to all type indices.

However, in Haskell, we want to work with these substitutions at the type
level, which does not include type-level lambda expressions. Here, it is
difficult to define the appropriate substitutions.

Therefore, we use the following datatype as a ``defunctionalized'' version of
substitions and substitution-producing operations.\footnote{Like the explicit
substitutions of Abadi et al.}


We could have also let the singletons library take care of the
defunctionalization for us. But that might be even more difficult to work
with.


NOTE: autosubst notation
|IdSub|        is  |ids|
|ConsSub t s|  is  |t .: s|
|Lift 1 s|  is  |up s|
|Inc 1|     is  |ren (+1)|
|CompSub s1 s2| is |s1 >> s2|

The substitution "up σ" is equal to
Var 0 .: (σ >> ren (+1)) where (+1) is the renaming increasing every variable by
one and .: is the stream-cons operator.

%endif

The autosubst library automatically generates four substitution lemmas.
\cite{autosubst-manual}. One of these lemmas states that renaming is equal to
substitution, so is not pertinent in this context.

However, we can translate the remaining three lemmas to this framework:

\begin{spec}
subst_comp : forall t s1 s2. subst s2 (subst s1 t) = subst (s1 >> s2) t
subst_id   : forall t. subst IdSub t = t
id_subst   : forall x t. subst s (IdSub !! x) = s !! x
\end{spec}

About subst\_comp: ``This property is essential and surprisingly difficult to
show if done manually.''



\begin{code}
prop_subst_comp s1 s2 t =
  subst (s1 :∘ s2) t == subst s2 (subst s1 t)
\end{code}

\begin{code}
prop_subst_id t = subst (Inc Z) t == t
\end{code}

Not sure I see the point in this one.
\begin{code}
prop_id_subst s x = subst s (Inc Z !! x) == s !! x
\end{code}


\begin{code}
instance Arbitrary RSub where
  arbitrary = Reg <$> arbitrary <*> arbitrary
  shrink (Reg t x) = [Reg t' x' | t' <- shrink t, x' <- shrink x]
\end{code}
