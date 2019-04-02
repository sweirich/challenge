
\documentclass[sigplan,10pt,review,anonymous]{acmart}
\settopmatter{printfolios=true,printccs=false,printacmref=false}

\acmConference[PL'18]{ACM SIGPLAN Conference on Programming Languages}{January 01--03, 2018}{New York, NY, USA}
\acmYear{2018}
\acmISBN{} % \acmISBN{978-x-xxxx-xxxx-x/YY/MM}
\acmDOI{} % \acmDOI{10.1145/nnnnnnn.nnnnnnn}
\startPage{1}

\setcopyright{none}
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\copyrightyear{2018}           %% If different from \acmYear

\bibliographystyle{ACM-Reference-Format}
%% Citation style
%\citestyle{acmauthoryear}  %% For author/year citations

%include polycode.fmt

%% Some recommended packages.
\usepackage{booktabs}   %% For formal tables:
                        %% http://ctan.org/pkg/booktabs
\usepackage{subcaption} %% For complex figures with subfigures/subcaptions
                        %% http://ctan.org/pkg/subcaption


\begin{document}

%% Title information
\title{Intrinsic polymorphism in Dependent Haskell}
%% Author with single affiliation.
\author{Stephanie Weirich}
\orcid{nnnn-nnnn-nnnn-nnnn}             %% \orcid is optional
\affiliation{
  \position{Professor}
  \department{Computer and Information Science}              %% \department is recommended
  \institution{University of Pennsylvania}            %% \institution is required
  \streetaddress{Street1 Address1}
  \city{City1}
  \state{State1}
  \postcode{Post-Code1}
  \country{Country1}                    %% \country is recommended
}
\email{sweirichcis.upenn.edu}          %% \email is recommended

\begin{abstract}
Text of abstract \ldots.
\end{abstract}


\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011008</concept_id>
<concept_desc>Software and its engineering~General programming languages</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10003456.10003457.10003521.10003525</concept_id>
<concept_desc>Social and professional topics~History of programming languages</concept_desc>
<concept_significance>300</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~General programming languages}
\ccsdesc[300]{Social and professional topics~History of programming languages}
%% End of generated code


%% Keywords
%% comma separated list
\keywords{keyword1, keyword2, keyword3}  %% \keywords are mandatory in final camera-ready submission


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle

\section{Introduction}

%if False
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

{-# OPTIONS_GHC -fwarn-incomplete-patterns -Wno-redundant-constraints #-}
module SysF where

import Prelude hiding ((!!),(>>))
import Test.QuickCheck
import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Kind(Type)

import Data.Type.Equality

import Debug.Trace
\end{code}
%endif

Let's get this out of the way early:
\begin{code}
import Unsafe.Coerce
\end{code}

This paper is a literate Haskell example of a strongly-typed representation of
System F. In other words, the datatype only includes well typed System F
terms.

Although strongly-typed ASTs are common examples for programming with GADTs,
this paper goes a bit further. On one hand, it uses a deep embedding types ---
our AST will be indexed by members of a Haskell datatype, called |Ty| instead
of actual Haskell types (of kind |Type|), the usual shallow embedding of
types.

Furthermore, this representation includes polymorphic types, which is an
uncommon example for a strongly-typed embedding (in Haskell).

We will use deBruijn indices, with explicit substitutions to represent type
variables in System F.

Why are we doing this:
\begin{enumerate}
  \item Demonstrate what is possible for intrinsic type representations
    in Haskell now.
  \item Compare capabilties with Coq and Agda
  \item Polymorphism is particularly tricky and not well represented in
    Haskell literature
\end{enumerate}

Comparison: better than Coq/Agda
\begin{enumerate}
  \item No termination proof required. Significantly simpler definition
    of substitution
  \item "Extensional"-like treatment of equality. (Does this show up
    anywhere???)
\end{enumerate}

Comparison: worse than Coq/Agda
\begin{enumerate}
  \item No proofs! Have to use unsafeCoerce. Confidence through testing
    (or proofs on paper/another system).
  \item No native type-level lambdas. Had to be clever and "defunctionalize"
    the representation of substitution.
  \item Ecosystem not designed for TypeInType (i.e. singletons!). So,
    cunningly selected version that did not index kinds, only indexed types.
\end{enumerate}


Discussion: Should we make the type indices more strongly typed?

Yes: earlier bug finding, tighter interface

No: it's all statically checked anyways, less support from singletons
    needs TypeInType, more proofs required


Question: Why use parallel substitutions vs. "standard DB"? Is one
easier to understand than the other? How do they compare?

Other issues: de Bruijn indices are terrible for efficiencies.  See Francois'
paper for alternative representation.  Even with pure functional programming,
the representation that is the easiest to verify may not be the one that is
the fastest.

Key ideas of Francois's paper --- use deBruijn levels instead.

But: what if we add "weakening" constructors to the expression datatype?  This
is an easy way to regain some efficiency. With less cost because we don't have
to prove our term translations are correct.

\subsection{Preliminaries}

First, a datatype for indices themselves --- natural numbers.
For simplicity, we will display natural numbers as Ints.
Eventually, we will move this code into another file as it is
fairly boring. Would be good to have a run-time representation
with "Int" (like PeanoRepr).

%if False
\begin{code}
$(singletons [d|
    data Nat = Z | S Nat deriving (Eq, Ord)

    addNat :: Nat -> Nat -> Nat
    addNat Z     x = x
    addNat (S y) x  = S (addNat y x)

    mulNat :: Nat -> Nat -> Nat
    mulNat Z     x = Z
    mulNat (S y) x = addNat x (mulNat y x)

    subNat :: Nat -> Nat -> Nat
    subNat x     Z = x
    subNat (S x) (S y) = subNat x y

    applyN :: Nat -> (a -> a) -> a -> a
    applyN Z     f x = x
    applyN (S n) f x = f (applyN n f x)

    natLength :: [a] -> Nat
    natLength [] = Z
    natLength (_:xs) = S (natLength xs)

    -- safe indexing operation
    natIdx :: [a] -> Nat -> Maybe a
    natIdx (x:_)  Z     = Just x
    natIdx (_:xs)(S n)  = natIdx xs n
    natIdx []    n      = Nothing

    dropNat :: Nat -> [a] -> [a]
    dropNat Z xs          = xs
    dropNat (S n) (_:xs)  = dropNat n xs
    dropNat n     []      = []                           
 
    |])

instance Num Nat where
  fromInteger 0 = Z
  fromInteger n | n < 0 = error "CANNOT represent negative numbers"
  fromInteger n = S (fromInteger (n - 1))

  (+) = addNat
  (*) = mulNat
  (-) = subNat

  negate x = error "Negative number"
  abs x    = x
  signum Z = 0
  signum x = 1

instance Enum Nat where
  toEnum :: Int -> Nat
  toEnum = fromInteger . toInteger
  fromEnum :: Nat -> Int
  fromEnum = natToInt

natToInt :: Nat -> Int
natToInt Z = 0
natToInt (S m) = 1 + natToInt m

instance Show Nat where
  show = show . natToInt

class Index a where
  type Element a
  (!!) :: a -> Nat -> Element a

instance Index [a] where
  type Element [a] = a
  (x:_)   !!  Z     = x
  (_:xs)  !! (S n)  = xs !! n
  []      !! n      = error "(!!): too few elements in index"

  
\end{code}
%endif

\section{Type representation}

Below, our datatype for types. Type variables are represented
by indices (i.e. natural numbers). 

\begin{code}
$(singletons [d|
    data Ty =
         BaseTy
      |  VarTy Nat
      |  FnTy Ty Ty
      |  PolyTy Nat Ty        -- forall {a,b}. a -> b
                              -- PolyTy 2 (FnTy (VarTy 0) (VarTy 1))
         deriving (Eq,Show)
    |])
\end{code}

For example, the type |forall a b. a -> b| is represented by the AST |PolyTy 2
(FnTy (VarTy 0) (VarTy 1))|.

Now, the representation of substitutions. In this representation,
substitutions are usually defined as functions from (natural number) indices
to types. This makes sense, in general, because these substitutions are
"infinite" --- they apply to all type indices.

However, in Haskell, we want to work with these substitutions at the type
level, which does not include type-level lambda expressions. Here, it is
difficult to define the appropriate substitutions.

Therefore, we use the following datatype as a "defunctionalized" version of
substitions and substitution-producing operations.\footnote{Like the explicit
substitutions of Abadi et al.}

We could have also let the singletons library take care of the
defunctionalization for us. But that might be even more difficult to work
with.

\begin{code}
$(singletons [d|
    data Sub = 
        IdSub              -- ^ identity 
     |  Ty  :· Sub         -- ^ cons
     |  IncSub Nat         -- ^ increment
     |  Sub :∘  Sub        -- ^ composition
     |  LiftSub Nat Sub    -- ^ shift sub under a binder
        deriving (Eq, Show)

    infixr :·    -- like usual cons operator (:)
    infixr :∘    -- like usual composition  (.)
    |])

-- infix notation
(>>) = (:∘)
\end{code}


We can understand these substitutions by looking at their behavior on
type variables (the function |applys| below).

\begin{itemize}
\item |IdSub| - the identity substitution. When used during substitution,
    maps all type variables to themselves.
\item |ty :· s| - extends a substitution by adding a new definition for
    index 0 and shifting everything in |s| one step to the right.
\item |IncSub n| - increment all variables by |n|.
  Sometimes written as |(+n)| or  $\uparrow^{n}$
\item |s2 :∘ s1| - composition
\item |LiftSub n s| - shift a substitution in preparation
  to go under a binder, definable in terms of the previous three
\end{itemize}

Quotation from Pottier:
"In short, ↑i t is the term obtained by adding i to every variable that
appears free in the term t. The symbol ↑i can be intuitively read as an
end-of-scope mark: it means that the i most-recently-introduced variables are
not in scope in the term that follows (Bird and Paterson, 1999, Hendriks and
van Oostrom, 2003)."

Usually the increment operator only works one at a time. But we choose to
allow a primitive n-ary increment operation. 

The `subst` operation then extends the substitution for a single index
throughout the type structure. When this function calls itself recursively
under a binder, it uses `lift` to modify the input substitution.
In particular |LiftSub| is exactly what we need when we go under a binder.
With |LiftSub k s|, the indices |0..k-1| are left alone, and
the free variables in the range of |s| are all incremented by |k|.

\begin{code}
$(singletons [d|
              

    -- the value of the de Bruijn index i in the substitution s
    -- also written as "s !! i"               
    applys :: Sub -> Nat -> Ty
    applys IdSub       x = VarTy x
    applys (e :· s)    x = case x of
                            Z      -> e
                            (S m)  -> applys s m
    applys (IncSub n)  x = VarTy (addNat n x)
    applys (s1 :∘ s2)  x = subst s2 (applys s1 x)
    applys (LiftSub n s) x = if x < n 
                             then VarTy x
                             else inc n (applys s (subNat x n))


    -- apply a substitution to a type
    subst :: Sub -> Ty -> Ty
    subst s BaseTy        = BaseTy
    subst s (VarTy x)     = applys s x
    subst s (FnTy a r)    = FnTy (subst s a) (subst s r)
    subst s (PolyTy n a)  = PolyTy n (lift n s a)

    -- apply an increment substitution  (\uparrow^n)
    inc :: Nat -> Ty -> Ty
    inc n = subst (IncSub n)

    -- apply a lift substitution (\Uparrow^n)
    lift :: Nat -> Sub -> Ty -> Ty
    lift n s = subst (LiftSub n s)

    |])

instance Index Sub where
  type Element Sub = Ty
  s !! x = applys s x

\end{code}

Even though the singletons library allows us to use higher-order functions,
like |map| it is not always convenient to do so. For ease, we define names
for some common maps that we will need later. These names make it easy for
us to refer to these operations later.

\begin{code}
$(singletons [d|
              
    substList :: Sub -> [Ty] -> [Ty]
    substList s = map (subst s)                                

    incList :: Nat -> [Ty] -> [Ty]
    incList n = map (subst (IncSub n))
               
    liftList :: Nat -> Sub -> [Ty] -> [Ty]
    liftList n s = map (subst (LiftSub n s))

   |])
\end{code}

\subsection{Stream interpretation}

We can also visualize substitutions as infinite lists of types,
where the ith type in the list is the substitution for variable i.

\begin{code}
toList :: Sub -> [Ty]
toList IdSub         = VarTy <$> [0, 1 ..]
toList (x :· y)      = x : toList y
toList (IncSub n)    = VarTy <$> enumFrom n
toList (s1 :∘ s2)    = substList s2 (toList s1)
toList (LiftSub Z s) = toList IdSub
toList (LiftSub (S n) s) =
  (VarTy <$> [0, 1 .. n]) <> toList (s :∘ IncSub (S n))

\end{code}

We can express the connection between the two interpretations of substitutions
using the following quickCheck property.  In other words, at any index |n|, the
result of |applys| is the same as first converting the substitution to a list
and then accessing the |n|th element.

\begin{code}
prop_applys_toList :: Sub -> Nat -> Bool
prop_applys_toList s x =
  s !! x == toList s !! x
\end{code}

\subsection{Regular Interpretation}

A \emph{regular substitution} is one of the form

  | t1 :· t2 :· .. :· tk :· IncSub n |

that is, a finite sequence of types followed by |IncSub n|, for some |n|.

All ground substitutions are equivalent to regular substitutions. We should
be able to compute these things. 

\begin{code}
tailSub ::Sub -> Sub
tailSub s = (IncSub 1 :∘ s)

dropSub :: Nat -> Sub -> Sub
dropSub n s = (IncSub n :∘ s)

prop_drop_inc n x =
  dropSub n (IncSub 1) !! x == IncSub (S n) !! x


liftSub :: Nat -> Sub -> Sub
liftSub n s = go n (s :∘ IncSub n) where
        go Z      s = s
        go (S m)  s = go m (VarTy m :· s)
\end{code}

We represent a regular substitution by the list of types
and the amount to increment at the end.

\begin{code}
data RSub = Reg [Ty] Nat deriving (Eq,Show)

-- indexing is just looking up one of the types or
-- shifting by the appropriate amount
instance Index RSub where
  type Element RSub = Ty
  (Reg ts n) !! x = if x < natLength ts then
                      ts !! x 
                   else VarTy (n + (x - natLength ts))

-- We can convert to/from regular substitutions
fromReg :: RSub -> Sub
fromReg (Reg []     x) = IncSub x
fromReg (Reg (t:ts) x) = t :· fromReg (Reg ts x)

toReg :: Sub -> RSub
toReg IdSub       = Reg [] 0
toReg (IncSub n)  = Reg [] n
toReg (x :· y)    = Reg (x : xs) n
  where Reg xs n  = toReg y
toReg (LiftSub n s) = toReg (liftSub n s)
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
-- here

eqSubst s1 s2 = all (\k -> r1 !! k == r2 !! k) [0 .. m]
  where
     r1 = toReg s1
     r2 = toReg s2
     m  = max (extent r1) (extent r2)

extent :: RSub -> Nat
extent (Reg ts _) = natLength ts


-- Question: do we need a type for regular substitutions?
-- can we just use this for "simplifying" substitutions instead?
\end{code}


\subsection{Properties}

Two of the five primitive substitution forms are actually derivable in terms
of the other three.

In fact, there are many ways to write the identity substitution:
\begin{code}
prop_IdSub_def0 n =
  IdSub !! n    == IncSub 0 !! n
prop_IdSub_def1 n =
  IdSub !! n    == (VarTy 0 :· IncSub 1) !! n
prop_IdSub_def2 n =
  IdSub !! n    == (VarTy 0 :· VarTy 1 :· IncSub 2) !! n
prop_IdSub_def3 n =
  IdSub !! n    == (VarTy 0 :· VarTy 1 :· VarTy 2 :· IncSub 3) !! n
\end{code}

Lifting also follows a similar pattern.

\begin{code}
prop_LiftSub0 s x =
  LiftSub 0 s !! x == (s :∘ IncSub 0) !! x
prop_LiftSub1 s x =
  LiftSub 1 s !! x == (VarTy 0 :· (s :∘ IncSub 1)) !! x
prop_LiftSub2 s x =
  LiftSub 2 s !! x == (VarTy 0 :· VarTy 1 :· (s :∘ IncSub 2)) !! x

-- more generally
prop_LiftSub_def k s x =
  LiftSub k s !! x == liftSub k s !! x
\end{code}

\subsection{Axiomatization for substitutions}

Shaefer et al give eight axioms about the equivalence of substitions.
The first follow directly from our definition of |subst| above.

The remainder are extensional equalities about substitutions:
\begin{code}
prop_Shift0 s x =
  (IncSub Z :∘ s) !! x == s !! x
  
prop_ShiftCons n t s x =
  (IncSub (S n) :∘ (t :· s)) !! x == (IncSub n :∘ s) !! x

prop_IdL s x =
  (IdSub :∘ s) !! x == s !! x

prop_IdR s x =
  (s :∘ IdSub) !! x == s !! x

prop_Ass s1 s2 s3 x =
  ((s1 :∘ s2) :∘ s3) !! x == (s1  :∘ (s2 :∘ s3)) !! x

prop_Map t s1 s2 x =
  ((t :· s1) :∘ s2) !! x == ((subst s2 t) :· (s1 :∘ s2)) !! x

\end{code}

\subsection{Simplification}

Unfortunately, we cannot normalize terms containing substitution expressions
because we don't have "explicit" substitutions. In otherwords we cannot write
type-level functions that dispatch on what substitutions have been applied to
|Ty| expressions.

It's actually a good thing that we can't do that because we want to have
unique forms for types. 

\begin{code}
-- Simplifications
asimpl :: Sub -> Sub
-- IdL 
asimpl (IdSub :∘ s) = s
-- IdR
asimpl (s :∘ IdSub) = s
-- ShiftCons
asimpl (IncSub Z     :∘ s)        = asimpl s
asimpl (IncSub (S n) :∘ (t :· s)) = asimpl (IncSub n :∘s)
-- Map
asimpl ((t :· s1) :∘ s2) =
  (subst s2 t) :· (asimpl (s1 :∘ s2))
-- Ass  
asimpl ((s1 :∘ s2) :∘ s3) =
  s1  :∘ (asimpl (s2 :∘ s3))
  
-- VarShift (how to generalize?)
asimpl (VarTy 0 :· IncSub 1) = IdSub
asimpl (VarTy 0 :· VarTy 1 :· IncSub 2) = IdSub

-- New for n-ary Inc
asimpl (IncSub 0) = IdSub
asimpl (IncSub n :∘ IncSub k) = IncSub (n + k)

asimpl s = s

prop_asimpl s n = s !! n == asimpl s !! n 
\end{code}

\paragraph{Interlude: Lemmas from autosubst}

NOTE: autosubst notation
|IdSub|        is  |ids|
|ConsSub t s|  is  |t .: s|
|LiftSub 1 s|  is  |up s|
|IncSub 1|     is  |ren (+1)|
|CompSub s1 s2| is |s1 >> s2|

The substitution "up σ" is equal to
Var 0 .: (σ >> ren (+1)) where (+1) is the renaming increasing every variable by
one and .: is the stream-cons operator.


The autosubst library automatically generates four substitution lemmas.
\cite{autosubst-manual}. One of these lemmas states that renaming
is equal to substitution, so is not pertinent in this context.

However, we can translate the remaining three lemmas to this framework:

\begin{spec}
subst_comp : forall t s1 s2. subst s2 (subst s1 t) = subst (s1 >> s2) t
subst_id   : forall t. subst IdSub t = t
id_subst   : forall x t. subst s (IdSub !! x) = s !! x
\end{spec}

About subst_comp: "This property is essential and surprisingly difficult to
show if done manually."

\begin{code}
prop_subst_id t = subst IdSub t == t
\end{code}

\section{Terms and types}

Now, in this section, use the promoted, quantified types to develop an
intrinsically-typed version of System F.

Before we do so, we need two additional operations on substitutions.

First, we need a way to interpret a list of types as a substitution,
where the first element of the list is the substition for TyVar 0,
etc. We do so, with the following unremarkable function.

\begin{code}
$(singletons [d|
  fromList :: [Ty] -> Sub
  fromList = foldr (:·) IdSub
  |])
\end{code}

\begin{code}
prop_toList_fromList tys =
  take (length tys) (toList (fromList tys)) == tys
\end{code}

Second, we give a name to the operation of mapping the increment operation
across a list of types.

\begin{code}
$(singletons [d|
   |])
\end{code}

With these two operations, we can define the GADTs for terms, indexed by a
context (i.e. list of types for the free variables of the term) and the type
of the term.

The `Sing a` type, defined in the singletons library, indicates the use of
dependent types. These are arguments that are used both as data (so must be
args to the data constructors) but also must appear later in the type. For 


In this term, the `TyLam` operation has to increment all of the type variables
in the context `g` by `k`, the number of type binders.  In the `TyApp` case,
we need to know that the number of binders in the polymorphic function matches
the number of type arguments. We then turn the type arguments into a
substitution which we use to calculate the result type.

\begin{code}

data Var :: [Ty] -> Ty -> Type where
  VZ  :: Var (ty:g) ty
  VS  :: Var g ty -> Var (ty1:g) ty

data Exp :: [Ty] -> Ty -> Type where
  
  EBase  :: Exp g BaseTy
  
  EVar   :: Var g ty
         -> Exp g ty
         
  ELam   :: Sing ty1
         -> Exp (ty1:g) ty2
         -> Exp g (FnTy ty1 ty2)
         
  EApp   :: Exp g (FnTy ty1 ty2)
         -> Exp g ty1
         -> Exp g ty2
  
  TyLam  :: Sing k
         -> Exp (IncList k g) ty
         -> Exp g (PolyTy k ty)
         
  TyApp  :: (k ~ NatLength tys)
         => Exp g (PolyTy k ty)
         -> Sing tys
         -> Exp g (Subst (FromList tys) ty)
         
\end{code}

For example, we can type check the polymorphic identity function:

\begin{code}
$(singletons [d|
     sid :: Ty
     sid = (PolyTy (S Z) (FnTy (VarTy Z) (VarTy Z)))
 |])

pid :: Exp '[] Sid
pid = TyLam (SS SZ) (ELam (SVarTy SZ) (EVar VZ))

pidpid :: Exp '[] Sid
pidpid = EApp (TyApp pid (SCons sSid SNil)) pid
\end{code}


\subsection{Substituting terms in types}

The next step is to define the operation of type substitution in terms.

Again, we name some operations that we would like to use with type contexts.




In this definition, instead of using the simply-typed version of these operations,
we need to use some Singletons to capture the dependency. For example, the operation

\begin{spec}
sSubst :: Sing s -> Sing ty -> Sing (Subst s ty)
\end{spec}

is the dependent version of `subst` above. i.e. the process of applying a substitution
to a type. We need to use this operation in the lambda case, because we need to substitute
in the type annotations.

\begin{code}
-- Substitute types in terms
substTy :: forall s g ty. Sing s -> Exp g ty -> Exp (SubstList s g) (Subst s ty)
substTy s EBase         = EBase
substTy s (EVar v)      = EVar (substVar @s v)
substTy s (ELam ty e)   = ELam (sSubst s ty) (substTy s e)
substTy s (EApp e1 e2)  = EApp (substTy s e1) (substTy s e2)
substTy s (TyLam k e)
  | Refl <- axiom_LiftIncList1 @g s k
  = TyLam k (substTy (SLiftSub k s) e)
  
substTy s (TyApp (e :: Exp g (PolyTy k ty1)) tys)
  | Refl <- typeEquality2 @ty1 s tys
  , Refl <- typeEquality3 @(SubstSym1 s) tys
  = TyApp (substTy s e) (sSubstList s tys)
\end{code}


In the first case of the function, we need to show that substituting through
variable lookups is type-sound.

\begin{code}
substVar :: forall s g ty. Var g ty -> Var (SubstList s g) (Subst s ty)
substVar VZ      = VZ
substVar (VS v)  = VS (substVar @s v)
\end{code}

Note that this function is more proof than code --- if you look at it, it is
just an identity function.  It is justified to replace the above with the
definition below, which has equivalent behavior.

\begin{spec}
substVar :: (Var g ty) -> Var (SubstList s g) (Subst s ty)
substVar v = unsafeCoerce v
\end{spec}

This is any example where, if we are not willing to use unsafeCoerce, we need
to pay a performance cost for the use of an intrinsic representation. The
intrinsic representation uses terms \emph{as proofs}.

This is not an issue with the fact that we are working in Haskell. Even in Coq
or Agda, we would face this dilemma. Indeed, there doesn't seem to be a way
out of this quandry without stepping out of the proof system.

Only Cedille's zero-cost conversions would be able to attack this issue. 
In that vein, perhaps Haskell could similarly support a way to derive the
fact that even though two terms have different types, they have the same runtime
representation. 

\begin{spec}
instance Coercible (Var g ty) (Var (SubstList s g) (Subst s ty)) where
  ...
substVar :: Sing s -> (Var g ty) -> Var (SubstList s g) (Subst s ty)
substVar s v = coerce v
\end{spec}

The last two branches of substTy requires more traditional proofs about type
equality.  (A version in Coq or Agda would also need to rely on these proofs.)

In the type abstraction case, we call the function recursively after shifting
the substitution by the number of binders in the abstraction.

we have

\begin{spec}
   substTy (SLiftSub k s) e ::
       Exp (SubstList (LiftSub k s) g) (Subst (LiftSub k s) ty)
\end{spec}

we want to produce a term of type

\begin{spec}
   Exp s (Subst s g) (Subst s (PolyTy k ty))
   ==
   Exp s (Subst s g) (PolyTy k (Subst (LiftSub k s) ty))
\end{spec}

we can do so with the TyLam, given a body of type

\begin{spec}
   Exp s (IncList k (Subst s g)) (Subst (LiftSub k s) ty)
\end{spec}

so the type of the body lines up. But we need a type equality between the
contexts.

\begin{code}
axiom_LiftInc :: forall g s k.
  Sing s -> Sing k -> Subst (LiftSub k s) (Subst (IncSub k) g)
  :~: Subst (IncSub k) (Subst s g)
axiom_LiftInc _ _ = unsafeCoerce Refl

axiom_LiftIncList1 :: forall g s k.
  Sing s -> Sing k -> LiftList k s (IncList k g) :~: IncList k (SubstList s g)
axiom_LiftIncList1 _ _ = unsafeCoerce Refl
\end{code}

Why is this equality justfied? Consider what happens in the case of some type variable
k1, that occurs in one type in the list. In this case, we need to show that 

  Subst (LiftSub k s) (Subst (IncSub k) (VarTy k1))  :~: Subst (IncSub k) (Subst s (VarTy k1))

So we have the following sequence of equalities connecting the left-hand-side with the
right-hand side.

\begin{spec}
   LHS  == Subst (LiftSub k s) (VarTy (AddNat k k1))
         {{ unfolding definitions }}
        == if (AddNat k k1) < k 
             then VarTy (AddNat k k1)
             else inc k s !! (subNat (AddNat k k1) k)
         {{ first case is impossible }}
        == inc k s !! (subNat (AddNat k k1) k)
         {{ arithmetic }}
        == inc k (s !! k1)
         {{ unfolding definitions }}
        == RHS
\end{spec}

We don't want to prove this equation in Haskell. That would impose a runtime
cost to our substitution function. Instead, we would like to declare this
property as an "axiom", one that we believe holds about the system.

We can gain confidence in the axiom in two ways. On one hand, we could try to
prove it on paper, or in an external tool, or in LiquidHaskell. However, it is
simpler to test it via quickCheck.  So, let's state it as a quickcheck
property.

\begin{code}
prop_LiftIncList1 :: [Ty] -> Sub -> Nat -> Bool
prop_LiftIncList1 g s k = liftList k s (incList k g) == incList k (substList s g)
\end{code}



\begin{code}
typeEquality2 :: forall ty1 s tys.
  Sing s -> Sing tys ->
  Subst (FromList (SubstList s tys))
    (Subst (LiftSub (NatLength tys) s) ty1)
     :~: 
  Subst s (Subst (FromList tys) ty1)
typeEquality2 _ _ = unsafeCoerce Refl

prop2 :: Ty -> Sub -> [Ty] -> Bool
prop2 ty1 s tys =
  subst (fromList (substList s tys))
    (lift (natLength tys) s ty1)
    ==
  subst s (subst (fromList tys) ty1)


typeEquality3 :: forall f tys.
  Sing tys ->
  NatLength (Map f tys) :~: NatLength tys
typeEquality3 _ = unsafeCoerce Refl

prop3 :: (a -> b) -> [a] -> Bool
prop3 f tys = natLength (map f tys) == natLength tys

\end{code}



\subsection{Term substitutions}

i.e. all this substitution stuff *again*, but more intrinsically typed. 


\begin{code}
data ESub g g' where
  EIdSub   :: ESub g g
  EConsSub :: Exp g' ty -> ESub g g' -> ESub (ty:g) g'
  ETailSub :: ESub (ty:g) g' -> ESub g g'
  EIncSub  :: ESub g (ty:g)
  ELiftSub :: ESub g g' -> ESub (ty:g) (ty:g')

----------------
applyESub :: ESub g g' -> Var g ty -> Exp g' ty
applyESub EIdSub         v = EVar v
applyESub (EConsSub e s) v = case v of
                                VZ -> e
                                VS m -> applyESub s m
applyESub (ETailSub s)   v = applyESub s (VS v)
applyESub EIncSub        v = EVar (VS v)
applyESub (ELiftSub s)   v = case v of
                                VZ -> EVar VZ
                                VS m -> substE EIncSub (applyESub s m)

---------------------

-- Composition of type-increment and term substitution.
-- Kinda nice that we have a concrete definition of term substitutions
-- to work from.
incESub :: Sing k -> ESub g g' -> ESub (IncList k g) (IncList k g')
incESub k EIdSub         = EIdSub
incESub k (EConsSub e s) = EConsSub (substTy (SIncSub k) e) (incESub k s)
incESub k (ETailSub s)   = ETailSub (incESub k s)
incESub k EIncSub        = EIncSub
incESub k (ELiftSub s)   = ELiftSub (incESub k s)

---------------------

substE :: ESub g g' -> Exp g ty -> Exp g' ty
substE s EBase         = EBase
substE s (EVar v)      = applyESub s v
substE s (EApp e1 e2)  = EApp (substE s e1) (substE s e2)
substE s (ELam ty e)   = ELam ty (substE (ELiftSub s) e)
substE s (TyLam k e)   = TyLam k (substE (incESub k s) e)
substE s (TyApp e tys) = TyApp (substE s e) tys


\end{code}
Example of an operation defined over this representation --- evaluation.

\begin{code}
data Val ty where
  VBase  :: Val BaseTy
  VLam   :: Sing t1 -> Exp '[t1] t2
         -> Val (FnTy t1 t2)
  VTyLam :: Sing k -> Exp '[] t2
         -> Val (PolyTy k t2)

-- Closed expressions evaluate to values (or diverge)
eval :: Exp '[] ty -> Val ty
eval EBase = VBase
eval (ELam t1 e1) = VLam t1 e1
eval (EApp e1 e2) = case eval e1 of
   VLam _ e1' -> eval (substE (EConsSub e2 EIdSub) e1')
eval (TyLam k e1) = VTyLam k e1
eval (TyApp e tys) = case eval e of
   VTyLam k e' -> eval (substTy (sFromList tys) e')
eval (EVar v) = case v of {}
\end{code}


Another example -- parallel reduction. Needs an axiom!

\begin{code}
axiomPar :: forall g tys. Sing tys ->
     SubstList (FromList tys) (IncList (NatLength tys) g) :~: g
axiomPar _ = undefined

prop_Par g tys = substList (fromList tys) (incList (natLength tys) g) == g

par :: forall g ty. Exp g ty -> Exp g ty
par EBase    = EBase
par (EVar v) = EVar v
par (EApp e1 e2) = case par e1 of
  ELam _ty e1' -> substE (EConsSub e2 EIdSub) e1'
  e1'         -> EApp e1' e2
par (ELam ty e) = ELam ty (par e)
par (TyApp (e :: Exp g (PolyTy k ty1)) (tys :: Sing tys)) = case par e of
  TyLam k (e' :: Exp (IncList k g) ty1)
    | Refl <- axiomPar @g tys
    -> e1 where
      e1 :: Exp (SubstList (FromList tys) (IncList k g)) (Subst (FromList tys) ty1)
      e1 = substTy (sFromList tys) e'
  e1' -> TyApp e1' tys
par (TyLam k e) = TyLam k e
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
utc g (UVar j)    = natIdx g j
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
      | k == natLength tys
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
tcVar (SCons t _ )   Z     = Checks t VZ
tcVar (SCons _ ts)  (S m)  =
  case tcVar ts m of
   Checks t v -> Checks t (VS v)
   Errors s   -> Errors s
tcVar SNil          _     = Errors "unbound variable"
   
tcExp :: Sing ctx -> UExp -> TcResult Exp ctx
tcExp g (UVar k) =
  case tcVar g k of
    Checks t v -> Checks t (EVar v)
    Errors s   -> Errors s 
tcExp g (ULam t1 u)
  | SomeSing sT1 <- toSing t1
  = case (tcExp (SCons sT1 g) u) of
      Checks sT2 e -> Checks (SFnTy sT1 sT2) (ELam sT1 e)
      Errors s     -> Errors s
tcExp g (UApp u1 u2) =
  case (tcExp g u1) of
    Checks t1 e1 -> case (tcExp g u2) of
      Checks t2 e2 ->
        case t1 of
          SFnTy t11 t12 ->
            case testEquality t11 t2 of
              Just Refl -> Checks t12 (EApp e1 e2)
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
            case testEquality sK (sNatLength sTys) of
              Just Refl -> Checks (sSubst (sFromList sTys) t1) (TyApp e1 sTys)
              Nothing -> Errors "Wrong number of type args"
          _ -> Errors "Wrong type in tyapp"
      Errors s -> Errors s
\end{code}

Example: Typeof

\begin{code}
varTy :: Sing g -> Var g t -> Sing t
varTy (SCons t _)  VZ      = t
varTy (SCons _ g)  (VS n)  = varTy g n
varTy SNil         v       = case v of {}

typeOf :: Sing g -> Exp g t -> Sing t
typeOf g (EVar v)       = varTy g v
typeOf g EBase          = SBaseTy
typeOf g (ELam t1 e)    = SFnTy t1 (typeOf (SCons t1 g) e)
typeOf g (EApp e1 e2)   =
  case typeOf g e1 of
    SFnTy _ t2 -> t2
typeOf g (TyLam k e)    = SPolyTy k (typeOf (sIncList k g) e)
typeOf g (TyApp e tys)  =
  case typeOf g e of
    SPolyTy k t1 -> sSubst (sFromList tys) t1
\end{code}

Example: CPS conversion

Note: need to know that these type functions are injective

\begin{code}
type VoidTy = PolyTy (S Z) (VarTy Z)

type family CpsTy a = r | r -> a where
  CpsTy (VarTy i)      = VarTy i
  CpsTy BaseTy         = BaseTy
  CpsTy (FnTy t1 t2)   = FnTy (CpsTy t1) (FnTy (ContTy t2) VoidTy)
  CpsTy (PolyTy k t1)  = PolyTy k (FnTy (ContTy t1) VoidTy)

type family ContTy a = r | r -> a where
  ContTy t = FnTy (CpsTy t) VoidTy

type family CpsList a = r | r -> a where
   CpsList '[] = '[]
   CpsList (t ': ts) = (CpsTy t ': CpsList ts)

----------------------------------------------------------------
-- UGH: have to write these by hand

voidTy = PolyTy 1 (VarTy 0)

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

sVoidTy :: Sing VoidTy
sVoidTy = SPolyTy (SS SZ) (SVarTy SZ)

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

----------------------------------------------------------------
-- NOTE: we still need CpsList because we have to convert the
-- type arguments
{-
type family CpsSub s = r | r -> s where
  CpsSub IdSub          = IdSub
  CpsSub (IncSub n)     = IncSub n
  CpsSub (ConsSub t ts) = ConsSub (CpsTy t) (CpsSub ts)
  CpsSub (TailSub n s)  = TailSub n (CpsSub s)
  CpsSub (LiftSub n s)  = LiftSub n (CpsSub s)

cpsSub :: Sub -> Sub
cpsSub IdSub = IdSub
cpsSub (IncSub n)     = IncSub n
cpsSub (ConsSub t ts) = ConsSub (cpsTy t) (cpsSub ts)
cpsSub (TailSub n s)  = TailSub n (cpsSub s)
cpsSub (LiftSub n s)  = LiftSub n (cpsSub s)

sCpsSub :: Sing s -> Sing (CpsSub s)
sCpsSub SIdSub = SIdSub
sCpsSub (SIncSub n)     = SIncSub n
sCpsSub (SConsSub t ts) = SConsSub (sCpsTy t) (sCpsSub ts)
sCpsSub (STailSub n s)  = STailSub n (sCpsSub s)
sCpsSub (SLiftSub n s)  = SLiftSub n (sCpsSub s)

cpsCommutes3 :: forall s ty.
               CpsTy (Subst s ty) :~: Subst (CpsSub s) (CpsTy ty)
cpsCommutes3 = unsafeCoerce Refl

cps_commutes3 s ty =
  cpsTy (subst s ty) == subst (cpsSub s) (cpsTy ty)
-}


cpsCommutes :: forall n ty.
               CpsTy (Subst (IncSub n) ty) :~: Subst (IncSub n) (CpsTy ty)
cpsCommutes = unsafeCoerce Refl

cps_commutes n ty =
  cpsTy (subst (IncSub n) ty) == subst (IncSub n) (cpsTy ty)

cpsCommutes2 :: forall tys ty.
               CpsTy (Subst (FromList tys) ty) :~:
               Subst (FromList (CpsList tys)) (CpsTy ty)
cpsCommutes2 = unsafeCoerce Refl

cps_commutes2 tys ty =
  cpsTy (subst (fromList tys) ty) == subst (fromList (cpsList tys)) (cpsTy ty)

cpsNatLength :: forall tys. NatLength tys :~: NatLength (CpsList tys)
cpsNatLength = unsafeCoerce Refl

cps_natLength tys =
  natLength tys == natLength (cpsList tys)
\end{code}

\begin{code}
--cpsProg ::

data CpsCtx g g' where
  CpsStart  :: CpsCtx '[] '[]
  CpsELam   :: Sing t1 -> Sing t2 -> CpsCtx g g'
            -> CpsCtx (t1 ': g) (ContTy t2  ': CpsTy t1 ': g')
  CpsEApp   :: Sing t1 -> CpsCtx g g'
            -> CpsCtx (t1 ': g) (CpsTy t1  ': g')
  CpsTyLam  :: Sing t1 -> CpsCtx g g'
            -> CpsCtx        g  (ContTy t1 ': g')

sIncCpsCtx :: forall n g g'.
              Sing n -> CpsCtx g g' -> CpsCtx (IncList n g) (IncList n g')
sIncCpsCtx n CpsStart = CpsStart
sIncCpsCtx n (CpsELam (t1 :: Sing t1) (t2 :: Sing t2) gg)
  | Refl <- cpsCommutes @n @t1
  , Refl <- cpsCommutes @n @t2
  = CpsELam (sInc n t1) (sInc n t2) (sIncCpsCtx n gg)
sIncCpsCtx n (CpsEApp (t1 :: Sing t1) gg)
  | Refl <- cpsCommutes @n @t1
  = CpsEApp (sInc n t1) (sIncCpsCtx n gg)
sIncCpsCtx n (CpsTyLam (t1 :: Sing t1) gg)
  | Refl <- cpsCommutes @n @t1
  = CpsTyLam (sInc n t1) (sIncCpsCtx n gg)
  

fstCtx :: CpsCtx g g' -> Sing g
fstCtx CpsStart = SNil
fstCtx (CpsELam t1 t2 gg) = SCons t1 (fstCtx gg)
fstCtx (CpsEApp t1 gg)    = SCons t1 (fstCtx gg)
fstCtx (CpsTyLam t1 gg)   = fstCtx gg


cpsVar :: CpsCtx g g' -> Var g t -> Var g' (CpsTy t)
cpsVar CpsStart v = case v of {}
cpsVar (CpsELam t1 t2 gg) VZ     =  VS VZ
cpsVar (CpsELam t1 t2 gg) (VS v) =  VS (VS (cpsVar gg v))
cpsVar (CpsEApp t1 gg) VZ     =  VZ
cpsVar (CpsEApp t1 gg) (VS v) =  VS (cpsVar gg v)
cpsVar (CpsTyLam t1 gg)   v      =  VS (cpsVar gg v)


-- Follow Francois' "inefficient" version
-- Note the uses of substE and substCont in the EApp case
-- NOTE: if Meta was *actually* meta (i.e. a Haskell function), we would
-- not be able to reify it correctly
data Cont g t where
  Obj  :: Exp g (FnTy t VoidTy) -> Cont g t
  Meta :: Exp (t ': g) VoidTy   -> Cont g t

applyCont :: Cont g t -> Exp g t -> Exp g VoidTy
applyCont (Obj o)  v  = EApp o v
applyCont (Meta k) v  = (substE (EConsSub v EIdSub)) k

reifyCont :: Sing t -> Cont g t -> Exp g (FnTy t VoidTy)
reifyCont t (Obj o)   = o
reifyCont t (Meta k)  = ELam t k

substCont :: ESub g g' -> Cont g t -> Cont g' t
substCont s (Obj o)   = Obj (substE s o)
substCont s (Meta k)  = Meta (substE (ELiftSub s) k)

substTyCont :: Sing s -> Cont g t -> Cont (SubstList s g) (Subst s t)
substTyCont s (Obj o)   = Obj (substTy s o)
substTyCont s (Meta k)  = Meta (substTy s k)

cpsExp :: forall t g g'.
          CpsCtx g g' 
       -> Exp g t
       -> Cont g' (CpsTy t) 
       -> Exp g' VoidTy
cpsExp gg (EVar v)      k = applyCont k (EVar (cpsVar gg v))
cpsExp gg EBase         k = applyCont k EBase
cpsExp gg (ELam t1 e1)  k =
  case typeOf (fstCtx gg) (ELam t1 e1) of
   (SFnTy (t1 :: Sing t1) (t2 :: Sing t2)) ->
      let
        e'  = ELam (sCpsTy t1)
               $ ELam (sContTy t2)
                 $ cpsExp (CpsELam t1 t2 gg) e1 k'

        k'  = Obj $ EVar VZ

      in
        applyCont k e'    
cpsExp gg (TyLam n e) k   = 
  case typeOf (fstCtx gg) (TyLam n e) of
    SPolyTy _k (t1 :: Sing t1) -> 
      applyCont k $ TyLam n 
                  $ ELam (sContTy t1) 
                  $  cpsExp (CpsTyLam t1 (sIncCpsCtx n gg)) e (Obj $ EVar VZ)
    
cpsExp gg (EApp e1 e2)  k =
  case typeOf (fstCtx gg) e1 of
   (SFnTy (t1 :: Sing t1) (t2 :: Sing t2)) ->
     let
        k1 :: Cont g' (CpsTy (FnTy t1 t2))
        k1 = Meta $ cpsExp (CpsEApp (SFnTy t1 t2) gg) (substE EIncSub e2) k2

        k2 :: Cont (CpsTy (FnTy t1 t2) ': g') (CpsTy t1)
        k2 = Meta $ EApp (EApp (EVar (VS VZ)) (EVar VZ))
               (reifyCont (sCpsTy t2) (substCont EIncSub (substCont EIncSub k)))
     in
       cpsExp gg e1 k1
cpsExp (gg :: CpsCtx g g') (TyApp e1 (tys :: Sing tys)) k =
  case typeOf (fstCtx gg) e1 of
    SPolyTy (n :: Sing n) (t1 :: Sing t1)
      | Refl <- cpsCommutes2 @tys @t1
      , Refl <- cpsNatLength @tys
      ->
      
      let 
          k1 :: Cont g' (CpsTy (PolyTy n t1))
          k1 = Meta $ EApp (TyApp (EVar VZ) (sCpsList tys)) (reifyCont t1' k2)

          k2 :: Cont (CpsTy (PolyTy n t1) ': g') 
                     (Subst (FromList (CpsList tys)) (CpsTy t1))
          k2 = substCont EIncSub k

          t1' :: Sing (Subst (FromList (CpsList tys))  (CpsTy t1))
          t1' = sSubst (sFromList (sCpsList tys)) (sCpsTy t1)
      in
        cpsExp gg e1 k1
\end{code}


\section {testing code}

\begin{code}
fi :: Integer -> Nat
fi n = if n == 0 then Z
    else if n < 0 then fi (-n)
    else S (fi (n - 1))

upto :: Nat -> [Nat]
upto Z = []
upto (S m) = m : upto m
  
instance Arbitrary Nat where
  arbitrary = fi <$> arbitrary
  shrink Z = []
  shrink (S n) = [n]

instance Arbitrary RSub where
  arbitrary = Reg <$> arbitrary <*> arbitrary
  shrink (Reg t x) = [Reg t' x' | t' <- shrink t, x' <- shrink x]

instance Arbitrary Ty where
  arbitrary = sized (gt Z) where
    base n = oneof (return BaseTy : [return (VarTy k) | k <- upto (fi 5) ])
    gl :: Nat -> Int -> Gen [Ty]
    gl n m = (gt n m) >>= \ty -> return [ty]
    
    gt :: Nat -> Int -> Gen Ty
    gt n m =
      if m <= 1 then base n
      else
      let m' = m `div` 2 in
      frequency
      [(2, base n),
       (1, FnTy <$> gt n m' <*> gt n m'),
       (1, do
           k <- elements [Z, S Z, S (S Z), S (S (S Z))]
           a <- gl (n + k) m'
           r <- gt (n + k) m'
           return (PolyTy k r))]
      
  shrink BaseTy = []   
  shrink (VarTy n) = [VarTy n' | n' <- shrink n]
  shrink (FnTy t1 t2) = t1 : t2 : 
    [ FnTy t1' t2' | t1' <- shrink t1, t2' <- shrink t2]
  shrink (PolyTy n t) = t : 
    [ PolyTy n' t' | n' <- shrink n, t' <- shrink t]

instance Arbitrary Sub where
  arbitrary = sized gt where
    base = oneof [return IdSub, IncSub <$> arbitrary]
    gt m =
      if m <= 1 then base else
      let m' = m `div` 2 in
      frequency
      [(1, base),
       (1, (:·) <$> arbitrary <*> gt m'), -- always closed? FVs?
       (1, (:∘) <$> gt m' <*> gt m')]

  shrink IdSub = []
  shrink (IncSub n) = [IncSub n' | n' <- shrink n]
  shrink (t :· s)   = s : [t' :· s' | t' <- shrink t, s' <- shrink s]
  shrink (s1 :∘ s2) = s1 : s2 :
    [s1' :∘ s2 | s1' <- shrink s1, s2' <- shrink s2]                       
  shrink (LiftSub n s) = s : [LiftSub n s' | n <- shrink n, s' <- shrink s]

----------------------------------------------------------------------
----------------------------------------------------------------------



prop_cons_sub ty ss tt =
  subst (ty :· ss) (subst (IncSub 1) tt) == subst ss tt


return []
runTests = $forAllProperties qc
\end{code}


\begin{code}
qc :: Testable prop => prop -> IO Result
qc = quickCheckWithResult (stdArgs { maxSuccess = 1000 })
\end{code}

\section{Related Work}

A Type-Preserving Compiler in Haskell
Louis-Julien Guillemette Stefan Monnier
ICFP 2008
Uses "standard" de Brujn Indices to represent System F types
"Pre-datakinds"  uses newtypes to introduce constructors for
All/Var in Type.

Revisiting the CPS Transformation and its Implementation
Franc¸ois Pottier

Martín Abadi, Luca Cardelli, Pierre-Louis Curien, and Jean-Jacques Lévy. Explicit
substitutions. J. Funct. Program., 1(4):375–416, 1991.

Completeness and Decidability of de Bruijn Substitution Algebra in Coq
Steven Schafer Gert Smolka Tobias Tebbi
CPP 2015

%% Acknowledgments
\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
  This material is based upon work supported by the
  \grantsponsor{GS100000001}{National Science
    Foundation}{http://dx.doi.org/10.13039/100000001} under Grant
  No.~\grantnum{GS100000001}{nnnnnnn} and Grant
  No.~\grantnum{GS100000001}{mmmmmmm}.  Any opinions, findings, and
  conclusions or recommendations expressed in this material are those
  of the author and do not necessarily reflect the views of the
  National Science Foundation.
\end{acks}


%% Bibliography
%\bibliography{bibfile}


%% Appendix
\appendix
\section{Appendix}

Text of appendix \ldots

\end{document}
