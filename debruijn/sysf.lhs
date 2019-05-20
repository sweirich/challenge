

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
\renewcommand{\Varid}[1]{\textit{#1}}  %% allow _ in identifiers
%format :∘ = "\mathop{:\!\!\circ}"
%format :· = "\mathop{:\!\!\cdot}"
%format . = "."
%format forall = "\forall"
%format _ = "\_"
%format s1 = "\ensuremath{s_1}"
%format s2 = "\ensuremath{s_2}"
%format g1 = "\ensuremath{g_1}"
%format g2 = "\ensuremath{g_2}"
%format g3 = "\ensuremath{g_3}"
%format e1 = "\ensuremath{e_1}"
%format e2 = "\ensuremath{e_2}"
%format e3 = "\ensuremath{e_3}"


%format Nat = "\ensuremath{\mathbb{N}}"
%format <>  = "\ensuremath{\diamond}"
%format ~   = "\ensuremath{\mathop{\sim}}"
%format :~: = "\ensuremath{\mathop{:\sim:}}"
%format λ   = "\ensuremath{\lambda}"

%% Some recommended packages.
\usepackage{booktabs}   %% For formal tables:
                        %% http://ctan.org/pkg/booktabs
\usepackage{subcaption} %% For complex figures with subfigures/subcaptions
                        %% http://ctan.org/pkg/subcaption


\begin{document}

%% Title information
\title{System F in Dependent Haskell}
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
\end{code}
%endif

Let's get this out of the way right now.
\begin{code}
import Unsafe.Coerce
\end{code}

This paper is about a balance between the fine-lines of type-based correctness
and broad strokes of practicality.

In the formost, static types should assist in program design, not stand in the
way. And definitely not become a vehicle for nerd-sniping naval gazing; where
we convince ourselves that we are making progress.

At the same time, there are difficult programs out there. Those that are
difficult to write, and those that are difficult to know when you've gotten
them right.

One example of such difficulty is the proper treatment of binding.

Variable binding is older than the lambda calculus. And you would think it
would be \emph{easy} after all of this time. And, it is true that we do know
how to do it. And so well that we can automate definitions.

This paper is a literate Haskell example of a strongly-typed representation of
System F. In other words, the datatype only includes well typed System F
terms.

We're going to do it, but just barely. Along the way there are points where we
could design the system to be even more implicitly typed, and we will point
out those opportunities. However, we will refrain from this sort of
over-exuberance.

Although strongly-typed ASTs are common examples for programming with GADTs,
here we go a bit further. On one hand, it uses a deep embedding types ---
our AST will be indexed by members of a Haskell datatype, called |Ty| instead
of actual Haskell types (of kind |Type|), the usual shallow embedding of
types.

Furthermore, System F includes \emph{polymorphic} types, which bring their own
challenges to a strongly-typed embedding (in Haskell).

We will use deBruijn indices with parallel substitutions to represent type
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

\subsection{Preliminaries: Nat and the |singletons| library}

First, a datatype for indices themselves --- natural numbers. 

\begin{spec}
data Nat = Z | S Nat
\end{spec}

We elide definitions relating to natural numbers (the full definitions are
available in our code base). However, we note that we have instances of this
type for the classes |Eq|, |Ord|, |Enum|, |Num| (partial) and |Show| (displays
using digits).

We have also redefined some prelude operations for lists to use |Nat| instead
of |Int|, including |take|, |drop|, and the indexing operator |!!|.

All of our operations on |Nat| are available in three different forms:
\begin{enumerate}
\item As a standard function (starts with lowercase letter)
\begin{spec}
ghci> :type take
take :: Nat -> [a] -> [a]
\end{spec}
\item As a type-level function (starts with uppercase letter)
\begin{spec}
ghci>:kind Take
Take :: Nat -> [a] -> [a]
\end{spec}
\item As a singleton function (starts with |s| then uppercase letter)
\begin{spec}
ghci> :type sTake
sTake :: Sing t1 -> Sing t2 -> Sing (Take t1 t2)
\end{spec}
\end{enumerate}

The singletons library automatically defines the second and third version from
the first, as well as the \texttt{Sing t} indexed type, displayed above as
|Sing t|.  However, any code that uses these operations must be careful to use
the correct one.

Any use of the |Sing a| type indicates the use of dependent types. These
arguments that are used both as runtime and compile time data.


\section{Type representation with de Bruijn indices}

Below, our datatype for types. 
\begin{code}
$(singletons [d|
    data Ty =
         BaseTy               
      |  VarTy Nat            
      |  FnTy Ty Ty           
      |  PolyTy Nat Ty        
         deriving (Eq,Show)
    |])
\end{code}

Types include base types, like |()| or |Bool|, type variables (which are
represented by indices), function types and polymorphic types. In the last
case, we allow polymorphic types to bind several type variables at once. The
natural number in this type indicates the number of simultaneously bound
variables.

For example, the System F type |forall a b. a -> b| is represented by the value
|PolyTy 2 (FnTy (VarTy 0) (VarTy 1))|.

The important property of this representation is that it all
$\alpha$-equivalent types have the same representation. In other words, both
|forall a. a -> a| and |forall b. b -> b| are represented by |idTy| below.

\begin{code}
$(singletons [d|
    idTy :: Ty
    idTy = PolyTy (S Z) (FnTy (VarTy Z) (VarTy Z))
    |])
\end{code}
By defining this value as a |singletons| declaration, we get the term value
|idTy|, the analogous type |IdTy| (of promoted kind |Ty|) and the singleton
version that connects the two: |sIdTy :: Sing IdTy|. 

Our goal is to use these types to index a typed term representation.  For example,
if a System F term |e| has type |Exp g IdTy|, in some context |g|, then |e| should
only be (the representation of) a polymorphic identity function.

The unique representation property is essential when using this data structure
to index a strongly typed AST. We don't have to define $\alpha$-equivalence
for types, as Haskell's pre-existing definition of type equivalence will just
work.  Furthermore, we don't have to worry that a type indexed by |forall a. a
-> a| is a different type than one indexed by |forall b. b -> b|; we can
easily work up to $\alpha-$equivalence with this representation.

\subsection{Substitution algebra}

Although $\alpha$-equivalence comes for free with a de Bruijn representation,
we still need to define what it means to \emph{substitute} for variables that
appear in types.

For example, in the strongly typed constructor for type abstractions, written
|TyApp| and part of the |Exp| GADT, we need to instantiate a polymorphic term
with (the correct number of) type arguments.  We do so by substituting for the
bound variables in the body of the polymorphic type.

\begin{spec}
  TyApp  :: (Length tys ~ n)             -- length requirement
    => Exp g (PolyTy n ty)               -- polymorphic term
    -> Sing tys                          -- type arguments
    -> Exp g (Subst (FromList tys) ty)   -- instantiated type
\end{spec}

In this type, the type-level function |FromList| converts a list of types to a
\emph{substitution} and the |Subst| operation applies this substitution to the
body of the polymorphic type, |ty|.  Furthermore, this data constructor also
requires that the number of type arguments (the length of the list |tys|) is
equal to the number of type parameters quantified by the polymorphic type.

Next, the representation of substitutions. We use a concrete representation of
substitutions, based on the algebraic data type below. 
\begin{code}
$(singletons [d|
    data Sub =
        Inc Nat            --  increment by n (shift)                
     |  Ty  :· Sub         --  extend a substitution (like cons)
     |  Sub :∘  Sub        --  compose substitutions
        deriving (Eq, Show)

    infixr :·    -- like usual cons operator (:)
    infixr :∘    -- like usual composition  (.)
    |])
\end{code}

This algebra allows us to construct a number of substitution actions on types
from these primitive operations. Intuitively these operations are:

\begin{itemize}

\item |Inc n| - A primitive substitution that increments all free variables
that appear in a type by |n|.\footnote{This substitution is sometimes written
as |(+n)| or $\uparrow^{n}$.}.

For example
\begin{spec}
ghci> subst (Inc 2) (FnTy (VarTy 0) (VarTy 1))
FnTy (VarTy 2) (VarTy 3)
\end{spec}

\item |ty :· s| - Extend a substitution by adding a new definition for
    index 0 and shifting everything in |s| one step to the right.
For example
\begin{spec}
ghci> subst (BaseTy :· Inc 0) (FnTy (VarTy 0) (VarTy 1))
FnTy BaseTy (VarTy 0)
\end{spec}

\item |s1 :∘ s2| - Compose two substitutions together. This is equivalent to
first substituting by |s1| and then substituting by |s2|.

\end{itemize}

These three substitution operations are all that we need to work with System
F. For example, we can define an identity substitution by incrementing by
zero.

\begin{code}
$(singletons [d|
    idSub :: Sub
    idSub = Inc Z      
    |])
\end{code}

Furthermore, we can use the cons and identity substitutions to define
|fromList| the conversion of a list of types to a substitution. In the result,
the $i$th free variable is replaced by the $i$th type in the list, and all
other free variables are left alone.

\begin{code}
$(singletons [d|
    fromList :: [Ty] -> Sub
    fromList (t:ts)  = t :· fromList ts
    fromList []      = idSub
  |])
\end{code}

Finally, we can define the |lift| substitution, which is exactly what we need
when working with substitutions under binders.  Using the substitution |lift n
s|, all free variables in the range |0..n-1| are left alone, and any free
variables in the range of |s| are all incremented by |n|.


\begin{code}
$(singletons [d|
    lift :: Nat -> Sub -> Sub
    lift k s = upTo k (s :∘ Inc k)

    upTo :: Nat -> Sub -> Sub
    upTo Z      s = s
    upTo (S m)  s = upTo m (VarTy m :· s)
    |])
\end{code}

For example, if have a substitution that replaces 0 with |FnTy (BaseTy) (VarTy
0)| and leaves all other types alone, we can lift it by two steps to the
version that leaves variables 0 and 1 alone and replaces variable 2 by
|(FnTy BaseTy (VarTy 2))|.

\begin{spec}
ghci> lift 2 ((FnTy BaseTy (VarTy 0)) :· Inc 0)
VarTy 0 :· (VarTy 1 :· ((FnTy BaseTy (VarTy 0) :· Inc 0) :∘ Inc 2))
\end{spec}


% Quotation from Pottier:
% "In short, $\uparrow^i t$ is the term obtained by adding $i$ to every variable that
% appears free in the term $t$. The symbol $\uparrow^i$ can be intuitively read as an
% end-of-scope mark: it means that the $i$ most-recently-introduced variables are
% not in scope in the term that follows (Bird and Paterson, 1999, Hendriks and
% van Oostrom, 2003)."

The main thing we want to do with a substitution |Sub| is apply it to a type.
Below, we define the opeartion |subst| (which applies a substiution to a type)
mutually with an operation |applyS| (which looks up the |nth| type in a
substitution).

The |subst| operation extends the substitution for a single index
throughout the type structure. When this function calls itself recursively
under a binder, it uses `lift` to modify the input substitution.

The |applyS| operation dispatches on the substitution algebra. In the base
case, it increments the index by |n|. For cons, if the index is zero, it
returns the type |ty|. If not, it decrements the index and looks up the value
in the substition in the tail.  For composition, it first determines the value
of the index in the first substitution, then applies the second substitution
to that type.

\begin{code}
$(singletons [d|

    -- apply a substitution to a type
    subst :: Sub -> Ty -> Ty
    subst s BaseTy        = BaseTy
    subst s (VarTy x)     = applyS s x
    subst s (FnTy a r)    = FnTy (subst s a) (subst s r)
    subst s (PolyTy n a)  = PolyTy n (subst (lift n s) a)
              
    -- value of the index x in the substitution s
    applyS :: Sub -> Nat -> Ty
    applyS (Inc n)        x  = VarTy (plus n x)           
    applyS (ty :· s)      x  = case x of
                                 Z      -> ty
                                 (S m)  -> applyS s m
    applyS (s1 :∘ s2)     x  = subst s2 (applyS s1 x)

               
    |])
\end{code}

In this definition we are taking advantage of Haskell's lack of termination
checking. The two functions above are not structurally recursive and would not
be accepted in this form in languages like Agda and Coq, where all functions
must be shown terminating. In that setting, this definition must be given in
stages: first one defines a renaming (which only replaces variables with other
variables, an operation that is structurally recursive) and then one uses
renaming to define substitution.

In Haskell, without the obligatio to show termination, we can use the more
direct implementation above.  (Of course, this lack of termination checking
means that if a type-level function is not actually terminating, there is a
danger that the GHC type checker could go into an infinite loop. As
programmers that behavior is annoying, but not disastrous.)

Even though the singletons library allows us to use higher-order functions,
like |map|, it is not always convenient to reason about the defunctionalized
symbols that must be given to |map|. For ease, we define names for some common
operations on lists that we will need later.

\begin{code}
$(singletons [d|
              
    substList :: Sub -> [Ty] -> [Ty]
    substList s = map (subst s)                                

    incList :: Nat -> [Ty] -> [Ty]
    incList n = map (subst (Inc n))
               
    liftList :: Nat -> Sub -> [Ty] -> [Ty]
    liftList n s = map (subst (lift n s))

   |])
\end{code}

\section{Strongly-typed Expressions}

Now, in this section, use the promoted, quantified types to develop an
intrinsically-typed version of System F.

The GADTs |Exp g t| below represents terms. This data structures is indexed by
|g|, a context (i.e. list of types for the free variables of the term) and the
type of the System F expression |t|.  As with types above, we represent
variables by natural number indices in the |VarE| constructor. However, this
constructor comes with a requirement that the index |n| can be used to lookup
the \emph{nth} type in the context. In other words, the variable constructor
ensures that expression variables are in scope.

The constructors for lambda abstraction and application are straightforward
for this representation --- in the lambda case, the context includes the type
of the variable bound by the function. In an application, the argument must
have the same type as that expected by the function.

The |TyLam| and |TyApp| constructors represent n-ary type abstraction and
application. In the former case, all variables in the context used to type
check the body of the type abstraction must be incremented by |n|, the number
of type variables bound in the type abstraction.  The |TyApp| case is as
described above.


\begin{code}
data Exp :: [Ty] -> Ty -> Type where
  
  BaseE  :: Exp g BaseTy
  
  VarE   :: (Idx g n ~ Just t)    -- scope requirement
         => Sing n                -- variable index
         -> Exp g t
         
  LamE   :: Sing t1               -- type of binder
         -> Exp (t1:g) t2         -- body of abstraction
         -> Exp g (FnTy t1 t2)
         
  AppE   :: Exp g (FnTy t1 t2)    -- function
         -> Exp g t1              -- argument
         -> Exp g t2
  
  TyLam  :: Sing n                -- num of tyvars to bind
         -> Exp (IncList n g) t   -- body of type abstraction
         -> Exp g (PolyTy n t)

  TyApp  :: (k ~ Length ts)       -- length requirement
         => Exp g (PolyTy k t)    -- polymorphic term
         -> Sing ts               -- type arguments
         -> Exp g (Subst (FromList ts) t)

data Var g t where
  V :: (Idx g n ~ Just t) => Sing n -> Var g t         
\end{code}

For example, we can use this expression to typecheck
the polymorphic identity function

\begin{spec}
ghci> :type TyLam (SS SZ) (LamE (SVarTy SZ) (VarE SZ))
  :: Exp g (PolyTy (S Z)
            (FnTy (VarTy Z) (VarTy Z)))
\end{spec}

This example works because expressions are annotated with runtime
representation of System F types. Haskell's type inference has enough
information to figure out the type of the term from the derivation.

In contrast, expressions that don't type check in System F are also ill-typed
in Haskell.
\begin{spec}
ghci> TODO!!!
\end{spec}

We can also dynamically produce the type of a well-typed expression, as long
as we have a runtime representation of the context so that we can calculate
the type of free variables. (We are not type checking with this function, only
recovering the type from a term that is known to be type correct.)

\begin{code}
typeOf :: Sing g -> Exp g t -> Sing t
typeOf g (VarE v)       =
  case sIdx g v of
    SJust t -> t
typeOf g BaseE          =
  SBaseTy
typeOf g (LamE t1 e)    =
  SFnTy t1 (typeOf (SCons t1 g) e)
typeOf g (AppE e1 e2)   =
  case typeOf g e1 of
    SFnTy _ t2 -> t2
typeOf g (TyLam n e)    =
  SPolyTy n (typeOf (sIncList n g) e)
typeOf g (TyApp e tys)  =
  case typeOf g e of
    SPolyTy _ t1 -> sSubst (sFromList tys) t1
\end{code}

Because we know that the term type checks, Haskell's pattern match coverage
checker does not complain about the three pattern matches in the function
above. In each case there is only one possible pattern that type checks.

Note also above that we use the singleton-ized versions of many operations
(such as the |incList|, |subst| and |fromList| functions defined above).

\begin{spec}
sIdx       :: Sing l -> Sing n  -> Sing (Idx l n)
sSubst     :: Sing s -> Sing ty -> Sing (Subst s ty)
sIncList   :: Sing n -> Sing g  -> Sing (IncList n g)
sFromList  :: Sing tys -> Sing (FromList tys)
\end{spec}

The |idx| function, defined in the natural number library determines the $i$th
element of a list, returning either |Nothing| or |Just x|. So the
singleton-ized version returns either |SNothing| or |SJust|.  However, in the
|VarE| case, the restriction on the type constructor means that we know that
the indexing operation will succeed. The type checker can tell that the
pattern match in this case is exhaustive.

\subsection{Type substitution in terms: version1}

The next step is to define the operation for type substitution in terms.  This
operation is challenging to define because we need to show that terms stay
well typed even under substitution. To write this function, we need to tell
the Haskell type checker four facts about about the type substitution
operation.  We communicate this information via \emph{lemma}s; i.e. functions
that return a evidence of equality between two types that Haskell would not
otherwise know equivalent. This evidence comes in the form of |Refl|, the sole
data constructor of the Haskell GADT |a :~: b|, a proposition that two types
are equal.

\begin{code}
substTy1 :: forall s g ty.
     Sing s
  -> Sing g
  -> Exp g ty
  -> Exp (SubstList s g) (Subst s ty)
substTy1 s g (VarE n)
  -- fact about substitution in contexts, see below
  |  Refl <- lemma_SubstIdx g n s
  =  VarE n
substTy1 s g BaseE
  = BaseE  
substTy1 s g (LamE ty e)
  = LamE (sSubst s ty) (substTy1 s (SCons ty g) e)
substTy1 s g (AppE e1 e2)
  = AppE (substTy1 s g e1) (substTy1 s g e2)

substTy1 s g (TyLam k e)
  |  Refl <- lemma_LiftIncList s k g
  =  TyLam k (substTy1 (sLift k s) (sIncList k g) e)
  
substTy1 s g (TyApp (e :: Exp g (PolyTy k ty1)) tys)
  |  Refl <- lemma_SubstFromList @ty1 s tys
  ,  Refl <- lemma_LengthSubstList s tys
  = TyApp (substTy1 s g e) (sSubstList s tys)
\end{code}


In the first case of |substTy1|, we need to show that substituting through
variable lookups is type-sound.  The fact that we need to show in this case is
not a difficult "proof" to write in Haskell. Essentially the proof is an
induction on the index |n|.

\begin{code}
lemma_SubstIdx :: (Idx g n ~ Just t) =>
  Sing g -> Sing n -> Sing s ->
  Idx (SubstList s g) n :~: Just (Subst s t)
lemma_SubstIdx (SCons _ _)   SZ     s
  = Refl
lemma_SubstIdx (SCons _ xs)  (SS n) s
  | Refl <- lemma_SubstIdx xs n s
  = Refl
\end{code}

The last two branches of substTy requires more traditional proofs about type
equality.  

In the |TyLam| case, we call the function recursively after shifting
the substitution by the number of binders in the abstraction.

we have

\begin{spec}
   substTy1 (sLift k s) .. e ::
       Exp (SubstList (Lift k s) g) (Subst (Lift k s) ty)
\end{spec}

we want to produce a term of type

\begin{spec}
   Exp s (Subst s g) (Subst s (PolyTy k ty))
   ==
   Exp s (Subst s g) (PolyTy k (Subst (Lift k s) ty))
\end{spec}

we can do so with the TyLam, given a body of type

\begin{spec}
   Exp s (IncList k (Subst s g)) (Subst (Lift k s) ty)
\end{spec}

so the type of the body lines up. But we need a type equality between the
contexts.


We also need three more lemmas.

\begin{spec}
lemma_LiftIncList :: forall s k g.
  Sing s -> Sing k -> Sing g -> 
  LiftList k s (IncList k g) :~: IncList k (SubstList s g)

lemma_SubstFromList :: forall ty1 s tys.
  Sing s -> Sing tys ->
  Subst (FromList (SubstList s tys))
    (Subst (Lift (Length tys) s) ty1)
     :~: 
  Subst s (Subst (FromList tys) ty1)

lemma_LengthSubstList :: forall s tys.
  Sing s -> Sing tys ->
  Length (SubstList s tys) :~: Length tys
\end{spec}

%if False
\begin{code}
lemma_LiftIncList :: forall s k g.
  Sing s -> Sing k -> Sing g -> 
  LiftList k s (IncList k g) :~: IncList k (SubstList s g)
lemma_LiftIncList s k SNil = Refl
lemma_LiftIncList s k (SCons (t :: Sing t) (ts :: Sing ts)) 
  | Refl <- lemma_LiftInc s k t
  , Refl <- lemma_LiftIncList s k ts
  = Refl
\end{code}

\begin{code}
-- helper function for above
lemma_LiftInc :: forall t s k.
  Sing s -> Sing k -> Sing t ->
  Subst (Lift k s) (Subst (Inc k) t) :~: Subst (Inc k) (Subst s t)
lemma_LiftInc s k (SVarTy n)
  | Refl <- lemma_UpTo s k n
  = Refl
lemma_LiftInc s k (SFnTy t1 t2)
  | Refl <- lemma_LiftInc s k t1
  , Refl <- lemma_LiftInc s k t2
  = Refl
lemma_LiftInc s k SBaseTy
  = Refl
lemma_LiftInc s k (SPolyTy n t)
  | Refl <- lemma_LiftInc s k t
  = undefined -- TODO!!!

lemma_UpTo :: Sing s -> Sing k -> Sing n ->
  ApplyS (UpTo k (s :∘ Inc k)) (Plus k n)
  :~: Subst (Inc k) (ApplyS s n)  
lemma_UpTo s SZ n = Refl
lemma_UpTo s (SS m) n 
  | Refl <- lemma_UpTo s m n
  = undefined -- TODO!!!
\end{code}

\begin{code}
lemma_SubstFromList :: forall ty1 s tys.
  Sing s -> Sing tys ->
  Subst (FromList (SubstList s tys))
    (Subst (Lift (Length tys) s) ty1)
     :~: 
  Subst s (Subst (FromList tys) ty1)
lemma_SubstFromList s SNil = undefined
lemma_SubstFromList s (SCons ty s1) = undefined

lemma_SubstId :: forall t.
  Sing t ->
  Subst (Inc Z) t :~: t
lemma_SubstId SBaseTy = Refl
lemma_SubstId (SFnTy t1 t2)
  | Refl <- lemma_SubstId t1
  , Refl <- lemma_SubstId t2
  = Refl
lemma_SubstId (SVarTy x) = Refl
lemma_SubstId (SPolyTy k t) 
  | Refl <- lemma_SubstLiftId k t
  = Refl

lemma_SubstLiftId :: forall n t.
   Sing n -> Sing t -> 
   Subst (UpTo n (Inc Z :∘ Inc n)) t :~: t
lemma_SubstLiftId _ _ = undefined -- TODO!!!
\end{code}

%endif

However, Haskell is not a good language for this sort of proof. The error
messages are terrible. There is no library of pre-existing theories to draw
on. Even worse, we have to "run" this proof. (And being able to run the proof
also forces us to require a |Sing g| argument to |substTy1|; which we would
not need otherwise.)

\subsection{Type substitution: version 2}

This is not what we want to do.  Instead, we should just \emph{inform} GHC of
the type equality and justify it through other means. We can inform GHC by
defining an ``axiom'', essentially a function that skirts the type system to
produce the ``evidence'' for equality. The axiom below can be used in the same
way as the lemma above --- but note that it doesn't evaluate any of its
arguments.

\begin{code}
axiom_SubstIdx :: (Idx g n ~ Just t) =>
  Sing g -> Sing n -> Sing s ->
  Idx (SubstList s g) n :~: Just (Subst s t)
axiom_SubstIdx _g _n _s = unsafeCoerce Refl
\end{code}

%if False
\begin{code}
axiom_LiftIncList :: forall s k g.
  Sing s -> Sing k -> Sing g -> 
  LiftList k s (IncList k g) :~: IncList k (SubstList s g)
axiom_LiftIncList _ _ _ = unsafeCoerce Refl

axiom_SubstFromList :: forall ty1 s tys.
  Sing s -> Sing tys ->
  Subst (FromList (SubstList s tys))
    (Subst (Lift (Length tys) s) ty1)
     :~: 
  Subst s (Subst (FromList tys) ty1)
axiom_SubstFromList _ _ = unsafeCoerce Refl

axiom_LengthSubstList :: forall s tys.
  Sing s -> Sing tys ->
  Length (SubstList s tys) :~: Length tys
axiom_LengthSubstList _ _ = unsafeCoerce Refl  
\end{code}
%endif

With the help of this axiom, we can produce another leaner version of
|substTy| that does no more work than necessary. All of the axioms immediately
return. Furthermore, because none are strict in their arguments, we need not
provide a runtime representation of the typing context to this function
(i.e. an argument of type |Sing g|).

\begin{code}
substTy :: forall s g ty.
     Sing s 
  -> Exp g ty
  -> Exp (SubstList s g) (Subst s ty)
substTy s (VarE n) 
  |  Refl <- axiom_SubstIdx (undefined :: Sing g) n s
  =  VarE n
substTy s BaseE         = BaseE  
substTy s (LamE ty e)   = LamE (sSubst s ty) (substTy s e)
substTy s (AppE e1 e2)  = AppE (substTy s e1) (substTy s  e2)

substTy s (TyLam k e)
  |  Refl <- axiom_LiftIncList s k (undefined :: Sing g)
  =  TyLam k (substTy (sLift k s) e)
  
substTy s (TyApp (e :: Exp g (PolyTy k ty1)) tys)
  |  Refl <- axiom_SubstFromList @ty1 s tys 
  ,  Refl <- axiom_LengthSubstList s tys 
  =   TyApp (substTy s e) (sSubstList s tys)
\end{code}


\section{Justifying axioms}

But, what is our justification for these axiom? Why should we allow these
instances of |unsafeCoerce| in our code? Shouldn't we worry that our Haskell
code could crash?


\paragraph{External proof of termination for Haskell proof}

One way to justify an axiom is to look at the Haskell proof and rigourously
argue (on paper) that the function will terminate.

For example, the proof of the last lemma is a simple structural recursion on
the list of types.  This function will terminate as long as the provided list
is finite.

\begin{code}
lemma_LengthSubstList :: forall s tys.
  Sing s -> Sing tys ->
  Length (SubstList s tys) :~: Length tys
lemma_LengthSubstList _ SNil = Refl
lemma_LengthSubstList s (SCons t1 s1)
  | Refl <- lemma_LengthSubstList s s1
  = Refl
\end{code}

An System F type application term with an infinite list of types will never
type check, so we can be confident that this equality will hold.

\paragraph{External proof of the property}

Some of the properties above are \emph{hard} to prove. Another alternative is
to translate them to Agda or Coq and try to prove them there.

TODO: describe how this could be done

\paragraph{Testing}

The final way that we can gain confidence about these type equalities is
through testing, and activity where Haskell excels.

For each of the axioms above, we can define QuickCheck properties that refer
to the non-singletonized versions of the operations. Because these are simple
datatypes, we only need to define instances of the |Arbitrary| type class for
the datatypes |Sub| and |Ty| to be able to run these tests.

\begin{code}
prop_SubstIdx :: [Ty] -> Nat -> Sub -> Bool
prop_SubstIdx g n s =
    idx (substList s g) n == (subst s <$> idx g n)
\end{code}

\begin{code}
prop_LiftIncList :: [Ty] -> Sub -> Nat -> Bool
prop_LiftIncList g s k =
    liftList k s (incList k g) == incList k (substList s g)
\end{code}

\begin{code}
prop_SubstFromList :: Ty -> Sub -> [Ty] -> Bool
prop_SubstFromList ty1 s tys =
  subst (fromList (substList s tys))
    (subst (lift (length tys) s) ty1)
    ==
  subst s (subst (fromList tys) ty1)
\end{code}

\begin{code}
prop_LengthSubstList :: Sub -> [Ty] -> Bool
prop_LengthSubstList s tys =
  length (substList s tys) == length tys
\end{code}


\section{Term substitution}

Next, we need to define substitition for expression variables. In this case,
the definitions are similar to above, but with two significant changes.

First, term substitutions are more informatively typed than type
substitutions. Because they apply to well-typed expressions, they need to
statically track the transformation of the environment during substitution.

Second, instead of bunching up increments by providing a natural number to
|Inc|, we instead only allow one increment at a time. We make this change to
account for the significant increase in complexity that comes from indexing
the types of substitutions by their associated contexts.  As a result, we need
to also provide an indendenty substitution for incrementing by zero.
\footnote{This implementation is less efficient, as it stores increments in unary.}

\begin{code}
data SubE g g' where
  IdE    :: SubE g g
  IncE   :: SubE g (ty:g)
  ConsE  :: Exp g' ty -> SubE g g' -> SubE (ty:g) g'
  CompE  :: SubE g1 g2 -> SubE g2 g3 -> SubE g1 g3
\end{code}

As before, we can define the ``lifting'' operation that appropriately modifies
the substitution for traversing under binders. However, we only ever bind one
variable at a time in expressions, so our lifting operation only ``lifts'' the
substitution by one index.

\begin{code}
liftE1    :: SubE g g' -> SubE (ty:g) (ty:g')
liftE1 s   = ConsE (VarE SZ) (CompE s IncE)
\end{code}

In contrast, when we traverse under a type binder, we bind a list of type
variables. Therefore, we need the following operation that increments the
indices of free type variables stored in the substitution.  Here, we see the
benefit in working with a concrete representation of substitution as compared
to higher-order functions --- we can define this operation directly over the
structure of the substitution.

\begin{code}
incSubE  :: Sing k
         -> SubE g g'
         -> SubE (IncList k g) (IncList k g')
incSubE k IdE             = IdE
incSubE k IncE            = IncE
incSubE k (ConsE e s)     =
  ConsE (substTy (SInc k) e) (incSubE k s)
incSubE k (CompE s1 s2)   =
  CompE (incSubE k s1) (incSubE k s2)
\end{code}

With these two operations, we can define the term substitution operation. In
the case of variables, this operation dispatches to a helper function that
looks up the value of the variable in the substitution. (Compare |applyES|
below with |applyE| above.) Otherwise, the substitution function works
homemomorphically over the structure of expressions, using the |liftE1| and
|incSubE| functions above to modify the substitution when traversing under
binders.

\begin{code}
substE  :: SubE g g' -> Exp g ty
        -> Exp g' ty
substE s BaseE          = BaseE
substE s (VarE v)       = applyES s v
substE s (AppE e1 e2)   = AppE (substE s e1) (substE s e2)
substE s (LamE ty e)    = LamE ty (substE (liftE1 s) e)
substE s (TyLam k e)    = TyLam k (substE (incSubE k s) e)
substE s (TyApp e tys)  = TyApp (substE s e) tys

applyES  :: (Idx g n ~ Just ty)
         => SubE g g' -> Sing n -> Exp g' ty
applyES IdE            v       = VarE v
applyES IncE           v       = VarE (SS v)
applyES (ConsE e s)    SZ      = e
applyES (ConsE e s)    (SS m)  = applyES s m
applyES (CompE s1 s2)  v       = substE s2 (applyES s1 v)
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%if False
\subsection{Stream interpretation}

We can visualize substitutions as infinite lists of types, where the ith type
in the list is the substitution for variable i.

\begin{code}
instance Index Sub where
  type Element Sub = Ty
  s !! x = applyS s x
\end{code}

\begin{code}
instance Enum Ty where
  toEnum x = VarTy (toEnum x)
  fromEnum (VarTy x) = fromEnum x
  fromEnum _ = error "cannot do it"
\end{code}


\begin{code}
toList :: Sub -> [Ty]
toList (x :· y)           = x : toList y
toList (Inc n)            = [VarTy n, VarTy (n + 1) ..]
toList (s1 :∘ s2)         = substList s2 (toList s1)
\end{code}

We can express the connection between the two interpretations of substitutions
using the following quickCheck property.  In other words, at any index |n|, the
result of |applyS| is the same as first converting the substitution to a list
and then accessing the |n|th element.

\begin{code}
prop_applyS_toList :: Sub -> Nat -> Bool
prop_applyS_toList s x =
  s !! x == toList s !! x
\end{code}

(Note: in our first version of this function, quick check did not catch a bug
in the |Lift Z s| case even with a 1000 tests.)

\begin{code}
prop_toList_fromList tys =
  take (length tys) (toList (fromList tys)) == tys
\end{code}


%endif


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%if False

This is the polymorphic function specialization. 

\begin{code}

prop_substFreshList g k tys =
  ((k <= length tys) == False)  ==>
  substList (fromList tys) (incList k g) == (incList (k - (length tys)) g)

ax_SubstFreshList :: forall g k tys.
  ((k <= Length tys) ~ False) =>
  SubstList (FromList tys) (IncList k g) :~:
  IncList (Minus k (Length tys)) g
ax_SubstFreshList = unsafeCoerce Refl

ax_SubstFresh :: forall t k tys.
  ((k <= Length tys) ~ False) =>
  Subst (FromList tys) (Subst (Inc k) t) :~:
  Subst (Inc (Minus k (Length tys))) t
ax_SubstFresh = unsafeCoerce Refl




$(singletons [d|
    specPolyTy :: Nat -> Ty -> [Ty] -> Ty
    specPolyTy k t1 tys =
      if k <= length tys then
        -- we have enough type arguments (ignore extras)
        subst (fromList (take k tys)) t1
      else
        -- we don't have enough type arguments (regeneralize)
        PolyTy (minus k (length tys)) (subst (fromList tys) t1)

    upN :: Nat -> [Ty]
    upN n = go Z where
      go m = 
        if n == m then []
        else (VarTy m : go (S m))
      
  |])

prop_length_upN n = length (upN n) == n

ax_Length_UpN :: forall n.
  Length (UpN n) :~: n
ax_Length_UpN = unsafeCoerce Refl

prop_subst_upN k ty =
  subst (fromList (upN k)) (subst (lift k (Inc k)) ty) == ty

ax_Subst_UpN :: forall k ty.
  (Subst (FromList (UpN k)) (Subst (Lift k (Inc k)) ty)) :~: ty
ax_Subst_UpN = unsafeCoerce Refl


-- Deriving the specialization rule from the above
spec :: forall g k ty tys. Sing g ->
  Exp g (PolyTy k ty) -> Sing tys -> Exp g (SpecPolyTy k ty tys)
spec g e1 tys =
  case typeOf g e1 of
    (SPolyTy k ty) ->
       case k %<= sLength tys of
         STrue
           | Refl <- ax_Length_Take @k @tys
           -> TyApp e1 (sTake k tys)         
         SFalse
           | Refl <- ax_SubstFreshList @g @k  @tys
           , Refl <- ax_SubstFresh     @ty @k @tys
           , Refl <- ax_Length_UpN  @k
           , Refl <- ax_Subst_UpN      @k @ty
           -> let
                x :: Exp (SubstList (FromList tys) (IncList k g))
                          (Subst (FromList tys) ty)
                x = substTy (sFromList tys) w
                
                z :: Exp (IncList k g) (PolyTy k (Subst (Lift k (Inc k)) ty))
                z = substTy (SInc k) e1

                w :: Exp (IncList k g) (Subst (FromList (UpN k))
                                              (Subst (Lift k (Inc k)) ty))
                w = TyApp z (sUpN k)
                
                fact :: SubstList (FromList tys) (IncList k g) :~:
                        IncList (Minus k (Length tys)) g
                fact = Refl
                
              in
                TyLam (sMinus k (sLength tys)) x 
\end{code}

%endif

\section{Type-safe evaluation and reduction}

Once we have defined the substitution operations, the addition of polymorphism
does not make the definition of a type-safe evaluator any more difficult.

First, define a data type of values. Values must be closed, but may be of any
type.  They include Base values, functions and polymorphic terms.  In the last
two cases, the body of the values are suspended expressions.

%if False
\begin{code}
type One a = '[a]
type Nil   = '[]
\end{code}
%endif

Because of the deep embedding of types, we also produce a deep embedding of
values. In other words, we are producing a subset of System F expressions
instead of Haskell values.

\begin{code}
data Val ty where
  BaseV   :: Val BaseTy
  LamV    :: Sing t1              -- type of binder
          -> Exp (One t1) t2      -- body of abstraction
          -> Val (FnTy t1 t2)
  TyLamV  :: Sing k               -- num of tyvars to bind
          -> Exp Nil t2           -- body of type abstraction
          -> Val (PolyTy k t2)
\end{code}

The evaluator translates terms that are already values to their corrsponding
value-tagged forms.  For the two application cases, GHC can determine that the
pattern matches are exhaustive (i.e. the only value of type |FnTy t1 t2| is
|LamV|). In these two cases, the evaluator uses the substitution operations
above to $\beta-reduce$ the applications.

Furthermore, note that evaluation is not a structural recursive
operation. This definition would not be accepted by Coq or Agda.

\begin{code}
oneSubE :: Exp g ty -> SubE (ty:g) g
oneSubE e = ConsE e IdE
\end{code}

\begin{code}
eval :: Exp Nil ty -> Val ty
eval BaseE          = BaseV
eval (LamE t1 e1)   = LamV t1 e1
eval (AppE e1 e2)   =
  case eval e1 of
   LamV _ e1' ->
     eval (substE (oneSubE e2) e1')
eval (TyLam k e1)   = TyLamV k e1
eval (TyApp e tys)  =
  case eval e of
    TyLamV k e' ->
      eval (substTy (sFromList tys) e')
\end{code}


For parallel reduction, the code is also straightforward. However, in the
case of type abstraction we need to show an equality.

\begin{code}
par :: forall g ty. Exp g ty -> Exp g ty
par BaseE          = BaseE
par (VarE v)       = VarE v
par (AppE e1 e2)   =
  case par e1 of
    LamE _ e1'  -> substE (oneSubE e2) e1'
    e1'         -> AppE e1' e2
par (LamE ty e)    = LamE ty (par e)
par (TyApp e tys)  =
  case par e of
    TyLam k e' | Refl <- axiom_SubstInc @g tys
         -> substTy (sFromList tys) e'
    e1'  -> TyApp e1' tys
    
par (TyLam k e)    = TyLam k e
\end{code}

In this case, the substitution in the context should have no effect as it is
preceeded by incrementing all type variables out of the way.

\begin{code}
axiom_SubstInc :: forall g tys.
  Sing tys -> SubstList (FromList tys) (IncList (Length tys) g) :~: g
axiom_SubstInc = unsafeCoerce Refl

prop_SubstInc :: [Ty] -> [Ty] -> Bool
prop_SubstInc g tys = 
  substList (fromList tys) (incList (length tys) g) == g

\end{code}

%include cps.lhs


\section{Related Work}

A Type-Preserving Compiler in Haskell
Louis-Julien Guillemette Stefan Monnier
ICFP 2008
Uses "standard" de Brujn Indices to represent System F types
"Pre-datakinds"  uses newtypes to introduce constructors for
All/Var in Type.

Revisiting the CPS Transformation and its Implementation
Francois Pottier

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
\section{Appendix: arbitrary instance}

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

instance Arbitrary Ty where
  arbitrary = sized (gt Z) where
    base n = oneof
       (return BaseTy : [return (VarTy k)
                        | k <- upto (fi 5) ])
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
    base = oneof [Inc <$> arbitrary]
    gt m =
      if m <= 1 then base else
      let m' = m `div` 2 in
      frequency
      [(1, base),
       (1, (:·)    <$> arbitrary <*> gt m'), 
       (1, (:∘)    <$> gt m'     <*> gt m')]

  shrink (Inc n) = [Inc n' | n' <- shrink n]
  shrink (t :· s)   = s : [t' :· s' | t' <- shrink t, s' <- shrink s]
  shrink (s1 :∘ s2) = s1 : s2 :
    [s1' :∘ s2 | s1' <- shrink s1, s2' <- shrink s2]                       


prop_cons_sub ty ss tt =
  subst (ty :· ss) (subst (Inc 1) tt) == subst ss tt


return []
runTests = $forAllProperties qc

\end{code}


\begin{code}
qc :: Testable prop => prop -> IO Result
qc = quickCheckWithResult (stdArgs { maxSuccess = 1000 })

\end{code}


\end{document}
