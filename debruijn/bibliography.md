# Bibliography

This is a partial list of papers that were influential in the development of
this project or cover related topics. It is not a comprehensive bibliography
of work related to de Bruijn indices or strongly-typed representations.

## Strongly-typed representations of System F 

- Benton, Hur, Kennedy, McBride. *Strongly-Typed Term Representations in Coq.* 
Journal of Automated Reasoning. 2012

This paper is the main inspiration for this work and demonstrates an encoding
of System F terms in the Coq proof assistant. Like here, the substitution
operation is defined in terms of parallel substitutions. However, because this
work is done in a proof assistant, the substitution operation must be shown to
be terminating. This is difficult because the operation is not structurally
recursive (note that in [Subst](src/Subst.hs) and instances, the function
`applySubst` depends on `subst`, which depends again on `applySubst`.) The
solution to well-foundedness is to define the operation in stages, first as a
renaming operation and then as a full substitution.

Benton et al. defines typed substitutions as functions of the following type.

```haskell
type Sub E g g' = forall t, Idx g t -> E g' t
```

Here, the [Subst](src/Subst.hs) module defunctionalizes these functions as a
data structure so that they are easier to work with in Haskell's type
level. This defunctionalization also enables optimizations via smart
constructors in [SubstOpt](src/SubstOpt.hs).

- Louis-Julien Guillemette, Stefan Monnier. *[A type-preserving compiler in Haskell](https://dl.acm.org/doi/10.1145/1411203.1411218).* ICFP 2008: 75-86

This impressive paper from 2008 represents several stages of a System F
compiler in Haskell, using GADTs, type families and functional
dependencies. Polymorphic type variables are represented using de Bruijn
indices, but term variables are sometimes expressed using HOAS (for CPS
conversion) and sometimes expressed using de Bruijn indices (for closure
conversion, and hoisting). Because this is a compiler, the paper only proves
that the various transformations are type-preserving. It does not define a
general substitution operation for System F terms.

- Pfenning and Lee, *[Metacircularity in the polymorphic λ-calculus](https://www.sciencedirect.com/science/article/pii/030439759090109U)*. Theoretical Computer Science 89 (1991) 137-159. 

Constructs a well-typed representation of System F using a higher-order
abstract syntax representation and a shallow embedding of types. They need a
more expressive language (i.e. a language with impredicative kind
polymorphism) to represent System F. Although GHC has such kind polymorphism,
the lack of anonymous functions in the type level makes this sort of
representation difficult to work with in GHC.

- James Chapman, Roman Kireev, Chad Nester, and Philip Wadler. *[System F in Agda, for fun and profit](https://files.zotero.net/eyJleHBpcmVzIjoxNTkyODQ5NjIzLCJoYXNoIjoiNTlkODRjZDU5YmQ2M2E2NTVjMDhiM2VhNTdlYmM3NmQiLCJjb250ZW50VHlwZSI6ImFwcGxpY2F0aW9uXC9wZGYiLCJjaGFyc2V0IjoiIiwiZmlsZW5hbWUiOiJDaGFwbWFuIGV0IGFsLiAtIDIwMTkgLSBTeXN0ZW0gRiBpbiBBZ2RhLCBmb3IgZnVuIGFuZCBwcm9maXQucGRmIn0%3D/1eaedb49fe3b8c3b8247ece24aca96db1f70cf460feb6404c1efb7ac627e2c5a/Chapman%20et%20al.%20-%202019%20-%20System%20F%20in%20Agda%2C%20for%20fun%20and%20profit.pdf). MPC 2019: Mathematics of Program Construction pp 255-297.

A well-typed representation of System F-omega using the Agda proof assistant. 

- Carsten Schürmann, Dachuan Yu, Zhaozhong Ni. *[A Representation of Fomega in LF](https://www.itu.dk/people/carsten/papers/safeIL.ps.gz)*. Electronic Notes in Theoretical Computer Science. Vol 58, No.1. 2001.

A well-typed representation of System F-omega using the Twelf proof assistant. 

## Frameworks, tools, techniques and libraries for working with de Bruijn indices

- N.G. de Bruijn. *[Lambda Calculus notation with nameless dummies, a tool for
automatic formula manipulation, with application to the Church-Rosser
theorem](https://www.sciencedirect.com/science/article/pii/1385725872900340)*. Indagationes
Mathematicae (Proceedings) Volume 75, Issue 5, 1972, Pages 381-392.


- Steven Schäfer, Gert Smolka, Tobias Tebbi *[Completeness and Decidability of
  de Bruijn Substitution Algebra in
  Coq](https://dl.acm.org/citation.cfm?id=2693163)* CPP '15

Describes the foundations of the
[Autosubst](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf)
system that uses parallel substitution for de Bruijn indices to support
binding in languages represented in the Coq proof assistant.

- Guillaume Allais, James Chapman, Conor Thomas McBride, James
  McKinna. *[Type-and-scope safe programs and their
  proofs](https://dl.acm.org/doi/10.1145/3018610.3018613)*. CPP
  '17. Agda-based framework for a strongly-typed representation of STLC, with
  semantic interpretation. Also defines an interface for languages, though in
  a "finally tagless" style.

- Richard Bird and Ross Paterson. *[De Bruijn Notation as a Nested
  Datatype](http://www.staff.city.ac.uk/~ross/papers/debruijn.html)*. Journal
  of Functional Programming, 9(1):77-91, January 1999.

Show how to use nested datatypes to enforce a well-scoped representation of
lambda terms. This is similar to indexing the expression with a type level
natural number indicating the nesting depth (i.e. We can relate the `Maybe`
type constructor with Nat's `Succ`.) Notice that the "well-scoped" index type
(often called `Fin`)

```
data Idx (n :: Nat) where
   Z :: Idx (S n)
   S :: Idx n -> Idx (S n)
```

is isomorphic to the set of types formed by sequences of `Maybe`s applied to `Void`.

```
Void                 == Idx Z          contains 0 elements
Maybe Void           == Idx (S Z)      contains 1 element
Maybe (Maybe Void)   == Idx (S (S Z))  contains 2 elements
...
```

- Edward Kmett. *[Bound](https://www.schoolofhaskell.com/user/edwardk/bound)*. December 2015.

A Haskell library for working with well-scoped terms using de Bruijn indices.

- Pottier. *[DB lib](https://github.com/coq-community/dblib)* Coq library for de Bruijn indices. 2013.

- Pottier. *[Revisiting the CPS Transformation and its
  Implementation](http://gallium.inria.fr/~fpottier/publis/fpottier-cps.pdf). Draft
  paper, 2017.*

This paper uses the
[Autosubst](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf)
library to represent variable binding in a simply-typed language and then
proves CPS transformation correct.  It doesn't use a strongly-typed term
representation. Pottier notes that this implementation is inefficient and replaces it
with de Bruijn level based representation instead for efficiency. This paper
is the inspiration for the strongly-typed [Cps](src/Cps.hs) transformation
example.
