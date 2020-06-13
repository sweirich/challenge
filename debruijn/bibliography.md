# Bibliography

- Benton, Hur, Kennedy, McBride. *Strongly-Typed Term Representations in Coq.* Journal of Automated Reasoning. 2012

This paper is the main inspiration for this work and 
demonstrates an encoding of System F terms in the Coq proof assistant. Like here, the substitution operation is defined in terms of parallel substitutions. However, because this work is done in a proof assistant, the substitution operation must be shown to be terminating. This is difficult because the operation is not structurally recursive (note that in [Subst](src/Subst.hs) and instances, the function `applySubst` depends on `subst`, which depends again on `applySubst`.) The solution to well-foundness is to define the operation in stages, first as a renaming operation and then as a full substitution.

This version defines typed substitutions as functions of the following type.

```haskell
type Sub E g g' = forall t, Idx g t -> E g' t
```
The [Subst](src/Subst.hs) module defunctionalizes these functions as a data structure so that they are easier to work with in Haskell's type level. This defunctionalization also enables optimizations via smart constructors in [SubstOpt](src/SubstOpt.hs).

- Pottier. *[Revisiting the CPS Transformation and its Implementation](http://gallium.inria.fr/~fpottier/publis/fpottier-cps.pdf). Draft paper, 2017.*

This paper uses the [Autosubst](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf) library to represent variable binding in a simply-typed language and then proves CPS transformation correct.  It doesn't use a strongly-typed term representation. Notes that this implementation is inefficient and replaces it with de Bruijn level based representation instead for efficiency. This  paper is the inspiration for the strongly-typed [Cps](src/Cps.hs) transformation example.

- Louis-Julien Guillemette, Stefan Monnier. *[A type-preserving compiler in Haskell](https://dl.acm.org/doi/10.1145/1411203.1411218).* ICFP 2008: 75-86

This impressive paper from 2008 represents several stages of a System F compiler in Haskell, using GADTs, type families and functional dependencies. Polymorphic type variables are represented using de Bruijn indices, but term variables are sometimes expressed using HOAS (for CPS conversion) and sometimes expressed using de Bruijn indices (for closure conversion, and hoisting).

- Steven Schäfer, Gert Smolka, Tobias Tebbi *[Completeness and Decidability of de Bruijn Substitution Algebra in Coq](https://dl.acm.org/citation.cfm?id=2693163)* CPP '15

Describes the foundations of the [Autosubst](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf) system that uses parallel substitution for de Bruijn indices to support binding in languages represented in the Coq proof assistant. 
