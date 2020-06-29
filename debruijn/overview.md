## Strongly-typed System F in GHC

Here is a challenge: Can you represent System F, using a strongly-typed term
representation in your favorite typed programming language?

This project demonstrates my solution to this challenge using the Haskell
programming language, assisted by the
[singletons](https://hackage.haskell.org/package/singletons) library. Because
I had a lot of fun completing this challenge, I wrote up this solution as a
tutorial of dependently-typed programming in GHC.

*Why strongly-typed ASTs?*

With a strongly-typed term representation, only well-typed terms can be
constructed. That means that language tools that manipulate these data
structures must respect the object language type system. For example, GHC's
type system can show that the definition of capture-avoiding substitution
preserves the types of the object language; ruling out certain sorts of
bugs. Similarly, other operations that manipulate typed terms, such as
interpreters, compilers and optimizers can be shown type-preserving by
implementing them using this representation in GHC.

### Chalmers Seminar video

<iframe width="560" height="315" src="https://www.youtube.com/embed/j2xYSxMkXeQ" frameborder="0" allow="accelerometer; autoplay; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>

### Road Map

This development is broken into four main parts, listed below. 

    Part I                      Part II
    Weak types / STLC           Strong types / STLC

    Part III                    Part IV
    Weak types / System F       Strong types / System F

- [Part I: Representing binding and substitution using de Bruijn indices](debruijn1.md)

    The first part is a tutorial overview of de Bruijn indices and substitution, culminating in an implementation of the simply-typed lambda  calculus (STLC). Although there are many 
    examples of this sort of implementation already, the version presented here introduces a novel, reusable library for substitution, which simplifies the language-specific parts of the implementation. 

- [Part II: Adding strong types to STLC](debruijn2.md)

    Next, we show how to add type indices to the AST developed in the previous section to constrain the representation to only *well-typed* terms of STLC. None of the code changes in this part, just the type annotations in the language definition and in the substitution library.

- Part IIa: Optimized de Bruijn representation  (*Optional part, may be skipped*)

   *This part does not have a separate write-up. Instead it appears in the comments of the files:* [SubstTypedOpt](src/SubstTypedOpt.hs) and [SimpleTypedOpt](src/SimpleTypedOpt.hs)

   Simple definitions of substitution for de Bruijn indices can be inefficient. In these files, we show how to rectify that by the introduction of delayed substitutions at binders. This optimization can even be hidden behind an abstract type for binders resulting in a library for substitution that is both easy to use and efficient. Furthermore, this optimization is compatible with the strong types from Part II. 

- [Part III: Untyped ASTs for System F](debruijn3.md)
  
  Using the substitution library developed in Part I, we extend our weakly-typed implementation of STLC to System F. 

- [Part IV: Strongly-typed AST for System F](debruijn4.md)

  Finally, we make a well-typed AST for System F, and define type and term
  substitution using both the weakly-typed (for System F types) and strongly-typed (for
  System F terms) substitution libraries. This part relies on the use of the
  singletons library.

- Part IVa: Optimized de Bruijn representation

  *Again no write up, refer to the file:* [PolyTypedOpt](src/PolyTypedOpt.hs)
  
  As a last (optional) treat, we show that it is straightforward to convert the well-typed version from part IV to use the *optimized* substitution library.

- Examples
  
  If you'd like to go deeper, there are several additional examples of operations that use the [PolyTyped](src/PolyTyped.hs) System F representation developed in Part IV.

  - [TypeCheck](src/TypeCheck.hs): A type checker that translates the weakly-typed AST to the strongly-typed AST (or fails if the term does not type check).
  - [CPS](src/Cps.hs): CPS-conversion algorithm for the strongly-typed System F. The type indices show that this 
  transformation is type-preserving.
  - [SubstScoped](src/SubstScoped.hs) and [SimpleScoped](src/SimpleScoped.hs): Just keep track of scopes, not types
  - [SubstInf](src/SubstInf.hs), [SubstTypedInf](src/SubstTypedInf.hs), [SimpleTypedInf](src/SimpleTypedInf.hs): 
     represent substitutions using a lazy list. This is significantly more difficult to make strongly typed.
 
- [Bibliography](bibliography.md): Sources and related work. This tutorial is
  inspired by an extensive literature of de Bruijn representations and
  strongly-typed term representations.
