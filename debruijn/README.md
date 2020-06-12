# Strongly-typed System F in GHC

## Introduction

This project demonstrates how to define a strongly-typed term representation for System F terms in GHC using the singletons library.

The explanation is accompanied by fully worked out example code in this repo. To get started, follow the road map below.

*Why strongly-typed ASTs?*
With a strongly-typed term representation, only well-typed terms can be constructed. Language tools that manipulate such data structures can be sure that certain invariants are maintained by the system. For example, the definition of capture-avoiding substitution can be difficult to get correct from scratch. By working with a typed representation, we can be sure that there are no scope-errors in our interpreters, compilers and optimizers and that our transformations are type preserving.

## Road Map

This development is broken into four main parts, listed below. 

    Part I                      Part II
    Weak types / STLC           Strong types / STLC


    Part III                    Part IV
    Weak types / System F       Strong types / System F

- [Part I: Representing binding and substitution using de Bruijn indices](debruijn1.md)

    *Reference files:* [Subst](src/Subst.hs) and [Simple](src/Simple.hs)

    The first part is a tutorial overview of de Bruijn indices and substitution, culminating in an traditionally typed implementation of the simply-typed lambda  calculus (STLC). If you are new to using de Bruijn indices, this part will walk you through the details and provide a general purpose recipe for a Haskell implementation of binding.  Even if you are not new to de Bruijn indices, you should take a look at this implementation because there are *different* versions of substitution with this representation.

- [Part II: Adding strong types to STLC](debruijn2.md)

    *Reference files:* [SubstTyped](src/SubstTyped.hs) and [SimpleTyped](src/SimpleTyped.hs)

    Next, we show how to add type indices to the ASTs developed in the previous section to constrain the representation to only well-typed terms of STLC. None of the code changes in this part, just the types.

- Part IIa: Optimized de Bruijn representation  (*Optional part, may be skipped*)

   *Reference files:* [SubstTypedOpt](src/SubstTypedOpt.hs) and [SimpleTypedOpt](src/SimpleTypedOpt.hs)

   Simple definitions of substitution for de Bruijn indices can be inefficient. In these files, we show how to rectify that by the introduction of delayed substitutions at binders. This optimization can even be hidden behind an abstract type for binders resulting in a library for substitution that is both easy to use and efficient. Furthermore, this optimization is compatible with the strong types from Part II. 

- [Part III: Untyped ASTs for System F](debruijn3.md)

  *Reference file:* [Poly](src/Poly.hs)
  
  Using the substitution infrastructure developed in Part I, we extend our   implementation of STLC to System F. 

- [Part IV: Strongly-typed AST for System F](debruijn4.md)

  *Reference file:* [PolyTyped](src/PolyTyped.hs) and [SubstProperties](src/SubstProperties.hs)
  
  Finally, we make a well-typed AST for System F, using both the untyped (for System F types) and typed (for System F terms) substitution infrastructures.

- Part IVa: Optimized de Bruijn representation

  *Reference file:* [PolyTypedOpt](src/PolyTypedOpt.hs)
  
  As a last (optional) treat, we show that it is straightforward to convert the well-typed version from part IV to use the *optimized* substitution library.

- Additional Examples
  
  If you'd like to go deeper, there are several additional examples of operations that use the [PolyTyped](src/PolyTyped.hs) module developed in Part IV.

  - [TypeCheck](src/TypeCheck.hs): A type checker that translates an untyped AST to a typed AST
  - [CPS](src/Cps.hs): CPS-conversion algorithm for the strongly-typed System F AST
  - [SubstScoped](src/SubstScoped.hs) and [SimpleScoped](src/SimpleScoped): Just keep track of scopes, not types

- [Bibliography](bibliography.md): Sources and related work

## Requirements

This code requires a recent version of singletons (2.6) to compile, which itself requires GHC 8.8. Earlier compilers and versions of the library will not work. For convenience, we suggest that you compile using the `stack` tool, which will automatically download and install the correct version of the compiler and librarie.

## Disclaimer

*Disclaimer*: there is a long-standing discussion in the Haskell community about the use of fancy types in industrial-strength libraries. This project does not describe an industrial use of Haskell so does not add anything to that discussion. Indeed, it's not at all clear that you would want to use this approach in your compiler for your polymorphic language; it's untested in practice and designed to make a point, not solve a problem. 

So why do I care about this topic? First, I've wanted to have deeper understanding of de Bruijn representations for some time now and working with strongly-typed versions forces me to look closer at what is going on. And in doing so, I've come up with a design that I'm pretty proud of. Second, I also like to explore (and demonstrate) the state of the art in dependently-typed programming in Haskell, especially with the assistance of the [singletons](https://hackage.haskell.org/package/singletons) library. But, most importantly, I find puzzles like this one fun to think about, and would like to share that fun.
