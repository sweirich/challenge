# Strongly-typed System F in GHC

## Introduction

This project demonstrates how to define a strongly-typed term representation for System F terms in GHC using the [singletons](https://hackage.haskell.org/package/singletons) library. Along the way it develops several versions of a reusable library for substitution, and explains the technique of using de Bruijn indices to represent variables.

The explanation is accompanied by fully worked out example code. To get started, follow the road map below, paying close attention to the source files referred to in each section.

*Why strongly-typed ASTs?*

With a strongly-typed term representation, only well-typed terms can be
constructed. That means that language tools that manipulate these data
structures must respect the object language type system. For example, the
GHC's type system can show that the definition of capture-avoiding
substitution preserves the types of the object language. Similarly, other
operations that manipulate typed terms, such as interpreters, compilers and
optimizers can be shown type preserving within GHC.

## Road Map

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
  substitution using both the untyped (for System F types) and typed (for
  System F terms) substitution libraries. This part relies on the use of the
  singletons library.

- Part IVa: Optimized de Bruijn representation

  *Again no write up, refer to the file:* [PolyTypedOpt](src/PolyTypedOpt.hs)
  
  As a last (optional) treat, we show that it is straightforward to convert the well-typed version from part IV to use the *optimized* substitution library.

- Examples
  
  If you'd like to go deeper, there are several additional examples of operations that use the [PolyTyped](src/PolyTyped.hs) System F representation developed in Part IV.

  - [TypeCheck](src/TypeCheck.hs): A type checker that translates the untyped AST to the typed AST (or fails if the term does not type check).
  - [CPS](src/Cps.hs): CPS-conversion algorithm for the strongly-typed System F. The type indices show that this 
  transformation is type preserving. 
  - [SubstScoped](src/SubstScoped.hs) and [SimpleScoped](src/SimpleScoped): Just keep track of scopes, not types

- [Bibliography](bibliography.md): Sources and related work

## Requirements

This code requires a recent version of singletons (2.6) to compile, which itself requires GHC 8.8. Earlier compilers and versions of the library will not work. For convenience, we suggest that you compile using the `stack` tool, which will automatically download and install the correct version of the compiler and libraries.

## Disclaimer

*Disclaimer*: there is a long-standing discussion in the Haskell community about the use of fancy types in industrial-strength libraries. This project does not describe an industrial use of Haskell so does not add anything to that discussion. Indeed, it's not at all clear that you would want to use this approach in your compiler for your polymorphic language; it's untested in practice and designed to make a point, not solve a problem. 

So why do I care about this topic? First, I've wanted to have deeper understanding of de Bruijn representations for some time now and working with strongly-typed versions forces me to look closer at what is going on. And in doing so, I've come up with a design that I'm pretty proud of. Second, I also like to explore (and demonstrate) the state of the art in dependently-typed programming in Haskell, especially with the assistance of the [singletons](https://hackage.haskell.org/package/singletons) library. But, most importantly, I find puzzles like this one fun to think about, and would like to share that fun.
