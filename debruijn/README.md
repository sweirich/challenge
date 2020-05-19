# Strongly-typed System F in GHC

## Introduction

This project demonstrates how to define a strongly-typed term representation for System F terms in GHC using the singletons library.

The explanation is accompanied by the fully worked out example code in the github repostory.

*Why strongly-typed ASTs?*
With a strongly-typed term representation, only well-typed terms can be constructed. Language tools that manipulate such datastructures can be sure that certain invariants are maintained by the system. For example, the definition of capture-avoiding substitution is often difficult to get correct from scratch. By working with a typed representation, we can be sure that there are no scope-errors in our interpreters, compilers and optimizers and that our transformations are type preserving. 

Note: there is a long-standing discussion in the Haskell community about the benefit of fancy types to industrial-strength libraries. This project does not describe industrial use of Haskell so will not add *anything* to that discussion. Indeed, it's not at all clear that you would want to use this approach in your compiler for your polymorphic language. Although variable binding is difficult to get right, there are already tools, such as [Unbound] and [Bound](https://hackage.haskell.org/package/bound), that can help you develop a correct implementation of binding through generic programming.

So why do I care about this topic? First, I've wanted to have deeper understanding of de Bruijn representations for some time now and working with strongly-typed versions forces me to look closer at what is actually going on. Second, I'd also like explore (and demonstrate) the state of the art in dependently-typed programming in Haskell, especially with the assistance of the singletons library. But, most importantly, I find puzzles like this fun to think about. (And we all need a little more fun in these uncertain times.)


## Table of Contents

- [Part I](debruijn1.md): Representing binding and substitution using de Bruijn indices

The first part is a tutorial overview of de Bruijn indices and substitution, culminating in an traditionally typed implmentation of the simply-typed lambda calculus (STLC). If you are new to using de Bruijn indices, this part will walk through the details and provide a general purpose recipe for a Haskell implementation.

- [Part II](debruijn2.md): Adding strong types to STLC

- Part III: Weak and Strong-typed ASTs for System F

- [Bibliography](bibliography.md): Sources and related work

