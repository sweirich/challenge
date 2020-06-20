# Strongly-typed System F in GHC

This tutorial demonstrates a strongly-typed term representation for System F
terms in GHC using the
[singletons](https://hackage.haskell.org/package/singletons) library. Along
the way it develops several versions of a reusable library for substitution
with de Bruijn indices.

To get started, follow the [road map](overview.md), paying close attention to
the source files referred to in each section.

## Requirements

This code requires a recent version of singletons (2.6) to compile, which
itself requires GHC 8.8. Earlier compilers and versions of the library will
not work. For convenience, we suggest that you compile using the `stack` tool,
which will automatically download and install the correct version of the
compiler and libraries.

## Disclaimer

*Disclaimer*: there is a long-standing discussion in the Haskell community
about the use of fancy types in industrial-strength libraries. This project
does not describe an industrial use of Haskell so does not add anything to
that discussion. Indeed, it's not at all clear that you would want to use this
approach in your compiler for your polymorphic language; it's untested in
practice and designed to make a point, not solve a problem.

So why do I care about this topic? First, I've wanted to have deeper
understanding of de Bruijn representations for some time now and working with
strongly-typed versions forces me to look closely at what is going on. Second,
I also like to explore (and demonstrate) the state of the art in
dependently-typed programming in Haskell, especially with the assistance of
the [singletons](https://hackage.haskell.org/package/singletons) library. But,
most importantly, I find challenges like this one fun to think about and would
like to share what I have learned.
