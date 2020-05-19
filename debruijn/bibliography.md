# Bibliography

- Benton, Hur, Kennedy, McBride. *Strongly-Typed Term Representations in Coq.* Journal of Automated Reasoning.

Demonstrates this technique for encoding System F terms in the Coq proof assistant. Like here, the substitution operation is defined in terms of parallel substitutions. However, because this work is done in a proof assistant, the substitution operation must be shown to be terminating. This is difficult because the operation is not structurally recursive (note that `applyS` depends on `subst`, which depends again on `applyS`.) The solution is to define the operation in stages, first as a renaming operation and then as a full substitution.

This version also does not defunctionalize substitutions (as we do here), but instead defines typed substitutions as functions of the following type.

```haskell
      type Sub E g g' = forall t, Idx g t -> E g' t
```

- Pottier. *Revisiting the CPS Transformation and its Implementation. Draft paper, 2017. 
  http://gallium.inria.fr/~fpottier/publis/fpottier-cps.pdf

Uses the [Autosubst](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf) to represent variable binding in a simply-typed language and then proves CPS transformation correct. Doesn't use a strongly-typed term representation. Notes that this implementation is inefficient and replaces it with de Bruijn level based representation instead.

# NOTES
ß
However, most places use functions to represent renamings and substitutions.

In this case, I'd like a concrete data structure for substitutions, so I've
defunctionalized the implementation. Note that the definition of composeSub
cannot be part of the data structure because its application requires the 
definition of subst.

Furthermore, I need to be able to implement n-ary substitutions. 

So the challenge is to prove that my definition of composeSub is actually 
substitution composition. See the last lemma in the file.

[Maybe useful reference](https://dl.acm.org/citation.cfm?id=2693163)