Reasoning with defunctionalized, parallel substitution

This challenge is based on the representation of variable binding 
called parallel substitution, used for example, by the 
[Autosubst](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf) tool.

However, most places use functions to represent renamings and substitutions.

In this case, I'd like a concrete data structure for substitutions, so I've
defunctionalized the implementation. Note that the definition of composeSub
cannot be part of the data structure because its application requires the 
definition of subst.

Furthermore, I need to be able to implement n-ary substitutions. 

So the challenge is to prove that my definition of composeSub is actually 
substitution composition. See the last lemma in the file.

