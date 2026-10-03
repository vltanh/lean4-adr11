# Rooted tree shapes on three, four and five taxa

**Source.** A. Cayley, *On the theory of the analytical forms called trees*, Philos. Mag. 13
(1857) 172–176.

**Statement used.** There are 2 unlabelled rooted tree shapes on three leaves, 5 on four leaves
and 12 on five leaves, binary or not.

**Use in the paper.** Section 5 and Appendix C (proof of Proposition 11) treat the nonbinary
species trees shape by shape: on five taxa, the three binary shapes of Section 4 and the nine
nonbinary shapes `P₁, …, P₉` of Table 6.

**In Lean.** `Shapes.lean` lists representatives (`shapes3`, `shapes4`, `shapes5`) and proves
`cayley_shapes`: every hierarchy on `Fin 3`, `Fin 4` or `Fin 5` is a relabelling of exactly one
of them. The proof distinguishes the shapes by an invariant (the number of nested pairs of
clusters) and reduces a hierarchy to a rooting of a standard unrooted tree
(`ADR11/Trees/Classify.lean`).

The formal proof of Proposition 11 does not need the count: it fixes the unrooted species tree
first (Corollary 6) and then distinguishes its rootings, through the same normal forms of
`ADR11/Trees/Classify.lean`. `cayley_shapes` is proved because the paper states the count.
