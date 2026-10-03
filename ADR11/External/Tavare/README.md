# Tavaré's formula (equation (2) of the paper)

**Source.** S. Tavaré, *Line-of-descent and genealogical processes, and their applications in
population genetics models*, Theoret. Population Biol. 26 (1984) 119–164.

**Statement.** For `1 ≤ j ≤ i`, the probability that `i` lineages of Kingman's coalescent have
coalesced into `j` lineages after a time `t` is

```text
g_ij(t) = ∑_{k=j}^{i} exp(-k(k-1)t/2) (2k-1)(-1)^{k-j} / (j! (k-j)! (j+k-1)) ∏_{m=0}^{k-1} (j+m)(i-m)/(i+m).
```

**Use in the paper.** Section 3 states it as equation (2); every explicit gene tree probability of
the paper is a sum of products of the `g_ij`.

**In Lean.** `Formula.lean` proves the formula for `deathProb i j t`, the transition probability
of the pure death process on the number of lineages with rates `k(k-1)/2`
(`deathProb_eq_tavare`), through the entries of the powers of its generator
(`deathPow_eq_tavare`), which a telescoping identity computes. The paper's `g_ij` is defined from
the coalescent on forests (`coalescenceProb`), and `ADR11/Coalescent/Factorization.lean`
identifies the number of lineages of that chain with the death process; equation (2) itself is
`equation2` in `ADR11/Model.lean`. The formula is proved for every real `t`; the paper states it
for `t > 0`.
