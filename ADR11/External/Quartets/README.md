# Unrooted trees are determined by their quartets

**Sources.**

- M. Steel, *The complexity of reconstructing trees from qualitative characters and subtrees*,
  J. Classification 9 (1992) 91–116: a binary unrooted tree is determined by its induced quartet
  trees, and (Proposition 6) every internal edge is distinguished by a quartet.
- H.-J. Bandelt, A. Dress, *Reconstructing the shape of a tree from observed dissimilarity data*,
  Adv. Appl. Math. 7 (1986) 309–343, and C. Semple, M. Steel, *Phylogenetics*, Oxford University
  Press, 2003, Theorem 6.3.5: the same for trees that need not be binary.

**Use in the paper.** Corollary 6 (`σ⁻` is determined by its quartet trees and their internal
edge lengths), the proof of Theorem 9 (Steel's Proposition 6) and, for nonbinary trees,
Appendix C (Proposition 11).

**In Lean.** `Steel.lean` states the results for the unrooted trees `σ⁻` of species trees, in the
representation of `ADR11.unroot` (an unrooted tree is the set of the sides of its splits), for
trees that need not be binary:

- `mem_unroot_iff_quartets`: `A | Aᶜ`, with both sides of size at least 2, is a split of `σ⁻` if
  and only if every quartet `aa'|bb'` with `a, a' ∈ A` and `b, b' ∉ A` is displayed by `σ⁻`;
- `exists_distinguishing_quartet`: every internal edge of `σ⁻` is the only edge separating some
  quartet;
- `SpeciesTree.sameUnrootedMetricTree_of_restrict`: two species trees whose induced unrooted
  metric trees agree on every set of four taxa have the same unrooted metric tree.

The paper uses these facts in exactly these forms; the last one combines the first two with the
lengths of the edges.
