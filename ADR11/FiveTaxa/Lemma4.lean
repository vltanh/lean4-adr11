module

public import ADR11.SmallTrees

/-!
# Lemma 4: all coalescences above the root

If the five lineages of a 5-taxon species tree all enter the population above the root without
having coalesced, then the unrooted gene tree is uniformly distributed on the 15 unrooted gene
trees. The paper remarks that this is special to five taxa; `lemma4_six` shows that it fails for
six lineages.
-/

@[expose] public section

namespace ADR11

open Finset

/-- **Lemma 4.** If all coalescent events occur above the root of a 5-taxon species tree, all 15
unrooted topological gene trees are equally likely: starting from five uncoalesced lineages, the
population above the root produces each `T_i` with probability `1/15`. -/
theorem lemma4 (i : ℕ) (hi : i ∈ Icc 1 15) :
    ∑ G, (if unroot G = T5 i then kingmanAbsorption (singletonForest 5) G else 0) = 1 / 15 := by
  sorry

/-- The remark after Lemma 4: for six taxa the analogous statement is false. Starting from six
uncoalesced lineages, the unrooted gene tree with the three cherries `AB`, `CD`, `EF` and the
unrooted caterpillar `((A,B),C,D,(E,F))` (splits `AB|CDEF`, `ABC|DEF`, `ABCD|EF`) have different
probabilities. -/
theorem lemma4_six :
    ∑ G, (if unroot G = treeOfClusters {{0, 1}, {2, 3}, {4, 5}}
        then kingmanAbsorption (singletonForest 6) G else 0) ≠
      ∑ G, (if unroot G = treeOfClusters {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}
        then kingmanAbsorption (singletonForest 6) G else 0) := by
  sorry

end ADR11
