module

public import ADR11.Introduction
public import ADR11.Identifiability.Lemma5
public import ADR11.Trees.Hierarchy
public import ADR11.MSC.Relabel

/-!
# Proposition 1 and Corollary 2: rooted triples

* `proposition1`: for a species tree with `n ≥ 3` taxa, the probabilities of rooted triple gene
  tree topologies determine the species tree topology and internal branch lengths.
* `corollary2`: so does the distribution of rooted gene trees.

By Lemma 5 (rooted version), the probability of the rooted triple `ab|c` is that of the rooted
gene tree `((A,B),C)` under the induced species tree on `{a, b, c}`; by equation (1) it exceeds `1/3`
exactly when the species tree has a cluster containing `a` and `b` but not `c`, and then determines
the length of the corresponding edge, `t = -log((3/2)(1 - p))`. Rooted triples determine the clusters
(`SpeciesTree.mem_clusters_of_triples`) and suitable triples isolate each internal edge.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]
/-- **Proposition 1.** For a species tree with `n ≥ 3` taxa, the probabilities of rooted triple
gene tree topologies determine the species tree topology and internal branch lengths. -/
theorem proposition1 (hX : 3 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary)
    (h : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c → σ.rootedTripleProb a b c = σ'.rootedTripleProb a b c) :
    σ.SameRootedMetricTree σ' := by
  sorry


/-- **Corollary 2.** For a species tree with `n ≥ 3` taxa, the distribution of rooted gene tree
topologies determines the species tree topology and internal branch lengths. -/
theorem corollary2 (hX : 3 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.rootedDist id = σ'.rootedDist id) :
    σ.SameRootedMetricTree σ' := by
  sorry

end ADR11
