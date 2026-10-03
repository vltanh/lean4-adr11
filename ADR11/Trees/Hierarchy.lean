module

public import ADR11.MSC.Basic

/-!
# Combinatorics of rooted species trees (hierarchies)

## Main results

* `SpeciesTree.mem_clusters_of_triples`: a set `A` with at least two taxa is a cluster as soon as,
  for all `a, a' ∈ A` and `b ∉ A`, some cluster contains `a` and `a'` but not `b` (rooted
  triples determine a rooted tree).
* `SpeciesTree.restrict_isBinary`: the induced subtree of a binary species tree is binary.
* `SpeciesTree.sameRootedMetricTree_of_restrict`: on at least five taxa, two species trees whose
  induced subtrees on every set of five taxa agree as metric trees agree as metric trees. This is
  how Theorem 9 is assembled from Proposition 8.
* `SpeciesTree.sameUnrootedMetricTree_of_card_le_three`: on at most three taxa all unrooted metric
  species trees agree (there is no internal edge).
* `SpeciesTree.restrict_unroot`, `SpeciesTree.restrict_unrootedLength`: induced subtrees and
  unrooting commute, and the unrooted length of a split of `σ(S)` is the sum of the unrooted
  lengths of the splits of `σ` that induce it.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

namespace SpeciesTree

/-- Rooted triples determine the clusters: if for all `a, a' ∈ A` and `b ∉ A` some cluster of
`σ` contains `a` and `a'` but not `b`, then `A` is a cluster of `σ`. -/
theorem mem_clusters_of_triples (σ : SpeciesTree X) {A : Finset X} (hA : A.Nonempty)
    (h : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∉ A, ∃ C ∈ σ.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C) :
    A ∈ σ.clusters := by
  sorry

/-- The induced subtree of a binary species tree is binary. -/
theorem restrict_isBinary {σ : SpeciesTree X} (hσ : σ.IsBinary) (S : Finset X)
    (hS : S.Nonempty) : (σ.restrict S hS).IsBinary := by
  sorry

/-- Theorem 9's assembly: on at least five taxa, agreement of all induced 5-taxon metric trees
implies agreement of the metric trees. -/
theorem sameRootedMetricTree_of_restrict (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS)) :
    σ.SameRootedMetricTree σ' := by
  sorry

/-- On at most three taxa there is no internal edge in an unrooted tree. -/
theorem sameUnrootedMetricTree_of_card_le_three (hX : Fintype.card X ≤ 3)
    (σ σ' : SpeciesTree X) : σ.SameUnrootedMetricTree σ' := by
  sorry

/-- The unrooted topology of an induced subtree is the induced unrooted topology. -/
theorem restrict_unroot (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    unroot (σ.restrict S hS).clusters = restrictSplits S (unroot σ.clusters) := by
  sorry

/-- The length of an internal edge of the unrooted induced subtree `σ⁻(S)`: the sum of the
unrooted lengths of the splits of `σ⁻` that induce its split. -/
theorem restrict_unrootedLength (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty)
    (C : Finset S) (hC : C ∈ unroot (σ.restrict S hS).clusters) (hC₁ : 2 ≤ #C)
    (hC₂ : 2 ≤ #Cᶜ) :
    (σ.restrict S hS).unrootedLength C =
      (1 / 2 : ℝ) * ∑ A ∈ unroot σ.clusters with A.subtype (· ∈ S) = C ∨ A.subtype (· ∈ S) = Cᶜ,
        σ.unrootedLength A := by
  sorry

end SpeciesTree

end ADR11
