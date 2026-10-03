module

public import ADR11.MSC.Marginal

/-!
# Several lineages per taxon: the extended species tree (proof of Corollary 10)

When at most two lineages are sampled from each taxon, the multispecies coalescent with lineages
`L` sampled through a surjection `s : L → X` is the multispecies coalescent with one lineage per
leaf on the *extended species tree* `σ.extend s` on the taxon set `L`: its clusters are the
preimages `s⁻¹(A)` of the clusters of `σ` and the singletons of `L`; the edge above `s⁻¹(A)` keeps
the length of the edge above `A` (so the pendant edge of a taxon sampled twice becomes an internal
edge), and the new pendant edges get length `1`.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

/-- The clusters of the extended species tree. -/
def extendClusters (H : Finset (Finset X)) (s : L → X) : Finset (Finset L) :=
  H.image (fun A => univ.filter fun l => s l ∈ A) ∪ univ.image fun l => {l}

theorem SpeciesTree.extend_univ_mem (σ : SpeciesTree X) (s : L → X) :
    (univ : Finset L) ∈ extendClusters σ.clusters s := by
  sorry

theorem SpeciesTree.extend_singleton_mem (σ : SpeciesTree X) (s : L → X) (l : L) :
    {l} ∈ extendClusters σ.clusters s := by
  sorry

theorem SpeciesTree.extend_nonempty_of_mem (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) : ∀ B ∈ extendClusters σ.clusters s, B.Nonempty := by
  sorry

theorem SpeciesTree.extend_laminar (σ : SpeciesTree X) (s : L → X) :
    ∀ B ∈ extendClusters σ.clusters s, ∀ C ∈ extendClusters σ.clusters s,
      B ⊆ C ∨ C ⊆ B ∨ Disjoint B C := by
  sorry

/-- The lengths of the extended species tree: a cluster `s⁻¹(A)` keeps the length of `A`; a new
singleton cluster gets length `1`. -/
noncomputable def SpeciesTree.extendLength (σ : SpeciesTree X) (s : L → X) (B : Finset L) : ℝ :=
  if h : ∃ A ∈ σ.clusters, (univ.filter fun l => s l ∈ A) = B ∧ 2 ≤ #B then
    σ.length h.choose else 1

theorem SpeciesTree.extendLength_pos (σ : SpeciesTree X) (s : L → X) :
    ∀ B ∈ extendClusters σ.clusters s, B ≠ univ → 0 < σ.extendLength s B := by
  sorry

/-- The extended species tree on the lineages `L`. -/
noncomputable def SpeciesTree.extend (σ : SpeciesTree X) (s : L → X)
    (hs : Function.Surjective s) : SpeciesTree L where
  clusters := extendClusters σ.clusters s
  univ_mem := σ.extend_univ_mem s
  singleton_mem := σ.extend_singleton_mem s
  nonempty_of_mem := σ.extend_nonempty_of_mem hs
  laminar := σ.extend_laminar s
  length := σ.extendLength s
  length_pos := σ.extendLength_pos s

/-- With at most two lineages per taxon, sampling through `s` is sampling one lineage per leaf of
the extended species tree. -/
theorem SpeciesTree.rootedDist_extend (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) (h2 : ∀ x, #(univ.filter fun l => s l = x) ≤ 2)
    (G : Finset (Finset L)) :
    σ.rootedDist s G = (σ.extend s hs).rootedDist id G := by
  sorry

theorem SpeciesTree.extend_isBinary {σ : SpeciesTree X} (hσ : σ.IsBinary) {s : L → X}
    (hs : Function.Surjective s) (h2 : ∀ x, #(univ.filter fun l => s l = x) ≤ 2) :
    (σ.extend s hs).IsBinary := by
  sorry

/-- The extended tree determines the species tree, its internal edge lengths, and the pendant
edge lengths of the taxa sampled twice. -/
theorem SpeciesTree.sameRootedMetricTree_of_extend (hX : 2 ≤ Fintype.card X)
    (σ σ' : SpeciesTree X) {s : L → X} (hs : Function.Surjective s)
    (h : (σ.extend s hs).SameRootedMetricTree (σ'.extend s hs)) :
    σ.SameRootedMetricTree σ' ∧
      ∀ x, 2 ≤ #(univ.filter fun l => s l = x) → σ.length {x} = σ'.length {x} := by
  sorry

end ADR11
