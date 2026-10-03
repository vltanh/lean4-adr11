module

public import ADR11.MSC.Basic

/-!
# Relabelling taxa

Everything in the model is natural with respect to bijections of the taxa: relabelling a species
tree relabels its gene tree distributions.

* `relabelFamily e F`: the image of a family of clusters under a bijection `e : X ≃ Y`.
* `SpeciesTree.relabel σ e`: the species tree `σ` with taxa relabelled by `e`.

## Main results

* `SpeciesTree.unrootedDist_relabel`, `SpeciesTree.rootedDist_relabel`: the gene tree
  distributions of the relabelled tree are the relabelled distributions.
* `SpeciesTree.sameRootedMetricTree_relabel_iff`, `SpeciesTree.sameUnrootedMetricTree_relabel_iff`:
  relabelling preserves and reflects equality of metric trees.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The image of a family of clusters under a bijection. -/
def relabelFamily (e : X ≃ Y) (F : Finset (Finset X)) : Finset (Finset Y) :=
  F.image fun A => A.map e.toEmbedding

theorem relabelFamily_injective (e : X ≃ Y) : Function.Injective (relabelFamily e) := by
  sorry

theorem relabelFamily_symm (e : X ≃ Y) (F : Finset (Finset X)) :
    relabelFamily e.symm (relabelFamily e F) = F := by
  sorry

theorem unroot_relabelFamily (e : X ≃ Y) (F : Finset (Finset X)) :
    unroot (relabelFamily e F) = relabelFamily e (unroot F) := by
  sorry

theorem SpeciesTree.relabel_univ_mem (σ : SpeciesTree X) (e : X ≃ Y) :
    (univ : Finset Y) ∈ relabelFamily e σ.clusters := by
  sorry

theorem SpeciesTree.relabel_singleton_mem (σ : SpeciesTree X) (e : X ≃ Y) (y : Y) :
    {y} ∈ relabelFamily e σ.clusters := by
  sorry

theorem SpeciesTree.relabel_nonempty_of_mem (σ : SpeciesTree X) (e : X ≃ Y) :
    ∀ B ∈ relabelFamily e σ.clusters, B.Nonempty := by
  sorry

theorem SpeciesTree.relabel_laminar (σ : SpeciesTree X) (e : X ≃ Y) :
    ∀ B ∈ relabelFamily e σ.clusters, ∀ C ∈ relabelFamily e σ.clusters,
      B ⊆ C ∨ C ⊆ B ∨ Disjoint B C := by
  sorry

theorem SpeciesTree.relabel_length_pos (σ : SpeciesTree X) (e : X ≃ Y) :
    ∀ B ∈ relabelFamily e σ.clusters, B ≠ univ → 0 < σ.length (B.map e.symm.toEmbedding) := by
  sorry

/-- The species tree `σ` with its taxa relabelled by `e`. -/
def SpeciesTree.relabel (σ : SpeciesTree X) (e : X ≃ Y) : SpeciesTree Y where
  clusters := relabelFamily e σ.clusters
  univ_mem := σ.relabel_univ_mem e
  singleton_mem := σ.relabel_singleton_mem e
  nonempty_of_mem := σ.relabel_nonempty_of_mem e
  laminar := σ.relabel_laminar e
  length B := σ.length (B.map e.symm.toEmbedding)
  length_pos := σ.relabel_length_pos e

theorem SpeciesTree.isBinary_relabel_iff (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).IsBinary ↔ σ.IsBinary := by
  sorry

theorem SpeciesTree.rootedDist_relabel (σ : SpeciesTree X) (e : X ≃ Y) (G : Finset (Finset X)) :
    (σ.relabel e).rootedDist id (relabelFamily e G) = σ.rootedDist id G := by
  sorry

theorem SpeciesTree.unrootedDist_relabel (σ : SpeciesTree X) (e : X ≃ Y)
    (T : Finset (Finset X)) :
    (σ.relabel e).unrootedDist id (relabelFamily e T) = σ.unrootedDist id T := by
  sorry

theorem SpeciesTree.unrootedDist_relabel_eq_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).unrootedDist id = (σ'.relabel e).unrootedDist id ↔
      σ.unrootedDist id = σ'.unrootedDist id := by
  sorry

theorem SpeciesTree.sameRootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameRootedMetricTree (σ'.relabel e) ↔ σ.SameRootedMetricTree σ' := by
  sorry

theorem SpeciesTree.sameUnrootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameUnrootedMetricTree (σ'.relabel e) ↔ σ.SameUnrootedMetricTree σ' := by
  sorry

end ADR11
