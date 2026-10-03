module

public import ADR11.Nonbinary.Proposition11

/-!
# Proposition 3: four taxa

* `fourTaxa_recovery`: for any binary 4-taxon species tree, the most probable unrooted gene tree
  has the topology of the unrooted species tree, and the internal edge length of the unrooted
  species tree is `-log((3/2)(1 - ℙ(T)))`.
* `proposition3`: for `|X| = 4`, `σ⁻` is identifiable from `ℙ_σ`, but `σ⁺` is not.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Section 4.1: for any binary species tree on four taxa, with nontrivial split `A | Aᶜ` of its
unrooted topology, the unrooted gene tree `T` with that split is strictly the most probable, and
the internal edge length of `σ⁻` is `-log((3/2)(1 - ℙ(T)))`. -/
theorem fourTaxa_recovery (hX : Fintype.card X = 4) (σ : SpeciesTree X) (hσ : σ.IsBinary)
    (A : Finset X) (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    (∀ B : Finset X, #B = 2 → B ≠ A → B ≠ Aᶜ →
        σ.unrootedDist id (treeOfClusters {B}) < σ.unrootedDist id (treeOfClusters {A})) ∧
      σ.unrootedLength A = -log (3 / 2 * (1 - σ.unrootedDist id (treeOfClusters {A}))) := by
  sorry

/-- **Proposition 3.** For `|X| = 4` taxa, `σ⁻` is identifiable from `ℙ_{σ⁺}`, but `σ⁺` is not. -/
theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
        σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
        σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  refine ⟨fun σ σ' _ _ h => (proposition11_proposition3 hX).1 σ σ' h, ?_⟩
  obtain ⟨τ, τ', hb, hb', hd, hn⟩ := exists_sameUnrootedDist_not_sameRooted_four
  let e : Fin 4 ≃ X := (Fintype.equivFinOfCardEq hX).symm
  exact ⟨τ.relabel e, τ'.relabel e, (τ.isBinary_relabel_iff e).2 hb,
    (τ'.isBinary_relabel_iff e).2 hb', (SpeciesTree.unrootedDist_relabel_eq_iff τ τ' e).2 hd,
    fun hs => hn ((SpeciesTree.sameRootedMetricTree_relabel_iff τ τ' e).1 hs)⟩

end ADR11
