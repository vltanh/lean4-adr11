module

public import ADR11.Identifiability.Lemma5

/-!
# Theorem 9: the main theorem

* `theorem9`: for `|X| ≥ 5` the unrooted gene tree distribution determines the metric species
  tree `σ⁺`.
* `theorem9_four`: for `|X| = 4` it determines exactly the unrooted metric species tree `σ⁻`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Theorem 9** (`|X| ≥ 5`). The unrooted topological gene tree distribution `ℙ_{σ⁺}` arising
from the multispecies coalescent model for samples of one lineage per taxon determines the metric
species tree `σ⁺` provided `|X| ≥ 5`. -/
theorem theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := by
  sorry

/-- **Theorem 9** (`|X| = 4`). If `|X| = 4`, `ℙ_{σ⁺}` determines only the unrooted metric species
tree `σ⁻`: two species trees have the same unrooted gene tree distribution exactly when they have
the same unrooted metric tree. -/
theorem theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  sorry

end ADR11
