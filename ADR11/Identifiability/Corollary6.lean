module

public import ADR11.Identifiability.Lemma5

/-!
# Corollary 6: the unrooted metric species tree is identifiable

For any taxon set `X`, the unrooted gene tree distribution `ℙ_{σ⁺}` determines `σ⁻`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Corollary 6.** For any `X`, `ℙ_{σ⁺}` determines `σ⁻`. -/
theorem corollary6 (σ σ' : SpeciesTree X) (hσ : σ.IsBinary) (hσ' : σ'.IsBinary)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' := by
  sorry

end ADR11
