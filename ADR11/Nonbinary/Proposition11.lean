module

public import ADR11.Basic

/-!
# Proposition 11: nonbinary species trees

Proposition 3, Corollary 6, Propositions 7 and 8, Theorem 9 and Corollary 10 remain valid if the
species tree `σ⁺` is nonbinary.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Proposition 11** (Proposition 3 for nonbinary species trees). For `|X| = 4`, `σ⁻` is
identifiable from `ℙ_{σ⁺}`, but `σ⁺` is not. -/
theorem proposition11_proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.unrootedDist id = σ'.unrootedDist id →
        σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.unrootedDist id = σ'.unrootedDist id ∧
        ¬ σ.SameRootedMetricTree σ' := by
  sorry

/-- **Proposition 11** (Corollary 6 for nonbinary species trees). For any `X`, `ℙ_{σ⁺}` determines
`σ⁻`. -/
theorem proposition11_corollary6 (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' := by
  sorry

/-- **Proposition 11** (Proposition 7 for nonbinary species trees). -/
theorem proposition11_proposition7 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.clusters = σ'.clusters := by
  sorry

/-- **Proposition 11** (Proposition 8 for nonbinary species trees). -/
theorem proposition11_proposition8 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  sorry

/-- **Proposition 11** (Theorem 9 for nonbinary species trees, `|X| ≥ 5`). -/
theorem proposition11_theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  sorry

/-- **Proposition 11** (Theorem 9 for nonbinary species trees, `|X| = 4`). -/
theorem proposition11_theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  sorry

/-- **Proposition 11** (Corollary 10 for nonbinary species trees). -/
theorem proposition11_corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := by
  sorry

end ADR11
