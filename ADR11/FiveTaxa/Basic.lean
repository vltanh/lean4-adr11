module

public import ADR11.SmallTrees

/-!
# Linear invariants of 5-taxon unrooted gene tree distributions

* `linearInvariants H`: the homogeneous linear invariants of the unrooted gene tree distributions
  of the 5-taxon species trees with topology `H`: the vectors `c` (indexed by `Fin 15`, entry
  `i` for `T_{i+1}`) with `∑ cᵢ uᵢ = 0` for every choice of branch lengths.
* `ue i`: the coordinate vector of `u_i`, so that the invariant `u_i - u_j = 0` is
  `ue i - ue j`.
-/

@[expose] public section

namespace ADR11

open Finset

/-- The homogeneous linear invariants of the unrooted gene tree distributions of the 5-taxon
species trees with topology `H`. -/
def linearInvariants (H : Finset (Finset (Fin 5))) : Submodule ℝ (Fin 15 → ℝ) where
  carrier := {c | ∀ σ : SpeciesTree (Fin 5), σ.clusters = H → ∑ i, c i * uVec σ i = 0}
  add_mem' := by
    intro a b ha hb σ hσ
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha σ hσ, hb σ hσ, add_zero]
  zero_mem' := by
    intro σ _
    simp
  smul_mem' := by
    intro r c hc σ hσ
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hc σ hσ, mul_zero]

/-- The coordinate vector of `u_i` (`1 ≤ i ≤ 15`). -/
def ue (i : ℕ) : Fin 15 → ℝ := fun k => if k.val + 1 = i then 1 else 0

end ADR11
