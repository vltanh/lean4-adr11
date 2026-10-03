module

public import ADR11.External.Tavare.Formula

/-!
# The population above the root: Kingman's coalescent run for an infinite time

As `t → ∞`, `g_kj(t) → 1` if `j = 1` and `→ 0` otherwise (for `k ≥ 1`), so `exp(tQ)(F, G)`
converges to the probability that the jump chain, run until one root is left, ends at `G`.

## Main results

* `tendsto_deathProb`: the limits of `g_kj(t)`.
* `tendsto_kingmanTransition`: the entries of `exp(tQ)` at a forest converge to those of
  `kingmanAbsorption`.
* `kingmanAbsorption_apply`: `kingmanAbsorption F G = J^{k-1}(F, G)` for complete `G`, `0`
  otherwise (and the identity on the empty forest).
* `kingmanTransition_mul_kingmanAbsorption`: running for a finite time and then for an infinite
  time is running for an infinite time.
-/

@[expose] public section

namespace ADR11

open Finset Real Filter Topology

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- From `k ≥ 1` lineages the pure death process never reaches `0`: the entries `(k, 0)` of the
powers of its generator vanish. -/
private theorem absorb_deathPow_zero (m k : ℕ) (hk : 1 ≤ k) : deathPow m k 0 = 0 := by
  induction m generalizing k with
  | zero => simp only [deathPow]; rw [ite_eq_right (by omega)]
  | succ m ih =>
    simp only [deathPow]
    rcases Nat.lt_or_ge k 2 with h | h
    · obtain rfl : k = 1 := by omega
      simp
    · rw [ih (k - 1) (by omega), ih k hk, sub_self, mul_zero]

private theorem absorb_deathProb_zero (k : ℕ) (hk : 1 ≤ k) (t : ℝ) : deathProb k 0 t = 0 := by
  simp [deathProb, absorb_deathPow_zero _ _ hk]

private theorem absorb_tavareCoeff_one (k : ℕ) (hk : 1 ≤ k) : tavareCoeff k 1 1 = 1 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  norm_num [tavareCoeff, div_self hk']

/-- `exp(-(m choose 2) t)` tends to `1` if `m = 1` and to `0` if `m ≥ 2`. -/
private theorem absorb_tendsto_exp (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun t : ℝ => exp (-(((m.choose 2 : ℕ) : ℝ) * t))) atTop
      (𝓝 (if m = 1 then 1 else 0)) := by
  split_ifs with h
  · subst h
    simp
  · have hpos : (0 : ℝ) < ((m.choose 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    exact tendsto_exp_comp_nhds_zero.mpr
      (tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hpos tendsto_id))

theorem tendsto_deathProb (k j : ℕ) (hk : 1 ≤ k) :
    Tendsto (deathProb k j) atTop (𝓝 (if j = 1 then 1 else 0)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h : deathProb k 0 = fun _ => 0 := funext fun t => absorb_deathProb_zero k hk t
    rw [h, ite_eq_right (by norm_num)]
    exact tendsto_const_nhds
  rcases lt_or_ge k j with hkj | hjk
  · have h : deathProb k j = fun _ => 0 := funext fun t => deathProb_eq_zero_of_lt hkj t
    rw [h, ite_eq_right (by omega)]
    exact tendsto_const_nhds
  have h := funext fun t => deathProb_eq_tavare k j hj hjk t
  rw [h]
  have hlim : (if j = 1 then (1 : ℝ) else 0) =
      ∑ m ∈ Icc j k, (if m = 1 then (1 : ℝ) else 0) * tavareCoeff k j m := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' (Icc j k) 1 (fun m => tavareCoeff k j m)]
    split_ifs with h1 h2 h2
    · subst h1; exact (absorb_tavareCoeff_one k hk).symm
    · exact absurd (Finset.mem_Icc.2 ⟨by omega, by omega⟩) h2
    · exact absurd (Finset.mem_Icc.1 h2).1 (by omega)
    · rfl
  rw [hlim]
  refine tendsto_finsetSum _ fun m hm => ?_
  exact (absorb_tendsto_exp m (by have := (Finset.mem_Icc.1 hm).1; omega)).mul_const _

/-- The limit of `exp(tQ)(F, G)`, computed from the factorization. -/
private theorem absorb_tendsto {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    Tendsto (fun t => kingmanTransition t F G) atTop
      (𝓝 (if #(roots F) = 0 then (if G = F then 1 else 0)
        else if #(roots G) = 1 then (jumpMatrix ^ (#(roots F) - 1)) F G else 0)) := by
  rcases Nat.eq_zero_or_pos (#(roots F)) with h0 | hpos
  · rw [ite_eq_left h0]
    have h : (fun t => kingmanTransition t F G) = fun _ => if G = F then 1 else 0 :=
      funext fun t => kingmanTransition_of_card_roots_le_one hF (by omega) t G
    rw [h]
    exact tendsto_const_nhds
  · rw [ite_eq_right (by omega)]
    have h : (fun t => kingmanTransition t F G) = fun t =>
        deathProb (#(roots F)) (#(roots G)) t * (jumpMatrix ^ (#(roots F) - #(roots G))) F G :=
      funext fun t => kingmanTransition_apply hF t G
    rw [h]
    have hl := (tendsto_deathProb (#(roots F)) (#(roots G)) hpos).mul_const
      ((jumpMatrix ^ (#(roots F) - #(roots G))) F G)
    split_ifs at hl ⊢ with hG
    · rw [hG] at hl ⊢
      simpa using hl
    · simpa using hl

theorem tendsto_kingmanTransition {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    Tendsto (fun t => kingmanTransition t F G) atTop (𝓝 (kingmanAbsorption F G)) := by
  have h := absorb_tendsto hF G
  have e : kingmanAbsorption F G = _ := h.limUnder_eq
  rw [e]
  exact h

theorem kingmanAbsorption_apply {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    kingmanAbsorption F G =
      if #(roots F) = 0 then (if G = F then 1 else 0)
      else if #(roots G) = 1 then (jumpMatrix ^ (#(roots F) - 1)) F G else 0 :=
  (absorb_tendsto hF G).limUnder_eq

theorem kingmanAbsorption_nonneg {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) : 0 ≤ kingmanAbsorption F G := by
  rw [kingmanAbsorption_apply hF]
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact jumpMatrix_pow_nonneg _ _ _
  · exact le_rfl

theorem kingmanAbsorption_sum {F : Finset (Finset L)} (hF : IsForest F) :
    ∑ G, kingmanAbsorption F G = 1 := by
  have h1 : Tendsto (fun t => ∑ G, kingmanTransition t F G) atTop
      (𝓝 (∑ G, kingmanAbsorption F G)) :=
    tendsto_finsetSum _ fun G _ => tendsto_kingmanTransition hF G
  have h2 : (fun t => ∑ G, kingmanTransition t F G) = fun _ => 1 :=
    funext fun t => kingmanTransition_sum hF t
  rw [h2] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

/-- First-step analysis in the population above the root. -/
theorem kingmanAbsorption_first_step {F : Finset (Finset L)} (hF : IsForest F)
    (hk : 2 ≤ #(roots F)) (G : Finset (Finset L)) :
    kingmanAbsorption F G =
      (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ * ∑ F' ∈ merges F, kingmanAbsorption F' G := by
  rw [kingmanAbsorption_apply hF, ite_eq_right (by omega)]
  have hm : ∀ F' ∈ merges F, kingmanAbsorption F' G =
      if #(roots G) = 1 then (jumpMatrix ^ (#(roots F) - 2)) F' G else 0 := by
    intro F' hF'
    obtain ⟨hF'f, hcard, -⟩ := hF.of_mem_merges hF'
    rw [kingmanAbsorption_apply hF'f, ite_eq_right (by omega),
      show #(roots F') - 1 = #(roots F) - 2 by omega]
  rw [Finset.sum_congr rfl hm]
  split_ifs with hG
  · rw [show #(roots F) - 1 = (#(roots F) - 2) + 1 by omega, jumpMatrix_pow_succ_apply hF hk]
  · simp

theorem kingmanTransition_mul_kingmanAbsorption {F : Finset (Finset L)} (hF : IsForest F)
    (t : ℝ) (G : Finset (Finset L)) :
    ∑ F', kingmanTransition t F F' * kingmanAbsorption F' G = kingmanAbsorption F G := by
  have hlim : Tendsto (fun s => kingmanTransition (t + s) F G) atTop
      (𝓝 (kingmanAbsorption F G)) :=
    (tendsto_kingmanTransition hF G).comp (tendsto_atTop_add_const_left atTop t tendsto_id)
  have heq : (fun s => kingmanTransition (t + s) F G) =
      fun s => ∑ F', kingmanTransition t F F' * kingmanTransition s F' G := by
    funext s
    rw [kingmanTransition_add, Matrix.mul_apply]
  rw [heq] at hlim
  have hlim2 : Tendsto (fun s => ∑ F', kingmanTransition t F F' * kingmanTransition s F' G)
      atTop (𝓝 (∑ F', kingmanTransition t F F' * kingmanAbsorption F' G)) := by
    refine tendsto_finsetSum _ fun F' _ => ?_
    by_cases h : kingmanTransition t F F' = 0
    · simp only [h, zero_mul]
      exact tendsto_const_nhds
    · have hF' : IsForest F' := by
        rw [kingmanTransition_apply hF] at h
        exact (jumpMatrix_pow_support hF (right_ne_zero_of_mul h)).1
      exact (tendsto_kingmanTransition hF' G).const_mul _
  exact tendsto_nhds_unique hlim2 hlim

end ADR11
