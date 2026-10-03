module

public import ADR11.Basic
public import ADR11.Coalescent.Forest

/-!
# The jump chain, the number of lineages, and the factorization of Kingman's coalescent

Kingman's coalescent on forests splits into two independent parts: the number of roots, a pure
death process with rate `k.choose 2` from `k` roots, and the sequence of merges, its jump chain,
which merges a uniformly chosen pair of roots at each step.

* `jumpMatrix`: the jump chain on forests (it stays put at forests with at most one root).
* `deathPow m k j`: the entry `(k, j)` of the `m`-th power of the generator of the pure death
  process, defined by the recursion `D^{m+1} = D · D^m`.
* `deathProb k j t`: the transition probability `exp(t D)(k, j)` of the pure death process, the
  paper's `g_kj(t)`.

## Main results

* `kingmanGenerator_pow_apply`, `kingmanTransition_apply`: for a forest `F` with `k` roots and any
  `G` with `j` roots, `exp(tQ)(F, G) = g_kj(t) · J^{k-j}(F, G)`.
* `coalescenceProb_eq_deathProb`: the paper's `g_ij`, defined from the coalescent on singletons,
  is `deathProb i j`.
* `jumpMatrix_pow_succ_apply`: first-step analysis of the jump chain.
* `deathProb_small`: the closed forms of `g_kj(t)` for `k ≤ 4`.
* `kingmanTransition_nonneg`, `kingmanTransition_sum`, `kingmanTransition_support`: the rows of
  `exp(tQ)` at forests are probability distributions on forests reachable by merges
  (nonnegativity holds at every `F`, by uniformization).
* `hasSum_deathProb`, `deathProb_sum_range`, `deathProb_sum_Icc`, `deathProb_le_one`: the series
  defining `g_kj(t)` converges, and the `g_kj(t)` form a probability distribution in `j`.
* `isForest_singletonForest`, `card_roots_singletonForest`: the starting point of `g_ij`.

## Implementation notes

Matrices carry no canonical norm, so the entries of `exp(tQ)` are computed from the exponential
series with the `L∞` operator norm (`Matrix.Norms.Operator`) opened locally, as in
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`. Nonnegativity of `exp(tQ)` for `t ≥ 0`
uses uniformization: `tQ = tP - tc · 1` with `P = Q + c · 1` entrywise nonnegative.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The jump chain of Kingman's coalescent on forests: from a forest with `k ≥ 2` roots, each of
its `k.choose 2` merges has probability `1 / (k choose 2)`; a forest with at most one root stays
put. -/
noncomputable def jumpMatrix : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G =>
    if #(roots F) ≤ 1 then (if G = F then 1 else 0)
    else if G ∈ merges F then (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ else 0

/-- `deathPow m k j` is the entry `(k, j)` of `D^m`, where `D` is the generator of the pure death
process on `ℕ` with rate `k.choose 2` from `k` to `k - 1`. -/
def deathPow : ℕ → ℕ → ℕ → ℝ
  | 0, k, j => if k = j then 1 else 0
  | m + 1, k, j => ((k.choose 2 : ℕ) : ℝ) * (deathPow m (k - 1) j - deathPow m k j)

/-- The transition probabilities `exp(tD)(k, j)` of the pure death process: the probability that
`k` lineages coalesce into `j` lineages within time `t`. -/
noncomputable def deathProb (k j : ℕ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, t ^ m / (m.factorial : ℝ) * deathPow m k j

set_option linter.unusedVariables false in
theorem jumpMatrix_apply_of_isForest {F : Finset (Finset L)} (hF : IsForest F)
    (hk : 2 ≤ #(roots F)) (G : Finset (Finset L)) :
    jumpMatrix F G = if G ∈ merges F then (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ else 0 := by
  have hk' : ¬ #(roots F) ≤ 1 := by omega
  simp only [jumpMatrix, ite_eq_right hk']

/-! ### The jump chain -/

private theorem fact_jumpMatrix_apply_of_le_one {F : Finset (Finset L)} (hk : #(roots F) ≤ 1)
    (G : Finset (Finset L)) : jumpMatrix F G = if G = F then 1 else 0 := by
  simp only [jumpMatrix, ite_eq_left hk]

private theorem fact_jumpMatrix_nonneg (F G : Finset (Finset L)) : 0 ≤ jumpMatrix F G := by
  simp only [jumpMatrix]
  split_ifs <;> positivity

omit [Fintype L] in
private theorem fact_one_apply (F G : Finset (Finset L)) :
    (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) F G = if G = F then 1 else 0 := by
  by_cases h : G = F
  · subst h; simp
  · rw [Matrix.one_apply_ne (Ne.symm h), ite_eq_right h]

/-- First-step analysis of the jump chain. -/
theorem jumpMatrix_pow_succ_apply {F : Finset (Finset L)} (hF : IsForest F) (hk : 2 ≤ #(roots F))
    (n : ℕ) (G : Finset (Finset L)) :
    (jumpMatrix ^ (n + 1)) F G =
      (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ * ∑ F' ∈ merges F, (jumpMatrix ^ n) F' G := by
  rw [pow_succ', Matrix.mul_apply]
  simp_rw [jumpMatrix_apply_of_isForest hF hk, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

theorem jumpMatrix_pow_of_card_roots_le_one {F : Finset (Finset L)} (hk : #(roots F) ≤ 1)
    (n : ℕ) (G : Finset (Finset L)) :
    (jumpMatrix ^ n) F G = if G = F then 1 else 0 := by
  induction n with
  | zero => rw [pow_zero, fact_one_apply]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [fact_jumpMatrix_apply_of_le_one hk, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ F), ih]

theorem jumpMatrix_pow_nonneg (n : ℕ) (F G : Finset (Finset L)) : 0 ≤ (jumpMatrix ^ n) F G := by
  induction n generalizing F with
  | zero => rw [pow_zero, fact_one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun F' _ => mul_nonneg (fact_jumpMatrix_nonneg F F') (ih F')

theorem jumpMatrix_pow_sum {F : Finset (Finset L)} (hF : IsForest F) (n : ℕ) :
    ∑ G, (jumpMatrix ^ n) F G = 1 := by
  induction n generalizing F with
  | zero => simp [fact_one_apply]
  | succ n ih =>
    simp_rw [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    by_cases hk : #(roots F) ≤ 1
    · simp_rw [fact_jumpMatrix_apply_of_le_one hk, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ F), ih hF]
    · replace hk : 2 ≤ #(roots F) := by omega
      simp_rw [jumpMatrix_apply_of_isForest hF hk, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_congr rfl (fun F' hF' => by rw [ih (hF.of_mem_merges hF').1, mul_one]),
        Finset.sum_const, hF.card_merges, nsmul_eq_mul]
      have hC : (((#(roots F)).choose 2 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos hk).ne'
      field_simp

/-- The jump chain only adds clusters, keeps the lineages, and removes one root per step until
one root is left. -/
theorem jumpMatrix_pow_support {F G : Finset (Finset L)} (hF : IsForest F) {n : ℕ}
    (h : (jumpMatrix ^ n) F G ≠ 0) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F ∧
      #(roots G) = if n < #(roots F) then #(roots F) - n else min (#(roots F)) 1 := by
  induction n generalizing F with
  | zero =>
    rw [pow_zero, fact_one_apply] at h
    split_ifs at h with hGF
    · subst hGF
      refine ⟨hF, subset_rfl, rfl, ?_⟩
      split_ifs <;> omega
    · exact absurd rfl h
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨F', -, hF'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hJ : jumpMatrix F F' ≠ 0 := left_ne_zero_of_mul hF'
    have hJn : (jumpMatrix ^ n) F' G ≠ 0 := right_ne_zero_of_mul hF'
    by_cases hk : #(roots F) ≤ 1
    · have hF'F : F' = F := by
        by_contra hne
        exact hJ (by rw [fact_jumpMatrix_apply_of_le_one hk, ite_eq_right hne])
      subst hF'F
      obtain ⟨h1, h2, h3, h4⟩ := ih hF hJn
      refine ⟨h1, h2, h3, ?_⟩
      rw [h4]
      split_ifs <;> omega
    · replace hk : 2 ≤ #(roots F) := by omega
      have hmem : F' ∈ merges F := by
        by_contra hne
        exact hJ (by rw [jumpMatrix_apply_of_isForest hF hk, ite_eq_right hne])
      obtain ⟨hF'f, hcard, hsub, -, hlin⟩ := hF.of_mem_merges hmem
      obtain ⟨h1, h2, h3, h4⟩ := ih hF'f hJn
      refine ⟨h1, hsub.trans h2, h3.trans hlin, ?_⟩
      rw [h4]
      split_ifs <;> omega

/-! ### The pure death process -/

theorem deathPow_succ (m k j : ℕ) :
    deathPow (m + 1) k j = ((k.choose 2 : ℕ) : ℝ) * (deathPow m (k - 1) j - deathPow m k j) :=
  rfl

/-- The pure death process never increases. -/
theorem deathPow_eq_zero_of_lt {k j : ℕ} (h : k < j) (m : ℕ) : deathPow m k j = 0 := by
  induction m generalizing k with
  | zero => simp [deathPow, h.ne]
  | succ m ih =>
    rw [deathPow_succ, ih (lt_of_le_of_lt (Nat.sub_le k 1) h), ih h]
    ring

theorem deathPow_self (m k : ℕ) : deathPow m k k = (-((k.choose 2 : ℕ) : ℝ)) ^ m := by
  induction m with
  | zero => simp [deathPow]
  | succ m ih =>
    rw [deathPow_succ, ih]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [deathPow_eq_zero_of_lt (Nat.sub_lt hk one_pos)]
      ring

/-- From `k ≥ 1` lineages, the pure death process never reaches `0`. -/
theorem deathPow_zero_right {k : ℕ} (hk : 1 ≤ k) (m : ℕ) : deathPow m k 0 = 0 := by
  induction m generalizing k with
  | zero => simp [deathPow]; omega
  | succ m ih =>
    rw [deathPow_succ]
    rcases Nat.lt_or_ge k 2 with h | h
    · obtain rfl : k = 1 := by omega
      simp
    · rw [ih (by omega), ih hk]
      ring

private theorem fact_abs_deathPow_le (m k j : ℕ) :
    |deathPow m k j| ≤ (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m := by
  induction m generalizing k with
  | zero => simp only [deathPow, pow_zero]; split_ifs <;> simp
  | succ m ih =>
    rw [deathPow_succ, abs_mul, pow_succ, abs_of_nonneg (by positivity)]
    have hc : (((k - 1).choose 2 : ℕ) : ℝ) ≤ ((k.choose 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose 2 (Nat.sub_le k 1)
    have h1 : |deathPow m (k - 1) j| ≤ (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m :=
      (ih (k - 1)).trans (pow_le_pow_left₀ (by positivity) (by linarith) m)
    have h2 := ih k
    calc ((k.choose 2 : ℕ) : ℝ) * |deathPow m (k - 1) j - deathPow m k j|
        ≤ ((k.choose 2 : ℕ) : ℝ) * (|deathPow m (k - 1) j| + |deathPow m k j|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
      _ ≤ ((k.choose 2 : ℕ) : ℝ) *
            ((2 * ((k.choose 2 : ℕ) : ℝ)) ^ m + (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m) := by
          gcongr
      _ = (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m * (2 * ((k.choose 2 : ℕ) : ℝ)) := by ring

/-- The series defining `deathProb k j t` converges (absolutely). -/
theorem summable_deathProb (k j : ℕ) (t : ℝ) :
    Summable fun m : ℕ => t ^ m / (m.factorial : ℝ) * deathPow m k j := by
  refine Summable.of_norm_bounded
    (Real.summable_pow_div_factorial (|t| * (2 * ((k.choose 2 : ℕ) : ℝ)))) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
  calc |t| ^ m / (m.factorial : ℝ) * |deathPow m k j|
      ≤ |t| ^ m / (m.factorial : ℝ) * (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m := by
        gcongr
        exact fact_abs_deathPow_le m k j
    _ = (|t| * (2 * ((k.choose 2 : ℕ) : ℝ))) ^ m / (m.factorial : ℝ) := by ring

theorem hasSum_deathProb (k j : ℕ) (t : ℝ) :
    HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ) * deathPow m k j) (deathProb k j t) :=
  (summable_deathProb k j t).hasSum

private theorem fact_hasSum_exp_mul (x t : ℝ) :
    HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ) * x ^ m) (Real.exp (x * t)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (x * t)
  rw [← Real.exp_eq_exp_ℝ] at h
  convert h using 1
  funext m
  rw [mul_pow]
  ring

theorem deathProb_self (k : ℕ) (t : ℝ) :
    deathProb k k t = exp (-(((k.choose 2 : ℕ) : ℝ) * t)) := by
  rw [← neg_mul]
  refine HasSum.tsum_eq ?_
  simp_rw [deathPow_self]
  exact fact_hasSum_exp_mul _ t

/-! ### The matrix exponential, entrywise -/

set_option backward.isDefEq.respectTransparency false in
/-- The entries of the exponential of a real matrix are given by the exponential series. -/
private theorem fact_hasSum_exp_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ * (A ^ n) i j) (NormedSpace.exp A i j) := by
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have h2 := Pi.hasSum.mp (Pi.hasSum.mp h i) j
  simpa using h2

/-- The powers of the generator at a forest factor through the number of roots and the jump
chain. -/
theorem kingmanGenerator_pow_apply {F : Finset (Finset L)} (hF : IsForest F) (m : ℕ)
    (G : Finset (Finset L)) :
    (kingmanGenerator ^ m) F G =
      deathPow m (#(roots F)) (#(roots G)) * (jumpMatrix ^ (#(roots F) - #(roots G))) F G := by
  induction m generalizing F with
  | zero =>
    rw [pow_zero, fact_one_apply]
    simp only [deathPow]
    by_cases h : G = F
    · subst h
      simp
    · rw [ite_eq_right h]
      split_ifs with hk
      · rw [hk, Nat.sub_self, pow_zero, fact_one_apply, ite_eq_right h, mul_zero]
      · rw [zero_mul]
  | succ m ih =>
    rw [pow_succ', hF.kingmanGenerator_mul_apply, ih hF]
    have hmerge : ∀ F' ∈ merges F, (kingmanGenerator ^ m) F' G =
        deathPow m (#(roots F) - 1) (#(roots G)) *
          (jumpMatrix ^ (#(roots F) - 1 - #(roots G))) F' G := by
      intro F' hF'
      obtain ⟨hF'f, hcard, -⟩ := hF.of_mem_merges hF'
      rw [ih hF'f, show #(roots F') = #(roots F) - 1 by omega]
    rw [Finset.sum_congr rfl hmerge, ← Finset.mul_sum, deathPow_succ]
    by_cases hk : #(roots F) ≤ 1
    · have hC : (((#(roots F)).choose 2 : ℕ) : ℝ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [hC, merges_eq_empty_of_card_roots_le_one hk]
      simp
    · replace hk : 2 ≤ #(roots F) := by omega
      by_cases hjk : #(roots G) < #(roots F)
      · have hstep := jumpMatrix_pow_succ_apply hF hk (#(roots F) - 1 - #(roots G)) G
        rw [show #(roots F) - 1 - #(roots G) + 1 = #(roots F) - #(roots G) by omega] at hstep
        have hC : (((#(roots F)).choose 2 : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos hk).ne'
        rw [hstep]
        field_simp
        ring
      · rw [deathPow_eq_zero_of_lt (show #(roots F) - 1 < #(roots G) by omega)]
        ring

/-- **Factorization.** For a forest `F` with `k` roots and `G` with `j` roots,
`exp(tQ)(F, G) = g_kj(t) · J^{k-j}(F, G)`. -/
theorem kingmanTransition_apply {F : Finset (Finset L)} (hF : IsForest F) (t : ℝ)
    (G : Finset (Finset L)) :
    kingmanTransition t F G =
      deathProb (#(roots F)) (#(roots G)) t * (jumpMatrix ^ (#(roots F) - #(roots G))) F G := by
  have h1 := fact_hasSum_exp_apply (t • kingmanGenerator (L := L)) F G
  have h2 := (hasSum_deathProb (#(roots F)) (#(roots G)) t).mul_right
    ((jumpMatrix ^ (#(roots F) - #(roots G))) F G)
  refine h1.unique ?_
  convert h2 using 1
  funext n
  rw [smul_pow, Matrix.smul_apply, kingmanGenerator_pow_apply hF, smul_eq_mul]
  ring

theorem kingmanTransition_zero :
    kingmanTransition (L := L) 0 = 1 := by
  simp [kingmanTransition]

theorem kingmanTransition_add (s t : ℝ) :
    kingmanTransition (L := L) (s + t) = kingmanTransition s * kingmanTransition t := by
  unfold kingmanTransition
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right t)

/-- A forest with at most one root does not change. -/
theorem kingmanTransition_of_card_roots_le_one {F : Finset (Finset L)} (hF : IsForest F)
    (hk : #(roots F) ≤ 1) (t : ℝ) (G : Finset (Finset L)) :
    kingmanTransition t F G = if G = F then 1 else 0 := by
  rw [kingmanTransition_apply hF]
  by_cases hG : G = F
  · subst hG
    rw [Nat.sub_self, pow_zero, Matrix.one_apply_eq, mul_one, ite_eq_left rfl, deathProb_self,
      Nat.choose_eq_zero_of_lt (by omega : #(roots G) < 2)]
    simp
  · rw [jumpMatrix_pow_of_card_roots_le_one hk, ite_eq_right hG, mul_zero]

/-- A forest with `k` roots is unchanged after time `t` with probability `exp(-(k choose 2) t)`. -/
theorem kingmanTransition_apply_self {F : Finset (Finset L)} (hF : IsForest F) (t : ℝ) :
    kingmanTransition t F F = exp (-((((#(roots F)).choose 2 : ℕ) : ℝ) * t)) := by
  rw [kingmanTransition_apply hF, Nat.sub_self, pow_zero, Matrix.one_apply_eq, mul_one,
    deathProb_self]

theorem kingmanTransition_nonneg {t : ℝ} (ht : 0 ≤ t) (F G : Finset (Finset L)) :
    0 ≤ kingmanTransition t F G := by
  -- uniformization: `tQ = tP - tc · 1` with `P = Q + c · 1` entrywise nonnegative
  set Q := kingmanGenerator (L := L) with hQ
  set c : ℝ := ∑ F : Finset (Finset L), (((#(roots F)).choose 2 : ℕ) : ℝ)
  set P : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ := Q + c • 1 with hPdef
  have hP : ∀ F G, 0 ≤ P F G := by
    intro F G
    rw [hPdef, Matrix.add_apply, Matrix.smul_apply, fact_one_apply, smul_eq_mul, hQ]
    unfold kingmanGenerator
    by_cases h : G = F
    · subst h
      simp only [ite_true, mul_one]
      have : (((#(roots G)).choose 2 : ℕ) : ℝ) ≤ c :=
        Finset.single_le_sum
          (f := fun F : Finset (Finset L) => (((#(roots F)).choose 2 : ℕ) : ℝ))
          (fun F _ => by positivity) (Finset.mem_univ G)
      linarith
    · simp only [ite_eq_right h, mul_zero, add_zero]
      split_ifs <;> norm_num
  have hPn : ∀ n F G, 0 ≤ (P ^ n) F G := by
    intro n
    induction n with
    | zero => intro F G; rw [pow_zero, fact_one_apply]; split_ifs <;> norm_num
    | succ n ih =>
      intro F G
      rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_nonneg fun F' _ => mul_nonneg (hP F F') (ih F' G)
  have hexpP : ∀ F G, 0 ≤ NormedSpace.exp (t • P) F G := by
    intro F G
    refine (fact_hasSum_exp_apply (t • P) F G).nonneg fun n => ?_
    rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg ht n) (hPn n F G))
  have hscal : ∀ (r : ℝ) (F G : Finset (Finset L)), 0 ≤
      NormedSpace.exp (r • (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ)) F G := by
    intro r F G
    have h := fact_hasSum_exp_apply
      (r • (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ)) F G
    simp_rw [smul_pow, one_pow, Matrix.smul_apply, fact_one_apply, smul_eq_mul] at h
    by_cases hGF : G = F
    · simp only [ite_eq_left hGF, mul_one] at h
      have h' : HasSum (fun n : ℕ => r ^ n / (n.factorial : ℝ)) (Real.exp r) := by
        rw [Real.exp_eq_exp_ℝ]
        exact NormedSpace.expSeries_div_hasSum_exp r
      rw [h.unique (by convert h' using 1; funext n; ring)]
      exact (Real.exp_pos r).le
    · simp only [ite_eq_right hGF, mul_zero] at h
      rw [h.unique hasSum_zero]
  have hsplit : t • Q =
      t • P + (-(t * c)) • (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) := by
    rw [hPdef, smul_add, smul_smul, add_assoc, ← add_smul]
    simp
  show 0 ≤ NormedSpace.exp (t • Q) F G
  rw [hsplit, Matrix.exp_add_of_commute _ _ ((Commute.one_right _).smul_right _), Matrix.mul_apply]
  exact Finset.sum_nonneg fun F' _ => mul_nonneg (hexpP F F') (hscal _ F' G)

/-- The rows of the powers of the generator at a forest sum to `0` (except for the identity). -/
private theorem fact_sum_kingmanGenerator_pow {F : Finset (Finset L)} (hF : IsForest F) (n : ℕ) :
    ∑ G, (kingmanGenerator ^ n) F G = if n = 0 then 1 else 0 := by
  induction n generalizing F with
  | zero => simp [fact_one_apply]
  | succ n ih =>
    simp_rw [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [hF.sum_kingmanGenerator_mul, ih hF,
      Finset.sum_congr rfl (fun F' hF' => ih (hF.of_mem_merges hF').1),
      Finset.sum_const, hF.card_merges, nsmul_eq_mul, ite_eq_right (Nat.succ_ne_zero n)]
    ring

theorem kingmanTransition_sum {F : Finset (Finset L)} (hF : IsForest F) (t : ℝ) :
    ∑ G, kingmanTransition t F G = 1 := by
  have h := hasSum_sum (s := univ) fun G _ =>
    fact_hasSum_exp_apply (t • kingmanGenerator (L := L)) F G
  refine h.unique ?_
  convert hasSum_ite_eq 0 (1 : ℝ) using 1
  funext n
  simp_rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, ← Finset.mul_sum]
  rw [fact_sum_kingmanGenerator_pow hF]
  split_ifs with hn
  · subst hn; simp
  · simp

/-- The coalescent started at a forest only reaches forests obtained by merging roots: they have
the same lineages, contain the starting forest, and have at most as many roots. -/
theorem kingmanTransition_support {F G : Finset (Finset L)} (hF : IsForest F) {t : ℝ}
    (h : kingmanTransition t F G ≠ 0) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F ∧ #(roots G) ≤ #(roots F) := by
  rw [kingmanTransition_apply hF] at h
  obtain ⟨h1, h2, h3, h4⟩ := jumpMatrix_pow_support hF (right_ne_zero_of_mul h)
  refine ⟨h1, h2, h3, ?_⟩
  rw [h4]
  split_ifs <;> omega

/-! ### Forests of singletons -/

omit [Fintype L] in
private theorem fact_isForest_image_singleton (S : Finset L) :
    IsForest (S.image fun l => ({l} : Finset L)) := by
  constructor
  · intro A hA
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hA
    exact Finset.singleton_nonempty l
  · intro A hA B hB
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hB
    by_cases hab : a = b
    · subst hab
      exact Or.inl subset_rfl
    · exact Or.inr (Or.inr (Finset.disjoint_singleton.mpr hab))

private theorem fact_roots_image_singleton (S : Finset L) :
    roots (S.image fun l => ({l} : Finset L)) = S.image fun l => ({l} : Finset L) := by
  unfold roots
  apply Finset.filter_true_of_mem
  intro A hA B hB hAB
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hB
  rw [Finset.singleton_subset_singleton] at hAB
  rw [hAB]

private theorem fact_card_roots_image_singleton (S : Finset L) :
    #(roots (S.image fun l => ({l} : Finset L))) = #S := by
  rw [fact_roots_image_singleton, Finset.card_image_of_injective _ Finset.singleton_injective]

theorem isForest_singletonForest (n : ℕ) : IsForest (singletonForest n) :=
  fact_isForest_image_singleton _

theorem roots_singletonForest (n : ℕ) : roots (singletonForest n) = singletonForest n :=
  fact_roots_image_singleton _

theorem card_roots_singletonForest (n : ℕ) : #(roots (singletonForest n)) = n := by
  rw [singletonForest, fact_card_roots_image_singleton, Finset.card_univ, Fintype.card_fin]

/-! ### The pure death process: transition probabilities -/

theorem deathProb_eq_zero_of_lt {k j : ℕ} (h : k < j) (t : ℝ) : deathProb k j t = 0 := by
  simp [deathProb, deathPow_eq_zero_of_lt h]

/-- From `k ≥ 1` lineages, `0` lineages are never reached. -/
theorem deathProb_zero_right {k : ℕ} (hk : 1 ≤ k) (t : ℝ) : deathProb k 0 t = 0 := by
  simp [deathProb, deathPow_zero_right hk]

/-- The paper's `g_ij(t)` is the transition probability of the pure death process. -/
theorem coalescenceProb_eq_deathProb (i j : ℕ) (t : ℝ) : coalescenceProb i j t = deathProb i j t := by
  have hS := isForest_singletonForest i
  have hk := card_roots_singletonForest i
  unfold coalescenceProb
  have key : ∀ G : Finset (Finset (Fin i)),
      (if #(roots G) = j then kingmanTransition t (singletonForest i) G else 0) =
        deathProb i j t *
          (if #(roots G) = j then (jumpMatrix ^ (i - j)) (singletonForest i) G else 0) := by
    intro G
    split_ifs with hG
    · rw [kingmanTransition_apply hS, hk, hG]
    · rw [mul_zero]
  rw [Finset.sum_congr rfl (fun G _ => key G), ← Finset.mul_sum]
  by_cases hji : i < j
  · rw [deathProb_eq_zero_of_lt hji, zero_mul]
  by_cases hj0 : j = 0 ∧ 1 ≤ i
  · rw [hj0.1, deathProb_zero_right hj0.2, zero_mul]
  have hsum : ∑ G : Finset (Finset (Fin i)),
      (if #(roots G) = j then (jumpMatrix ^ (i - j)) (singletonForest i) G else 0) = 1 := by
    rw [← jumpMatrix_pow_sum hS (i - j)]
    refine Finset.sum_congr rfl fun G _ => ?_
    split_ifs with hG
    · rfl
    · by_contra hne
      have h4 := (jumpMatrix_pow_support hS (fun h0 => hne h0.symm)).2.2.2
      rw [hk] at h4
      apply hG
      rw [h4]
      split_ifs <;> omega
  rw [hsum, mul_one]

theorem deathProb_nonneg (k j : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ deathProb k j t := by
  rw [← coalescenceProb_eq_deathProb]
  refine Finset.sum_nonneg fun G _ => ?_
  split_ifs
  · exact kingmanTransition_nonneg ht _ _
  · exact le_rfl

/-- The rows of the powers of the generator of the pure death process sum to `0` (except for the
identity). -/
private theorem fact_sum_deathPow (m k : ℕ) :
    ∑ j ∈ range (k + 1), deathPow m k j = if m = 0 then 1 else 0 := by
  induction m generalizing k with
  | zero =>
    simp only [deathPow, ite_true]
    rw [Finset.sum_ite_eq]
    simp
  | succ m ih =>
    simp only [deathPow_succ, ← Finset.mul_sum, Finset.sum_sub_distrib]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [ih k, Finset.sum_range_succ (fun j => deathPow m (k - 1) j) k,
        deathPow_eq_zero_of_lt (by omega : k - 1 < k), add_zero]
      have h := ih (k - 1)
      rw [Nat.sub_add_cancel hk] at h
      rw [h]
      simp

/-- The `g_kj(t)`, `j = 0, …, k`, sum to `1`. -/
theorem deathProb_sum_range (k : ℕ) (t : ℝ) : ∑ j ∈ range (k + 1), deathProb k j t = 1 := by
  have h := hasSum_sum (s := range (k + 1)) fun j _ => hasSum_deathProb k j t
  refine h.unique ?_
  convert hasSum_ite_eq 0 (1 : ℝ) using 1
  funext m
  rw [← Finset.mul_sum, fact_sum_deathPow]
  split_ifs with hm
  · subst hm; simp
  · simp

/-- For `k ≥ 1`, the `g_kj(t)`, `j = 1, …, k`, sum to `1`. -/
theorem deathProb_sum_Icc {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    ∑ j ∈ Icc 1 k, deathProb k j t = 1 := by
  rw [← deathProb_sum_range k t, Finset.sum_range_eq_add_Ico _ (by omega : 0 < k + 1),
    deathProb_zero_right hk, zero_add, Finset.Ico_add_one_right_eq_Icc]

theorem deathProb_le_one (k j : ℕ) {t : ℝ} (ht : 0 ≤ t) : deathProb k j t ≤ 1 := by
  rcases lt_or_ge k j with h | h
  · rw [deathProb_eq_zero_of_lt h]
    exact zero_le_one
  · rw [← deathProb_sum_range k t]
    exact Finset.single_le_sum (fun i _ => deathProb_nonneg k i ht)
      (Finset.mem_range.mpr (by omega))

/-! ### Small cases -/

private theorem fact_deathProb_of_closed {k j : ℕ} (a b c d : ℝ)
    (h : ∀ m, deathPow m k j = a * 0 ^ m + b * (-1) ^ m + c * (-3) ^ m + d * (-6) ^ m) (t : ℝ) :
    deathProb k j t = a + b * exp (-t) + c * exp (-t) ^ 3 + d * exp (-t) ^ 6 := by
  have hs := (((fact_hasSum_exp_mul 0 t).mul_left a).add
    ((fact_hasSum_exp_mul (-1) t).mul_left b)).add ((fact_hasSum_exp_mul (-3) t).mul_left c)
      |>.add ((fact_hasSum_exp_mul (-6) t).mul_left d)
  have e : deathProb k j t =
      a * exp (0 * t) + b * exp (-1 * t) + c * exp (-3 * t) + d * exp (-6 * t) := by
    refine HasSum.tsum_eq ?_
    convert hs using 1
    funext m
    rw [h m]
    ring
  rw [e, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  · congr 1
    · congr 1
      · simp
      · ring_nf
    · congr 2
      push_cast
      ring
  · congr 2
    push_cast
    ring

private theorem fact_deathPow_two_one (m : ℕ) :
    deathPow m 2 1 = 1 * 0 ^ m + (-1) * (-1) ^ m + 0 * (-3) ^ m + 0 * (-6) ^ m := by
  induction m with
  | zero => simp [deathPow]
  | succ m ih =>
    rw [deathPow_succ, ih, show (2 : ℕ) - 1 = 1 from rfl, deathPow_self,
      show Nat.choose 2 2 = 1 from rfl, show Nat.choose 1 2 = 0 from rfl]
    push_cast
    ring

private theorem fact_deathPow_three_two (m : ℕ) :
    deathPow m 3 2 = 0 * 0 ^ m + 3 / 2 * (-1) ^ m + (-3 / 2) * (-3) ^ m + 0 * (-6) ^ m := by
  induction m with
  | zero => simp [deathPow]; norm_num
  | succ m ih =>
    rw [deathPow_succ, ih, show (3 : ℕ) - 1 = 2 from rfl, deathPow_self,
      show Nat.choose 3 2 = 3 from rfl, show Nat.choose 2 2 = 1 from rfl]
    push_cast
    ring

private theorem fact_deathPow_three_one (m : ℕ) :
    deathPow m 3 1 = 1 * 0 ^ m + (-3 / 2) * (-1) ^ m + 1 / 2 * (-3) ^ m + 0 * (-6) ^ m := by
  induction m with
  | zero => simp [deathPow]; norm_num
  | succ m ih =>
    rw [deathPow_succ, ih, show (3 : ℕ) - 1 = 2 from rfl, fact_deathPow_two_one,
      show Nat.choose 3 2 = 3 from rfl]
    push_cast
    ring

private theorem fact_deathPow_four_three (m : ℕ) :
    deathPow m 4 3 = 0 * 0 ^ m + 0 * (-1) ^ m + 2 * (-3) ^ m + (-2) * (-6) ^ m := by
  induction m with
  | zero => simp [deathPow]
  | succ m ih =>
    rw [deathPow_succ, ih, show (4 : ℕ) - 1 = 3 from rfl, deathPow_self,
      show Nat.choose 4 2 = 6 from rfl, show Nat.choose 3 2 = 3 from rfl]
    push_cast
    ring

private theorem fact_deathPow_four_two (m : ℕ) :
    deathPow m 4 2 = 0 * 0 ^ m + 9 / 5 * (-1) ^ m + (-3) * (-3) ^ m + 6 / 5 * (-6) ^ m := by
  induction m with
  | zero => simp [deathPow]; norm_num
  | succ m ih =>
    rw [deathPow_succ, ih, show (4 : ℕ) - 1 = 3 from rfl, fact_deathPow_three_two,
      show Nat.choose 4 2 = 6 from rfl]
    push_cast
    ring

private theorem fact_deathPow_four_one (m : ℕ) :
    deathPow m 4 1 = 1 * 0 ^ m + (-9 / 5) * (-1) ^ m + 1 * (-3) ^ m + (-1 / 5) * (-6) ^ m := by
  induction m with
  | zero => simp [deathPow]; norm_num
  | succ m ih =>
    rw [deathPow_succ, ih, show (4 : ℕ) - 1 = 3 from rfl, fact_deathPow_three_one,
      show Nat.choose 4 2 = 6 from rfl]
    push_cast
    ring

/-- The closed forms of `g_kj(t)` for `k ≤ 4`, in terms of `T = e^{-t}`. -/
theorem deathProb_small (t : ℝ) :
    let T := exp (-t)
    deathProb 0 0 t = 1 ∧ deathProb 1 1 t = 1 ∧
    deathProb 2 1 t = 1 - T ∧ deathProb 2 2 t = T ∧
    deathProb 3 1 t = 1 - 3 / 2 * T + 1 / 2 * T ^ 3 ∧ deathProb 3 2 t = 3 / 2 * T - 3 / 2 * T ^ 3 ∧
      deathProb 3 3 t = T ^ 3 ∧
    deathProb 4 1 t = 1 - 9 / 5 * T + T ^ 3 - 1 / 5 * T ^ 6 ∧
      deathProb 4 2 t = 9 / 5 * T - 3 * T ^ 3 + 6 / 5 * T ^ 6 ∧
      deathProb 4 3 t = 2 * T ^ 3 - 2 * T ^ 6 ∧ deathProb 4 4 t = T ^ 6 := by
  intro T
  have hT3 : exp (-(((Nat.choose 3 2 : ℕ) : ℝ) * t)) = T ^ 3 := by
    rw [← Real.exp_nat_mul, show Nat.choose 3 2 = 3 from rfl]
    push_cast
    ring_nf
  have hT6 : exp (-(((Nat.choose 4 2 : ℕ) : ℝ) * t)) = T ^ 6 := by
    rw [← Real.exp_nat_mul, show Nat.choose 4 2 = 6 from rfl]
    push_cast
    ring_nf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [deathProb_self]; simp
  · rw [deathProb_self]; simp
  · rw [fact_deathProb_of_closed _ _ _ _ fact_deathPow_two_one]; ring
  · rw [deathProb_self, show Nat.choose 2 2 = 1 from rfl]; simp [T]
  · rw [fact_deathProb_of_closed _ _ _ _ fact_deathPow_three_one]; ring
  · rw [fact_deathProb_of_closed _ _ _ _ fact_deathPow_three_two]; ring
  · rw [deathProb_self, hT3]
  · rw [fact_deathProb_of_closed _ _ _ _ fact_deathPow_four_one]; ring
  · rw [fact_deathProb_of_closed _ _ _ _ fact_deathPow_four_two]; ring
  · rw [fact_deathProb_of_closed _ _ _ _ fact_deathPow_four_three]; ring
  · rw [deathProb_self, hT6]

end ADR11
