module

public import ADR11.Coalescent.Factorization

/-!
# Tavaré's formula for the number of lineages in Kingman's coalescent

[S. Tavaré, *Line-of-descent and genealogical processes, and their applications in population
genetics models*, Theoret. Population Biol. 26 (1984) 119–164]

For `1 ≤ j ≤ i`, the probability that `i` lineages coalesce into `j` lineages within time `t` is
`g_ij(t) = ∑_{k=j}^{i} exp(-k(k-1)t/2) a_ijk` with
`a_ijk = (2k-1)(-1)^{k-j} / (j!(k-j)!(j+k-1)) ∏_{m=0}^{k-1} (j+m)(i-m)/(i+m)`;
this is the paper's equation (2). We prove it for `deathProb`, the transition probability of the
pure death process with rates `k.choose 2`, by showing that the entries of the powers of its
generator are `deathPow m i j = ∑_k a_ijk (-(k choose 2))^m`.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-- Tavaré's coefficient `a_ijk`. -/
noncomputable def tavareCoeff (i j k : ℕ) : ℝ :=
  (2 * k - 1) * (-1) ^ (k - j) / ((j.factorial : ℝ) * (k - j).factorial * (j + k - 1)) *
    ∏ m ∈ range k, (((j : ℝ) + m) * ((i : ℝ) - m) / ((i : ℝ) + m))

/-- The death process never increases the number of lineages. -/
private theorem tavare_deathPow_of_lt (m : ℕ) {k j : ℕ} (h : k < j) : deathPow m k j = 0 := by
  induction m generalizing k with
  | zero => simp [deathPow, h.ne]
  | succ m ih => rw [deathPow, ih (by omega), ih h, sub_self, mul_zero]

private theorem tavareCoeff_self {j : ℕ} (hj : 1 ≤ j) : tavareCoeff j j j = 1 := by
  unfold tavareCoeff
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : ∏ m ∈ range j, (((j : ℝ) + m) * ((j : ℝ) - m) / ((j : ℝ) + m)) =
      (j.factorial : ℝ) := by
    rw [prod_congr rfl (fun (m : ℕ) _ => mul_div_cancel_left₀ ((j : ℝ) - (m : ℝ))
      (ne_of_gt (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith :
        (0 : ℝ) < (j : ℝ) + m)))]
    rw [← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine prod_congr rfl fun m hm => ?_
    rw [Nat.cast_sub (by simp only [mem_range] at hm; omega)]
  rw [h1, Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, mul_one,
    show (j : ℝ) + j - 1 = 2 * j - 1 by ring]
  have h2 : (2 * j - 1 : ℝ) ≠ 0 := by linarith
  have h3 : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp

private theorem tavareCoeff_succ_self (i j : ℕ) : tavareCoeff i j (i + 1) = 0 := by
  unfold tavareCoeff
  simp [prod_range_succ]

private theorem tavareCoeff_succ_ratio {i j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    tavareCoeff i j (k + 1) * ((2 * k - 1) * ((k : ℝ) + 1 - j) * ((i : ℝ) + k)) =
      -((2 * k + 1) * ((j : ℝ) + k - 1) * ((i : ℝ) - k)) * tavareCoeff i j k := by
  unfold tavareCoeff
  rw [prod_range_succ, show k + 1 - j = (k - j) + 1 by omega, Nat.factorial_succ, pow_succ]
  push_cast [Nat.cast_sub hjk]
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hi' : (0 : ℝ) ≤ i := by positivity
  have h1 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((k - j).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (j : ℝ) + k - 1 ≠ 0 := by linarith
  have h4 : (j : ℝ) + (k + 1) - 1 ≠ 0 := by linarith
  have h5 : (i : ℝ) + k ≠ 0 := by linarith
  have h6 : (k : ℝ) - j + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Gosper telescoping: `a_ijk = G(k+1) - G(k)` with `G(k) = -(k-j)(i+k-1)/((i-j)(2k-1)) a_ijk`,
so the coefficients sum to zero when `j < i`. -/
private theorem tavare_sum_eq_zero {i j : ℕ} (hj : 1 ≤ j) (hji : j < i) :
    ∑ k ∈ Icc j i, tavareCoeff i j k = 0 := by
  set G : ℕ → ℝ := fun k =>
    -(((k : ℝ) - j) * ((i : ℝ) + k - 1)) / (((i : ℝ) - j) * (2 * k - 1)) * tavareCoeff i j k
    with hG
  have hstep : ∀ k ∈ Icc j i, tavareCoeff i j k = G (k + 1) - G k := by
    intro k hk
    rw [mem_Icc] at hk
    have h := tavareCoeff_succ_ratio (i := i) hj hk.1
    simp only [hG]
    push_cast
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hk' : (j : ℝ) ≤ k := by exact_mod_cast hk.1
    have hij : (j : ℝ) < i := by exact_mod_cast hji
    have h1 : ((i : ℝ) - j) * (2 * ((k : ℝ) + 1) - 1) ≠ 0 :=
      mul_ne_zero (by linarith) (by linarith)
    have h2 : ((i : ℝ) - j) * (2 * k - 1) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_sub_div _ _ h1 h2,
      eq_div_iff (mul_ne_zero h1 h2)]
    linear_combination ((i : ℝ) - j) * h
  rw [sum_congr rfl hstep, sum_Icc_sub hji.le]
  simp [hG, tavareCoeff_succ_self]

/-- The `i`-dependent part of `a_ijk` under `i ↦ i + 1`. -/
private theorem tavare_prod_step (x : ℝ) (hx : 0 < x) (k : ℕ) :
    ((x + 1) * x / 2) * ∏ m ∈ range k, ((x - m) / (x + m)) =
      ((x + 1) * x / 2 - k * (k - 1) / 2) * ∏ m ∈ range k, ((x + 1 - m) / (x + 1 + m)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, prod_range_succ, ← mul_assoc, ih]
    push_cast
    have hk := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have h1 : x + k ≠ 0 := by linarith
    have h2 : x + 1 + k ≠ 0 := by linarith
    field_simp
    ring

/-- `c_{i+1} a_{i,j,k} = (c_{i+1} - c_k) a_{i+1,j,k}`. -/
private theorem tavareCoeff_pred {i j k : ℕ} (hi : 1 ≤ i) :
    (((i + 1).choose 2 : ℕ) : ℝ) * tavareCoeff i j k =
      ((((i + 1).choose 2 : ℕ) : ℝ) - ((k.choose 2 : ℕ) : ℝ)) * tavareCoeff (i + 1) j k := by
  unfold tavareCoeff
  rw [Nat.cast_choose_two, Nat.cast_choose_two]
  have hsplit : ∀ y : ℝ, ∏ m ∈ range k, (((j : ℝ) + m) * (y - m) / (y + m)) =
      (∏ m ∈ range k, ((j : ℝ) + m)) * ∏ m ∈ range k, ((y - m) / (y + m)) := by
    intro y
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun m _ => by ring
  rw [hsplit, hsplit]
  have h := tavare_prod_step (i : ℝ) (by exact_mod_cast hi) k
  push_cast
  linear_combination ((2 * k - 1) * (-1) ^ (k - j) / ((j.factorial : ℝ) * (k - j).factorial *
    (j + k - 1)) * ∏ m ∈ range k, ((j : ℝ) + m)) * h

/-- The spectral form of the powers of the generator of the pure death process. -/
theorem deathPow_eq_tavare (m i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    deathPow m i j = ∑ k ∈ Icc j i, tavareCoeff i j k * (-(((k.choose 2 : ℕ) : ℝ))) ^ m := by
  induction m generalizing i with
  | zero =>
    simp only [deathPow, pow_zero, mul_one]
    rcases eq_or_lt_of_le hji with rfl | hlt
    · simp [tavareCoeff_self hj]
    · rw [tavare_sum_eq_zero hj hlt]
      simp [hlt.ne']
  | succ m ih =>
    rw [deathPow]
    rcases eq_or_lt_of_le hji with rfl | hlt
    · rw [tavare_deathPow_of_lt m (by omega : j - 1 < j), ih j le_rfl, Icc_self, sum_singleton,
        sum_singleton]
      ring
    · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hji' : j ≤ i := by omega
      rw [Nat.add_sub_cancel, ih i hji', ih (i + 1) hji, sum_Icc_succ_top hji, sum_Icc_succ_top hji]
      have h1 : (((i + 1).choose 2 : ℕ) : ℝ) * ∑ k ∈ Icc j i,
            tavareCoeff i j k * (-(((k.choose 2 : ℕ) : ℝ))) ^ m -
          (((i + 1).choose 2 : ℕ) : ℝ) * ∑ k ∈ Icc j i,
            tavareCoeff (i + 1) j k * (-(((k.choose 2 : ℕ) : ℝ))) ^ m =
          ∑ k ∈ Icc j i, tavareCoeff (i + 1) j k * (-(((k.choose 2 : ℕ) : ℝ))) ^ (m + 1) := by
        rw [mul_sum, mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, tavareCoeff_pred (by omega : 1 ≤ i)]
        ring
      linear_combination h1

/-- **Tavaré's formula** (the paper's equation (2)) for the pure death process. -/
theorem deathProb_eq_tavare (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (t : ℝ) :
    deathProb i j t = ∑ k ∈ Icc j i, exp (-(((k.choose 2 : ℕ) : ℝ) * t)) * tavareCoeff i j k := by
  have key : ∀ k ∈ Icc j i, HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ) *
      (tavareCoeff i j k * (-(((k.choose 2 : ℕ) : ℝ))) ^ m))
      (exp (-(((k.choose 2 : ℕ) : ℝ) * t)) * tavareCoeff i j k) := by
    intro k _
    have h := NormedSpace.expSeries_div_hasSum_exp (-(((k.choose 2 : ℕ) : ℝ) * t))
    rw [← Real.exp_eq_exp_ℝ] at h
    convert h.mul_right (tavareCoeff i j k) using 1
    funext m
    rw [neg_mul_eq_neg_mul, mul_pow]
    ring
  unfold deathProb
  rw [← (hasSum_sum key).tsum_eq]
  congr 1
  funext m
  rw [deathPow_eq_tavare m i j hj hji, mul_sum]

end ADR11
