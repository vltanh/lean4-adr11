module

public import ADR11.Identifiability.FiveTaxa.Common

/-!
# The five-taxon analysis: rootings of the binary unrooted tree `U5 2`

Two species trees on `Fin 5` whose hierarchies are rootings of `U5 2 = {AB|CDE, ABC|DE}`, with
the same unrooted gene tree probabilities `u₁, …, u₁₅` and the same lengths `t₁, t₂` of the two
internal edges `AB|CDE`, `ABC|DE` of the unrooted tree, have the same rooted metric tree.

The ten rootings (`ADR11.rootings5 2`) are told apart by the signs of `u₂ - u₃`, `u₄ - u₁₃`,
`u₅ - u₈` and `u₅ - u₇`, except for two pairs: the root on the internal edge `ABC|DE` (where
`15 u₇ > e^{-t₁} e^{-3 t₂}`) versus the trifurcating root `((a,b),c),d,e` (where equality holds),
and symmetrically the root on the edge `AB|CDE` versus `a,b,((d,e),c)` (with `u₅`). This is
encoded by the index `five_code2 τ`, a function of the data, which equals the position of the
hierarchy of `τ` in the list. The lengths of the edges are then read off one probability.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-- The rootings of `U5 2`, in the order of `ADR11.rootings5 2`. -/
private def five_R2 : ℕ → Finset (Finset (Fin 5))
  | 0 => hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}
  | 1 => hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}}
  | 2 => hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}
  | 3 => hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}}
  | 4 => hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}
  | 5 => hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}}
  | 6 => hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}}
  | 7 => hierarchyOf {{0, 1}, {3, 4}}
  | 8 => hierarchyOf {{0, 1}, {0, 1, 2}}
  | _ => hierarchyOf {{3, 4}, {2, 3, 4}}

/-- The position of the rooting, read off the gene tree probabilities and the lengths of the
internal edges of the unrooted tree. -/
private noncomputable def five_code2 (τ : SpeciesTree (Fin 5)) : ℕ :=
  if u τ 2 < u τ 3 then 0
  else if u τ 3 < u τ 2 then 1
  else if u τ 4 < u τ 13 then 2
  else if u τ 13 < u τ 4 then 3
  else if u τ 5 < u τ 8 then 4
  else if u τ 7 < u τ 5 then
    (if 15 * u τ 7 = exp (-τ.unrootedLength {0, 1}) * exp (-τ.unrootedLength {3, 4}) ^ 3 then 8
      else 5)
  else if u τ 5 < u τ 7 then
    (if 15 * u τ 5 = exp (-τ.unrootedLength {0, 1}) ^ 3 * exp (-τ.unrootedLength {3, 4}) then 9
      else 6)
  else 7

/-! ### The index of each rooting -/

private lemma five_code2_0 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}) : five_code2 τ = 0 := by
  obtain ⟨-, h2, h3, -⟩ := rootingDist5_2_0 τ h
  obtain ⟨a0, -⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨b0, -⟩ := five_exp_bounds τ (A := {0, 1, 2}) (by rw [h]; decide) (by decide)
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {0, 1, 2, 3}) (by rw [h]; decide) (by decide)
  have k := mul_pos (mul_pos a0 (pow_pos b0 3))
    (sub_pos.2 (pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)))
  have f : u τ 2 < u τ 3 := by rw [h2, h3]; linarith
  rw [five_code2, ite_eq_left f]

private lemma five_code2_1 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}}) : five_code2 τ = 1 := by
  obtain ⟨-, h2, h3, -⟩ := rootingDist5_2_1 τ h
  obtain ⟨a0, -⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨b0, -⟩ := five_exp_bounds τ (A := {0, 1, 2}) (by rw [h]; decide) (by decide)
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {0, 1, 2, 4}) (by rw [h]; decide) (by decide)
  have k := mul_pos (mul_pos a0 (pow_pos b0 3))
    (sub_pos.2 (pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)))
  have f : u τ 3 < u τ 2 := by rw [h2, h3]; linarith
  rw [five_code2, ite_eq_right (lt_asymm f), ite_eq_left f]

private lemma five_code2_2 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}) : five_code2 τ = 2 := by
  obtain ⟨-, h2, h3, h4, -, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_2_2 τ h
  obtain ⟨a0, -⟩ := five_exp_bounds τ (A := {3, 4}) (by rw [h]; decide) (by decide)
  obtain ⟨b0, -⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {1, 2, 3, 4}) (by rw [h]; decide) (by decide)
  have k := mul_pos (mul_pos a0 (pow_pos b0 3))
    (sub_pos.2 (pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)))
  have f1 : u τ 2 = u τ 3 := by rw [h2, h3]
  have f2 : u τ 4 < u τ 13 := by rw [h4, h13]; linarith
  rw [five_code2, ite_eq_right f1.not_lt, ite_eq_right f1.not_gt, ite_eq_left f2]

private lemma five_code2_3 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}}) : five_code2 τ = 3 := by
  obtain ⟨-, h2, h3, h4, -, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_2_3 τ h
  obtain ⟨a0, -⟩ := five_exp_bounds τ (A := {3, 4}) (by rw [h]; decide) (by decide)
  obtain ⟨b0, -⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {0, 2, 3, 4}) (by rw [h]; decide) (by decide)
  have k := mul_pos (mul_pos a0 (pow_pos b0 3))
    (sub_pos.2 (pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)))
  have f1 : u τ 2 = u τ 3 := by rw [h2, h3]
  have f2 : u τ 13 < u τ 4 := by rw [h4, h13]; linarith
  rw [five_code2, ite_eq_right f1.not_lt, ite_eq_right f1.not_gt, ite_eq_right (lt_asymm f2), ite_eq_left f2]

private lemma five_code2_4 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}) : five_code2 τ = 4 := by
  obtain ⟨-, h2, h3, h4, h5, -, -, h8, -, -, -, -, h13, -⟩ := rootingDist5_2_4 τ h
  obtain ⟨a0, -⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨b0, -⟩ := five_exp_bounds τ (A := {3, 4}) (by rw [h]; decide) (by decide)
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {0, 1, 3, 4}) (by rw [h]; decide) (by decide)
  have k := mul_pos (mul_pos a0 b0)
    (sub_pos.2 (pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)))
  have f1 : u τ 2 = u τ 3 := by rw [h2, h3]
  have f2 : u τ 4 = u τ 13 := by rw [h4, h13]
  have f3 : u τ 5 < u τ 8 := by rw [h5, h8]; linarith
  rw [five_code2, ite_eq_right f1.not_lt, ite_eq_right f1.not_gt, ite_eq_right f2.not_lt, ite_eq_right f2.not_gt,
    ite_eq_left f3]

private lemma five_code2_5 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}}) : five_code2 τ = 5 := by
  obtain ⟨-, h2, h3, h4, h5, -, h7, h8, -, -, -, -, h13, -⟩ := rootingDist5_2_5 τ h
  obtain ⟨a0, -⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨b0, b1⟩ := five_exp_bounds τ (A := {3, 4}) (by rw [h]; decide) (by decide)
  obtain ⟨w0, w1⟩ := five_exp_bounds τ (A := {0, 1, 2}) (by rw [h]; decide) (by decide)
  have t1 : τ.unrootedLength {0, 1} = τ.length {0, 1} :=
    five_unrootedLength_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide)
  have t2 : τ.unrootedLength {3, 4} = τ.length {3, 4} + τ.length {0, 1, 2} :=
    five_unrootedLength_both τ (by decide) (by rw [h]; decide) (by decide) (by rw [h]; decide)
      (by decide)
  have k1 := mul_pos (mul_pos (mul_pos a0 b0) w0)
    (sub_pos.2 (pow_lt_one₀ w0.le w1 (by decide : (2 : ℕ) ≠ 0)))
  have k2 := mul_pos (mul_pos (mul_pos a0 b0) (pow_pos w0 3))
    (sub_pos.2 (pow_lt_one₀ b0.le b1 (by decide : (2 : ℕ) ≠ 0)))
  have f1 : u τ 2 = u τ 3 := by rw [h2, h3]
  have f2 : u τ 4 = u τ 13 := by rw [h4, h13]
  have f3 : u τ 8 < u τ 5 := by rw [h5, h8]; linarith
  have f4 : u τ 7 < u τ 5 := by rw [h5, h7]; linarith
  have f5 : exp (-τ.unrootedLength {0, 1}) * exp (-τ.unrootedLength {3, 4}) ^ 3 < 15 * u τ 7 := by
    rw [t1, t2, neg_add, Real.exp_add, h7]; linarith
  rw [five_code2, ite_eq_right f1.not_lt, ite_eq_right f1.not_gt, ite_eq_right f2.not_lt, ite_eq_right f2.not_gt,
    ite_eq_right (lt_asymm f3), ite_eq_left f4, ite_eq_right f5.ne']

private lemma five_code2_6 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}}) : five_code2 τ = 6 := by
  obtain ⟨-, h2, h3, h4, h5, -, h7, h8, -, -, -, -, h13, -⟩ := rootingDist5_2_6 τ h
  obtain ⟨a0, a1⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨b0, -⟩ := five_exp_bounds τ (A := {3, 4}) (by rw [h]; decide) (by decide)
  obtain ⟨w0, w1⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
  have t1 : τ.unrootedLength {0, 1} = τ.length {0, 1} + τ.length {2, 3, 4} :=
    five_unrootedLength_both τ (by decide) (by rw [h]; decide) (by decide) (by rw [h]; decide)
      (by decide)
  have t2 : τ.unrootedLength {3, 4} = τ.length {3, 4} :=
    five_unrootedLength_mem τ (T := {0, 1, 2}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide)
  have k1 := mul_pos (mul_pos (mul_pos a0 b0) w0)
    (sub_pos.2 (pow_lt_one₀ w0.le w1 (by decide : (2 : ℕ) ≠ 0)))
  have k2 := mul_pos (mul_pos (mul_pos a0 b0) (pow_pos w0 3))
    (sub_pos.2 (pow_lt_one₀ a0.le a1 (by decide : (2 : ℕ) ≠ 0)))
  have f1 : u τ 2 = u τ 3 := by rw [h2, h3]
  have f2 : u τ 4 = u τ 13 := by rw [h4, h13]
  have f3 : u τ 5 = u τ 8 := by rw [h5, h8]
  have f4 : u τ 5 < u τ 7 := by rw [h5, h7]; linarith
  have f5 : exp (-τ.unrootedLength {0, 1}) ^ 3 * exp (-τ.unrootedLength {3, 4}) < 15 * u τ 5 := by
    rw [t1, t2, neg_add, Real.exp_add, h5]; linarith
  rw [five_code2, ite_eq_right f1.not_lt, ite_eq_right f1.not_gt, ite_eq_right f2.not_lt, ite_eq_right f2.not_gt,
    ite_eq_right f3.not_lt, ite_eq_right (lt_asymm f4), ite_eq_left f4, ite_eq_right f5.ne']

private lemma five_code2_7 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {3, 4}}) : five_code2 τ = 7 := by
  obtain ⟨-, h2, h3, h4, h5, -, h7, h8, -, -, -, -, h13, -⟩ := rootingDist5_2_7 τ h
  have f1 : u τ 2 = u τ 3 := by rw [h2, h3]
  have f2 : u τ 4 = u τ 13 := by rw [h4, h13]
  have f3 : u τ 5 = u τ 8 := by rw [h5, h8]
  have f4 : u τ 5 = u τ 7 := by rw [h5, h7]
  rw [five_code2, ite_eq_right f1.not_lt, ite_eq_right f1.not_gt, ite_eq_right f2.not_lt, ite_eq_right f2.not_gt,
    ite_eq_right f3.not_lt, ite_eq_right f4.not_gt, ite_eq_right f4.not_lt]

private lemma five_code2_8 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}}) : five_code2 τ = 8 := by
  obtain ⟨-, h2, h3, h4, h5, -, h7, h8, -, -, -, -, h13, -⟩ := rootingDist5_2_8 τ h
  obtain ⟨a0, -⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨b0, b1⟩ := five_exp_bounds τ (A := {0, 1, 2}) (by rw [h]; decide) (by decide)
  have t1 : τ.unrootedLength {0, 1} = τ.length {0, 1} :=
    five_unrootedLength_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide)
  have t2 : τ.unrootedLength {3, 4} = τ.length {0, 1, 2} :=
    five_unrootedLength_compl_mem τ (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide)
  have k := mul_pos (mul_pos a0 b0) (sub_pos.2 (pow_lt_one₀ b0.le b1 (by decide : (2 : ℕ) ≠ 0)))
  have f1 : u τ 2 = u τ 3 := by rw [h2, h3]
  have f2 : u τ 4 = u τ 13 := by rw [h4, h13]
  have f3 : u τ 8 < u τ 5 := by rw [h5, h8]; linarith
  have f4 : u τ 7 < u τ 5 := by rw [h5, h7]; linarith
  have f5 : 15 * u τ 7 = exp (-τ.unrootedLength {0, 1}) * exp (-τ.unrootedLength {3, 4}) ^ 3 := by
    rw [t1, t2, h7]; ring
  rw [five_code2, ite_eq_right f1.not_lt, ite_eq_right f1.not_gt, ite_eq_right f2.not_lt, ite_eq_right f2.not_gt,
    ite_eq_right (lt_asymm f3), ite_eq_left f4, ite_eq_left f5]

private lemma five_code2_9 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}}) : five_code2 τ = 9 := by
  obtain ⟨-, h2, h3, h4, h5, -, h7, h8, -, -, -, -, h13, -⟩ := rootingDist5_2_9 τ h
  obtain ⟨a0, -⟩ := five_exp_bounds τ (A := {3, 4}) (by rw [h]; decide) (by decide)
  obtain ⟨b0, b1⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
  have t1 : τ.unrootedLength {0, 1} = τ.length {2, 3, 4} :=
    five_unrootedLength_compl_mem τ (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide)
  have t2 : τ.unrootedLength {3, 4} = τ.length {3, 4} :=
    five_unrootedLength_mem τ (T := {0, 1, 2}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide)
  have k := mul_pos (mul_pos a0 b0) (sub_pos.2 (pow_lt_one₀ b0.le b1 (by decide : (2 : ℕ) ≠ 0)))
  have f1 : u τ 2 = u τ 3 := by rw [h2, h3]
  have f2 : u τ 4 = u τ 13 := by rw [h4, h13]
  have f3 : u τ 5 = u τ 8 := by rw [h5, h8]
  have f4 : u τ 5 < u τ 7 := by rw [h5, h7]; linarith
  have f5 : 15 * u τ 5 = exp (-τ.unrootedLength {0, 1}) ^ 3 * exp (-τ.unrootedLength {3, 4}) := by
    rw [t1, t2, h5]; ring
  rw [five_code2, ite_eq_right f1.not_lt, ite_eq_right f1.not_gt, ite_eq_right f2.not_lt, ite_eq_right f2.not_gt,
    ite_eq_right f3.not_lt, ite_eq_right (lt_asymm f4), ite_eq_left f4, ite_eq_left f5]

/-- The hierarchy of a rooting of `U5 2` is the one at position `five_code2 τ`. -/
private lemma five_R2_code2 (τ : SpeciesTree (Fin 5)) (hR : τ.clusters ∈ rootings5 2) :
    τ.clusters = five_R2 (five_code2 τ) := by
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h | h | h | h | h
  · rw [five_code2_0 τ h]; exact h
  · rw [five_code2_1 τ h]; exact h
  · rw [five_code2_2 τ h]; exact h
  · rw [five_code2_3 τ h]; exact h
  · rw [five_code2_4 τ h]; exact h
  · rw [five_code2_5 τ h]; exact h
  · rw [five_code2_6 τ h]; exact h
  · rw [five_code2_7 τ h]; exact h
  · rw [five_code2_8 τ h]; exact h
  · rw [five_code2_9 τ h]; exact h

/-! ### The lengths of the edges of each rooting -/

section Lengths

variable {τ τ' : SpeciesTree (Fin 5)} (hu : u τ = u τ')
  (ht1 : τ.unrootedLength {0, 1} = τ'.unrootedLength {0, 1})
  (ht2 : τ.unrootedLength {3, 4} = τ'.unrootedLength {3, 4})
include hu ht1 ht2

private lemma five_same2_0 (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}) :
    τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {0, 1} = τ'.length {0, 1} := by
    rwa [five_unrootedLength_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {2, 3, 4}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  have l2 : τ.length {0, 1, 2} = τ'.length {0, 1, 2} := by
    rwa [five_unrootedLength_compl_mem τ (T := {0, 1, 2}) (by decide) (by rw [h]; decide)
      (by decide) (by rw [h]; decide), five_unrootedLength_compl_mem τ' (T := {0, 1, 2})
      (by decide) (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht2
  obtain ⟨-, -, -, -, -, -, f, -⟩ := rootingDist5_2_0 τ h
  obtain ⟨-, -, -, -, -, -, f', -⟩ := rootingDist5_2_0 τ' h'
  have l3 : τ.length {0, 1, 2, 3} = τ'.length {0, 1, 2, 3} :=
    five_length_eq (n := 6) (v := u τ' 7)
      (A := 1 / 90 * exp (-τ'.length {0, 1}) * exp (-τ'.length {0, 1, 2}) ^ 3)
      (B := 1 / 18 * exp (-τ'.length {0, 1}) * exp (-τ'.length {0, 1, 2}) ^ 3)
      (by decide) (by positivity) (by rw [← hu, f, l1, l2]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l2, l3⟩

private lemma five_same2_1 (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}}) :
    τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {0, 1} = τ'.length {0, 1} := by
    rwa [five_unrootedLength_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {2, 3, 4}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  have l2 : τ.length {0, 1, 2} = τ'.length {0, 1, 2} := by
    rwa [five_unrootedLength_compl_mem τ (T := {0, 1, 2}) (by decide) (by rw [h]; decide)
      (by decide) (by rw [h]; decide), five_unrootedLength_compl_mem τ' (T := {0, 1, 2})
      (by decide) (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht2
  obtain ⟨-, -, -, -, -, -, f, -⟩ := rootingDist5_2_1 τ h
  obtain ⟨-, -, -, -, -, -, f', -⟩ := rootingDist5_2_1 τ' h'
  have l3 : τ.length {0, 1, 2, 4} = τ'.length {0, 1, 2, 4} :=
    five_length_eq (n := 6) (v := u τ' 7)
      (A := 1 / 90 * exp (-τ'.length {0, 1}) * exp (-τ'.length {0, 1, 2}) ^ 3)
      (B := 1 / 18 * exp (-τ'.length {0, 1}) * exp (-τ'.length {0, 1, 2}) ^ 3)
      (by decide) (by positivity) (by rw [← hu, f, l1, l2]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l2, l3⟩

private lemma five_same2_2 (h : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}) :
    τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {2, 3, 4} = τ'.length {2, 3, 4} := by
    rwa [five_unrootedLength_compl_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide)
      (by decide) (by rw [h]; decide), five_unrootedLength_compl_mem τ' (T := {2, 3, 4})
      (by decide) (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  have l2 : τ.length {3, 4} = τ'.length {3, 4} := by
    rwa [five_unrootedLength_mem τ (T := {0, 1, 2}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {0, 1, 2}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht2
  obtain ⟨-, -, -, -, f, -⟩ := rootingDist5_2_2 τ h
  obtain ⟨-, -, -, -, f', -⟩ := rootingDist5_2_2 τ' h'
  have l3 : τ.length {1, 2, 3, 4} = τ'.length {1, 2, 3, 4} :=
    five_length_eq (n := 6) (v := u τ' 5)
      (A := 1 / 90 * exp (-τ'.length {3, 4}) * exp (-τ'.length {2, 3, 4}) ^ 3)
      (B := 1 / 18 * exp (-τ'.length {3, 4}) * exp (-τ'.length {2, 3, 4}) ^ 3)
      (by decide) (by positivity) (by rw [← hu, f, l1, l2]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l2, l1, l3⟩

private lemma five_same2_3 (h : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}}) :
    τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {2, 3, 4} = τ'.length {2, 3, 4} := by
    rwa [five_unrootedLength_compl_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide)
      (by decide) (by rw [h]; decide), five_unrootedLength_compl_mem τ' (T := {2, 3, 4})
      (by decide) (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  have l2 : τ.length {3, 4} = τ'.length {3, 4} := by
    rwa [five_unrootedLength_mem τ (T := {0, 1, 2}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {0, 1, 2}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht2
  obtain ⟨-, -, -, -, f, -⟩ := rootingDist5_2_3 τ h
  obtain ⟨-, -, -, -, f', -⟩ := rootingDist5_2_3 τ' h'
  have l3 : τ.length {0, 2, 3, 4} = τ'.length {0, 2, 3, 4} :=
    five_length_eq (n := 6) (v := u τ' 5)
      (A := 1 / 90 * exp (-τ'.length {3, 4}) * exp (-τ'.length {2, 3, 4}) ^ 3)
      (B := 1 / 18 * exp (-τ'.length {3, 4}) * exp (-τ'.length {2, 3, 4}) ^ 3)
      (by decide) (by positivity) (by rw [← hu, f, l1, l2]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l2, l1, l3⟩

private lemma five_same2_4 (h : τ.clusters = hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}) :
    τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {0, 1} = τ'.length {0, 1} := by
    rwa [five_unrootedLength_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {2, 3, 4}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  have l2 : τ.length {3, 4} = τ'.length {3, 4} := by
    rwa [five_unrootedLength_mem τ (T := {0, 1, 2}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {0, 1, 2}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht2
  obtain ⟨-, -, -, -, f, -⟩ := rootingDist5_2_4 τ h
  obtain ⟨-, -, -, -, f', -⟩ := rootingDist5_2_4 τ' h'
  have l3 : τ.length {0, 1, 3, 4} = τ'.length {0, 1, 3, 4} :=
    five_length_eq (n := 6) (v := u τ' 5)
      (A := 1 / 90 * exp (-τ'.length {0, 1}) * exp (-τ'.length {3, 4}))
      (B := 1 / 18 * exp (-τ'.length {0, 1}) * exp (-τ'.length {3, 4}))
      (by decide) (by positivity) (by rw [← hu, f, l1, l2]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l2, l3⟩

private lemma five_same2_5 (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}}) :
    τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {0, 1} = τ'.length {0, 1} := by
    rwa [five_unrootedLength_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {2, 3, 4}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  have s2 : τ.length {3, 4} + τ.length {0, 1, 2} = τ'.length {3, 4} + τ'.length {0, 1, 2} := by
    rwa [five_unrootedLength_both τ (T := {0, 1, 2}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide) (by decide), five_unrootedLength_both τ' (T := {0, 1, 2}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide) (by decide)] at ht2
  obtain ⟨-, -, -, -, -, -, f, -⟩ := rootingDist5_2_5 τ h
  obtain ⟨-, -, -, -, -, -, f', -⟩ := rootingDist5_2_5 τ' h'
  have l3 : τ.length {0, 1, 2} = τ'.length {0, 1, 2} :=
    five_length_eq (n := 2) (v := u τ' 7) (B := 0)
      (A := 1 / 15 * exp (-τ'.length {0, 1}) * exp (-(τ'.length {3, 4} + τ'.length {0, 1, 2})))
      (by decide) (by positivity)
      (by rw [← hu, f, ← s2, ← l1, neg_add, Real.exp_add]; ring)
      (by rw [f', neg_add, Real.exp_add]; ring)
  have l2 : τ.length {3, 4} = τ'.length {3, 4} := by linarith
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l3, l2⟩

private lemma five_same2_6 (h : τ.clusters = hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}}) :
    τ.SameRootedMetricTree τ' := by
  have s1 : τ.length {0, 1} + τ.length {2, 3, 4} = τ'.length {0, 1} + τ'.length {2, 3, 4} := by
    rwa [five_unrootedLength_both τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide) (by decide), five_unrootedLength_both τ' (T := {2, 3, 4}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide) (by decide)] at ht1
  have l2 : τ.length {3, 4} = τ'.length {3, 4} := by
    rwa [five_unrootedLength_mem τ (T := {0, 1, 2}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {0, 1, 2}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht2
  obtain ⟨-, -, -, -, f, -⟩ := rootingDist5_2_6 τ h
  obtain ⟨-, -, -, -, f', -⟩ := rootingDist5_2_6 τ' h'
  have l3 : τ.length {2, 3, 4} = τ'.length {2, 3, 4} :=
    five_length_eq (n := 2) (v := u τ' 5) (B := 0)
      (A := 1 / 15 * exp (-(τ'.length {0, 1} + τ'.length {2, 3, 4})) * exp (-τ'.length {3, 4}))
      (by decide) (by positivity)
      (by rw [← hu, f, ← s1, ← l2, neg_add, Real.exp_add]; ring)
      (by rw [f', neg_add, Real.exp_add]; ring)
  have l1 : τ.length {0, 1} = τ'.length {0, 1} := by linarith
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l2, l3⟩

omit hu in
private lemma five_same2_7 (h : τ.clusters = hierarchyOf {{0, 1}, {3, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {3, 4}}) :
    τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {0, 1} = τ'.length {0, 1} := by
    rwa [five_unrootedLength_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {2, 3, 4}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  have l2 : τ.length {3, 4} = τ'.length {3, 4} := by
    rwa [five_unrootedLength_mem τ (T := {0, 1, 2}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {0, 1, 2}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht2
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l2⟩

omit hu in
private lemma five_same2_8 (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {0, 1, 2}}) :
    τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {0, 1} = τ'.length {0, 1} := by
    rwa [five_unrootedLength_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {2, 3, 4}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  have l2 : τ.length {0, 1, 2} = τ'.length {0, 1, 2} := by
    rwa [five_unrootedLength_compl_mem τ (T := {0, 1, 2}) (by decide) (by rw [h]; decide)
      (by decide) (by rw [h]; decide), five_unrootedLength_compl_mem τ' (T := {0, 1, 2})
      (by decide) (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht2
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l2⟩

omit hu in
private lemma five_same2_9 (h : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{3, 4}, {2, 3, 4}}) :
    τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {2, 3, 4} = τ'.length {2, 3, 4} := by
    rwa [five_unrootedLength_compl_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide)
      (by decide) (by rw [h]; decide), five_unrootedLength_compl_mem τ' (T := {2, 3, 4})
      (by decide) (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  have l2 : τ.length {3, 4} = τ'.length {3, 4} := by
    rwa [five_unrootedLength_mem τ (T := {0, 1, 2}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {0, 1, 2}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht2
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l2, l1⟩

end Lengths

/-- Two rootings of `U5 2` with the same unrooted gene tree probabilities and the same lengths of
the internal edges of the unrooted tree have the same rooted metric tree. -/
theorem five_sameRootedMetricTree_two (τ τ' : SpeciesTree (Fin 5))
    (hR : τ.clusters ∈ rootings5 2) (hR' : τ'.clusters ∈ rootings5 2) (hu : u τ = u τ')
    (ht1 : τ.unrootedLength {0, 1} = τ'.unrootedLength {0, 1})
    (ht2 : τ.unrootedLength {3, 4} = τ'.unrootedLength {3, 4}) :
    τ.SameRootedMetricTree τ' := by
  have hcode : five_code2 τ = five_code2 τ' := by
    unfold five_code2
    rw [hu, ht1, ht2]
  have hc : τ'.clusters = τ.clusters := by
    rw [five_R2_code2 τ' hR', ← hcode, ← five_R2_code2 τ hR]
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h | h | h | h | h
  · exact five_same2_0 hu ht1 ht2 h (hc.trans h)
  · exact five_same2_1 hu ht1 ht2 h (hc.trans h)
  · exact five_same2_2 hu ht1 ht2 h (hc.trans h)
  · exact five_same2_3 hu ht1 ht2 h (hc.trans h)
  · exact five_same2_4 hu ht1 ht2 h (hc.trans h)
  · exact five_same2_5 hu ht1 ht2 h (hc.trans h)
  · exact five_same2_6 hu ht1 ht2 h (hc.trans h)
  · exact five_same2_7 ht1 ht2 h (hc.trans h)
  · exact five_same2_8 ht1 ht2 h (hc.trans h)
  · exact five_same2_9 ht1 ht2 h (hc.trans h)

end ADR11
