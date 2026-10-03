module

public import ADR11.Identifiability.FiveTaxa.Common

/-!
# The five-taxon analysis: rootings of the unrooted tree `U5 1`

Two species trees on `Fin 5` whose hierarchies are rootings of `U5 1 = {AB|CDE}`, with the same
unrooted gene tree probabilities `u₁, …, u₁₅` and the same length `t₁` of the internal edge
`AB|CDE` of the unrooted tree, have the same rooted metric tree.

The eight rootings (`ADR11.rootings5 1`) are told apart by the signs of `u₁ - u₂`, `u₁ - u₃`,
`u₄ - u₁₃` and `u₄ - u₅`, except for the root on the internal edge `AB|CDE` (where
`15 u₅ > e^{-3 t₁}`) versus the root `a,b,(c,d,e)` (where equality holds). This is encoded by the
index `five_code1 τ`, a function of the data, which equals the position of the hierarchy of `τ`
in the list. The lengths of the edges are then read off one probability.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-- The rootings of `U5 1`, in the order of `ADR11.rootings5 1`. -/
private def five_R1 : ℕ → Finset (Finset (Fin 5))
  | 0 => hierarchyOf {{0, 1}}
  | 1 => hierarchyOf {{2, 3, 4}}
  | 2 => hierarchyOf {{0, 1}, {2, 3, 4}}
  | 3 => hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}
  | 4 => hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}}
  | 5 => hierarchyOf {{0, 1}, {0, 1, 3, 4}}
  | 6 => hierarchyOf {{0, 1}, {0, 1, 2, 4}}
  | _ => hierarchyOf {{0, 1}, {0, 1, 2, 3}}

/-- The position of the rooting, read off the gene tree probabilities and the length of the
internal edge of the unrooted tree. -/
private noncomputable def five_code1 (τ : SpeciesTree (Fin 5)) : ℕ :=
  if u τ 2 < u τ 1 then 5
  else if u τ 1 < u τ 2 then 6
  else if u τ 1 < u τ 3 then 7
  else if u τ 4 < u τ 13 then 3
  else if u τ 13 < u τ 4 then 4
  else if u τ 5 < u τ 4 then
    (if 15 * u τ 5 = exp (-τ.unrootedLength {0, 1}) ^ 3 then 1 else 2)
  else 0

/-! ### The index of each rooting -/

private lemma five_code1_0 (τ : SpeciesTree (Fin 5)) (h : τ.clusters = hierarchyOf {{0, 1}}) :
    five_code1 τ = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_1_0 τ h
  have f1 : u τ 1 = u τ 2 := by rw [h1, h2]
  have f2 : u τ 1 = u τ 3 := by rw [h1, h3]
  have f3 : u τ 4 = u τ 13 := by rw [h4, h13]
  have f4 : u τ 4 = u τ 5 := by rw [h4, h5]
  rw [five_code1, ite_eq_right f1.not_gt, ite_eq_right f1.not_lt, ite_eq_right f2.not_lt,
    ite_eq_right f3.not_lt, ite_eq_right f3.not_gt, ite_eq_right f4.not_gt]

private lemma five_code1_1 (τ : SpeciesTree (Fin 5)) (h : τ.clusters = hierarchyOf {{2, 3, 4}}) :
    five_code1 τ = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_1_1 τ h
  obtain ⟨b0, b1⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
  have t1 : τ.unrootedLength {0, 1} = τ.length {2, 3, 4} :=
    five_unrootedLength_compl_mem τ (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide)
  have k := mul_pos b0 (sub_pos.2 (pow_lt_one₀ b0.le b1 (by decide : (2 : ℕ) ≠ 0)))
  have f1 : u τ 1 = u τ 2 := by rw [h1, h2]
  have f2 : u τ 1 = u τ 3 := by rw [h1, h3]
  have f3 : u τ 4 = u τ 13 := by rw [h4, h13]
  have f4 : u τ 5 < u τ 4 := by rw [h4, h5]; linarith
  have f5 : 15 * u τ 5 = exp (-τ.unrootedLength {0, 1}) ^ 3 := by rw [t1, h5]; ring
  rw [five_code1, ite_eq_right f1.not_gt, ite_eq_right f1.not_lt, ite_eq_right f2.not_lt,
    ite_eq_right f3.not_lt, ite_eq_right f3.not_gt, ite_eq_left f4, ite_eq_left f5]

private lemma five_code1_2 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {2, 3, 4}}) : five_code1 τ = 2 := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_1_2 τ h
  obtain ⟨a0, a1⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨b0, b1⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
  have t1 : τ.unrootedLength {0, 1} = τ.length {0, 1} + τ.length {2, 3, 4} :=
    five_unrootedLength_both τ (by decide) (by rw [h]; decide) (by decide) (by rw [h]; decide)
      (by decide)
  have k1 := mul_pos (mul_pos a0 b0)
    (sub_pos.2 (pow_lt_one₀ b0.le b1 (by decide : (2 : ℕ) ≠ 0)))
  have k2 := mul_pos (mul_pos a0 (pow_pos b0 3))
    (sub_pos.2 (pow_lt_one₀ a0.le a1 (by decide : (2 : ℕ) ≠ 0)))
  have f1 : u τ 1 = u τ 2 := by rw [h1, h2]
  have f2 : u τ 1 = u τ 3 := by rw [h1, h3]
  have f3 : u τ 4 = u τ 13 := by rw [h4, h13]
  have f4 : u τ 5 < u τ 4 := by rw [h4, h5]; linarith
  have f5 : exp (-τ.unrootedLength {0, 1}) ^ 3 < 15 * u τ 5 := by
    rw [t1, neg_add, Real.exp_add, h5]; linarith
  rw [five_code1, ite_eq_right f1.not_gt, ite_eq_right f1.not_lt, ite_eq_right f2.not_lt,
    ite_eq_right f3.not_lt, ite_eq_right f3.not_gt, ite_eq_left f4, ite_eq_right f5.ne']

private lemma five_code1_3 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}) : five_code1 τ = 3 := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_1_3 τ h
  obtain ⟨b0, -⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {1, 2, 3, 4}) (by rw [h]; decide) (by decide)
  have k := mul_pos (pow_pos b0 3) (sub_pos.2 (pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)))
  have f1 : u τ 1 = u τ 2 := by rw [h1, h2]
  have f2 : u τ 1 = u τ 3 := by rw [h1, h3]
  have f3 : u τ 4 < u τ 13 := by rw [h4, h13]; linarith
  rw [five_code1, ite_eq_right f1.not_gt, ite_eq_right f1.not_lt, ite_eq_right f2.not_lt,
    ite_eq_left f3]

private lemma five_code1_4 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}}) : five_code1 τ = 4 := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_1_4 τ h
  obtain ⟨b0, -⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {0, 2, 3, 4}) (by rw [h]; decide) (by decide)
  have k := mul_pos (pow_pos b0 3) (sub_pos.2 (pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)))
  have f1 : u τ 1 = u τ 2 := by rw [h1, h2]
  have f2 : u τ 1 = u τ 3 := by rw [h1, h3]
  have f3 : u τ 13 < u τ 4 := by rw [h4, h13]; linarith
  rw [five_code1, ite_eq_right f1.not_gt, ite_eq_right f1.not_lt, ite_eq_right f2.not_lt,
    ite_eq_right (lt_asymm f3), ite_eq_left f3]

private lemma five_code1_5 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 3, 4}}) : five_code1 τ = 5 := by
  obtain ⟨h1, h2, -⟩ := rootingDist5_1_5 τ h
  obtain ⟨a0, -⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {0, 1, 3, 4}) (by rw [h]; decide) (by decide)
  have k := mul_pos a0 (sub_pos.2 (pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)))
  have f : u τ 2 < u τ 1 := by rw [h1, h2]; linarith
  rw [five_code1, ite_eq_left f]

private lemma five_code1_6 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 4}}) : five_code1 τ = 6 := by
  obtain ⟨h1, h2, -⟩ := rootingDist5_1_6 τ h
  obtain ⟨a0, -⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {0, 1, 2, 4}) (by rw [h]; decide) (by decide)
  have k := mul_pos a0 (sub_pos.2 (pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)))
  have f : u τ 1 < u τ 2 := by rw [h1, h2]; linarith
  rw [five_code1, ite_eq_right (lt_asymm f), ite_eq_left f]

private lemma five_code1_7 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 3}}) : five_code1 τ = 7 := by
  obtain ⟨h1, h2, h3, -⟩ := rootingDist5_1_7 τ h
  obtain ⟨a0, -⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {0, 1, 2, 3}) (by rw [h]; decide) (by decide)
  have k := mul_pos a0 (sub_pos.2 (pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)))
  have f1 : u τ 1 = u τ 2 := by rw [h1, h2]
  have f2 : u τ 1 < u τ 3 := by rw [h1, h3]; linarith
  rw [five_code1, ite_eq_right f1.not_gt, ite_eq_right f1.not_lt, ite_eq_left f2]

/-- The hierarchy of a rooting of `U5 1` is the one at position `five_code1 τ`. -/
private lemma five_R1_code1 (τ : SpeciesTree (Fin 5)) (hR : τ.clusters ∈ rootings5 1) :
    τ.clusters = five_R1 (five_code1 τ) := by
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h | h | h
  · rw [five_code1_0 τ h]; exact h
  · rw [five_code1_1 τ h]; exact h
  · rw [five_code1_2 τ h]; exact h
  · rw [five_code1_3 τ h]; exact h
  · rw [five_code1_4 τ h]; exact h
  · rw [five_code1_5 τ h]; exact h
  · rw [five_code1_6 τ h]; exact h
  · rw [five_code1_7 τ h]; exact h

/-! ### The lengths of the edges of each rooting -/

section Lengths

variable {τ τ' : SpeciesTree (Fin 5)} (hu : u τ = u τ')
  (ht1 : τ.unrootedLength {0, 1} = τ'.unrootedLength {0, 1})
include hu ht1

omit hu in
private lemma five_same1_0 (h : τ.clusters = hierarchyOf {{0, 1}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}}) : τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {0, 1} = τ'.length {0, 1} := by
    rwa [five_unrootedLength_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {2, 3, 4}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_singleton, forall_eq]
  exact l1

omit hu in
private lemma five_same1_1 (h : τ.clusters = hierarchyOf {{2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{2, 3, 4}}) : τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {2, 3, 4} = τ'.length {2, 3, 4} := by
    rwa [five_unrootedLength_compl_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide)
      (by decide) (by rw [h]; decide), five_unrootedLength_compl_mem τ' (T := {2, 3, 4})
      (by decide) (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_singleton, forall_eq]
  exact l1

private lemma five_same1_2 (h : τ.clusters = hierarchyOf {{0, 1}, {2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {2, 3, 4}}) : τ.SameRootedMetricTree τ' := by
  have s1 : τ.length {0, 1} + τ.length {2, 3, 4} = τ'.length {0, 1} + τ'.length {2, 3, 4} := by
    rwa [five_unrootedLength_both τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide) (by decide), five_unrootedLength_both τ' (T := {2, 3, 4}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide) (by decide)] at ht1
  obtain ⟨-, -, -, -, f, -⟩ := rootingDist5_1_2 τ h
  obtain ⟨-, -, -, -, f', -⟩ := rootingDist5_1_2 τ' h'
  have l2 : τ.length {2, 3, 4} = τ'.length {2, 3, 4} :=
    five_length_eq (n := 2) (v := u τ' 5) (B := 0)
      (A := 1 / 15 * exp (-(τ'.length {0, 1} + τ'.length {2, 3, 4})))
      (by decide) (by positivity)
      (by rw [← hu, f, ← s1, neg_add, Real.exp_add]; ring)
      (by rw [f', neg_add, Real.exp_add]; ring)
  have l1 : τ.length {0, 1} = τ'.length {0, 1} := by linarith
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l2⟩

private lemma five_same1_3 (h : τ.clusters = hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}) : τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {2, 3, 4} = τ'.length {2, 3, 4} := by
    rwa [five_unrootedLength_compl_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide)
      (by decide) (by rw [h]; decide), five_unrootedLength_compl_mem τ' (T := {2, 3, 4})
      (by decide) (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  obtain ⟨-, -, -, -, f, -⟩ := rootingDist5_1_3 τ h
  obtain ⟨-, -, -, -, f', -⟩ := rootingDist5_1_3 τ' h'
  have l2 : τ.length {1, 2, 3, 4} = τ'.length {1, 2, 3, 4} :=
    five_length_eq (n := 6) (v := u τ' 5)
      (A := 1 / 90 * exp (-τ'.length {2, 3, 4}) ^ 3) (B := 1 / 18 * exp (-τ'.length {2, 3, 4}) ^ 3)
      (by decide) (by positivity) (by rw [← hu, f, l1]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l2⟩

private lemma five_same1_4 (h : τ.clusters = hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}}) : τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {2, 3, 4} = τ'.length {2, 3, 4} := by
    rwa [five_unrootedLength_compl_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide)
      (by decide) (by rw [h]; decide), five_unrootedLength_compl_mem τ' (T := {2, 3, 4})
      (by decide) (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  obtain ⟨-, -, -, -, f, -⟩ := rootingDist5_1_4 τ h
  obtain ⟨-, -, -, -, f', -⟩ := rootingDist5_1_4 τ' h'
  have l2 : τ.length {0, 2, 3, 4} = τ'.length {0, 2, 3, 4} :=
    five_length_eq (n := 6) (v := u τ' 5)
      (A := 1 / 90 * exp (-τ'.length {2, 3, 4}) ^ 3) (B := 1 / 18 * exp (-τ'.length {2, 3, 4}) ^ 3)
      (by decide) (by positivity) (by rw [← hu, f, l1]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l2⟩

private lemma five_same1_5 (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {0, 1, 3, 4}}) : τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {0, 1} = τ'.length {0, 1} := by
    rwa [five_unrootedLength_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {2, 3, 4}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  obtain ⟨-, -, -, f, -⟩ := rootingDist5_1_5 τ h
  obtain ⟨-, -, -, f', -⟩ := rootingDist5_1_5 τ' h'
  have l2 : τ.length {0, 1, 3, 4} = τ'.length {0, 1, 3, 4} :=
    five_length_eq (n := 6) (v := u τ' 4)
      (A := 1 / 90 * exp (-τ'.length {0, 1})) (B := 1 / 18 * exp (-τ'.length {0, 1}))
      (by decide) (by positivity) (by rw [← hu, f, l1]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l2⟩

private lemma five_same1_6 (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 4}}) : τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {0, 1} = τ'.length {0, 1} := by
    rwa [five_unrootedLength_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {2, 3, 4}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  obtain ⟨-, -, -, f, -⟩ := rootingDist5_1_6 τ h
  obtain ⟨-, -, -, f', -⟩ := rootingDist5_1_6 τ' h'
  have l2 : τ.length {0, 1, 2, 4} = τ'.length {0, 1, 2, 4} :=
    five_length_eq (n := 6) (v := u τ' 4)
      (A := 1 / 90 * exp (-τ'.length {0, 1})) (B := 1 / 18 * exp (-τ'.length {0, 1}))
      (by decide) (by positivity) (by rw [← hu, f, l1]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l2⟩

private lemma five_same1_7 (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 3}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 3}}) : τ.SameRootedMetricTree τ' := by
  have l1 : τ.length {0, 1} = τ'.length {0, 1} := by
    rwa [five_unrootedLength_mem τ (T := {2, 3, 4}) (by decide) (by rw [h]; decide) (by decide)
      (by rw [h]; decide), five_unrootedLength_mem τ' (T := {2, 3, 4}) (by decide)
      (by rw [h']; decide) (by decide) (by rw [h']; decide)] at ht1
  obtain ⟨-, -, -, f, -⟩ := rootingDist5_1_7 τ h
  obtain ⟨-, -, -, f', -⟩ := rootingDist5_1_7 τ' h'
  have l2 : τ.length {0, 1, 2, 3} = τ'.length {0, 1, 2, 3} :=
    five_length_eq (n := 6) (v := u τ' 4)
      (A := 1 / 90 * exp (-τ'.length {0, 1})) (B := 1 / 18 * exp (-τ'.length {0, 1}))
      (by decide) (by positivity) (by rw [← hu, f, l1]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1, l2⟩

end Lengths

/-- Two rootings of `U5 1` with the same unrooted gene tree probabilities and the same length of
the internal edge of the unrooted tree have the same rooted metric tree. -/
theorem five_sameRootedMetricTree_one (τ τ' : SpeciesTree (Fin 5))
    (hR : τ.clusters ∈ rootings5 1) (hR' : τ'.clusters ∈ rootings5 1) (hu : u τ = u τ')
    (ht1 : τ.unrootedLength {0, 1} = τ'.unrootedLength {0, 1}) :
    τ.SameRootedMetricTree τ' := by
  have hcode : five_code1 τ = five_code1 τ' := by
    unfold five_code1
    rw [hu, ht1]
  have hc : τ'.clusters = τ.clusters := by
    rw [five_R1_code1 τ' hR', ← hcode, ← five_R1_code1 τ hR]
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h | h | h
  · exact five_same1_0 ht1 h (hc.trans h)
  · exact five_same1_1 ht1 h (hc.trans h)
  · exact five_same1_2 hu ht1 h (hc.trans h)
  · exact five_same1_3 hu ht1 h (hc.trans h)
  · exact five_same1_4 hu ht1 h (hc.trans h)
  · exact five_same1_5 hu ht1 h (hc.trans h)
  · exact five_same1_6 hu ht1 h (hc.trans h)
  · exact five_same1_7 hu ht1 h (hc.trans h)

end ADR11
