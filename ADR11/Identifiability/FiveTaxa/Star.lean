module

public import ADR11.Identifiability.FiveTaxa.Common

/-!
# The five-taxon analysis: rootings of the star tree `U5 0`

Two species trees on `Fin 5` whose hierarchies are rootings of the star `U5 0`, with the same
unrooted gene tree probabilities `u₁, …, u₁₅`, have the same rooted metric tree.

The six rootings (`ADR11.rootings5 0`: the star, and the five trees with one cluster of four
taxa) are told apart by the signs of `u₁ - u₁₃`, `u₁ - u₄`, `u₁ - u₂` and `u₁ - u₃`: with the
cluster `X ∖ {x}`, the three gene trees with the cherry of `x` and a given other taxon have
probability `1/9 - (2/45) e^{-6 ℓ}`, and the twelve others `1/18 + (1/90) e^{-6 ℓ}`. This is
encoded by the index `five_code0 τ`, a function of the probabilities, which equals the position of
the hierarchy of `τ` in the list. The length `ℓ` is then read off `u₁` or `u₂`.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-- The rootings of `U5 0`, in the order of `ADR11.rootings5 0`. -/
private def five_R0 : ℕ → Finset (Finset (Fin 5))
  | 0 => hierarchyOf ∅
  | 1 => hierarchyOf {{1, 2, 3, 4}}
  | 2 => hierarchyOf {{0, 2, 3, 4}}
  | 3 => hierarchyOf {{0, 1, 3, 4}}
  | 4 => hierarchyOf {{0, 1, 2, 4}}
  | _ => hierarchyOf {{0, 1, 2, 3}}

/-- The position of the rooting, read off the gene tree probabilities. -/
private noncomputable def five_code0 (τ : SpeciesTree (Fin 5)) : ℕ :=
  if u τ 1 < u τ 13 then 1
  else if u τ 13 < u τ 1 then 3
  else if u τ 1 < u τ 4 then 2
  else if u τ 1 < u τ 2 then 4
  else if u τ 1 < u τ 3 then 5
  else 0

/-! ### The index of each rooting -/

private lemma five_code0_0 (τ : SpeciesTree (Fin 5)) (h : τ.clusters = hierarchyOf ∅) :
    five_code0 τ = 0 := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_0_0 τ h
  have f1 : u τ 1 = u τ 13 := by rw [h1, h13]
  have f2 : u τ 1 = u τ 4 := by rw [h1, h4]
  have f3 : u τ 1 = u τ 2 := by rw [h1, h2]
  have f4 : u τ 1 = u τ 3 := by rw [h1, h3]
  rw [five_code0, ite_eq_right f1.not_lt, ite_eq_right f1.not_gt, ite_eq_right f2.not_lt,
    ite_eq_right f3.not_lt, ite_eq_right f4.not_lt]

private lemma five_code0_1 (τ : SpeciesTree (Fin 5)) (h : τ.clusters = hierarchyOf {{1, 2, 3, 4}}) :
    five_code0 τ = 1 := by
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_0_1 τ h
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {1, 2, 3, 4}) (by rw [h]; decide) (by decide)
  have k := pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)
  have f : u τ 1 < u τ 13 := by rw [h1, h13]; linarith
  rw [five_code0, ite_eq_left f]

private lemma five_code0_2 (τ : SpeciesTree (Fin 5)) (h : τ.clusters = hierarchyOf {{0, 2, 3, 4}}) :
    five_code0 τ = 2 := by
  obtain ⟨h1, -, -, h4, -, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_0_2 τ h
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {0, 2, 3, 4}) (by rw [h]; decide) (by decide)
  have k := pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)
  have f1 : u τ 1 = u τ 13 := by rw [h1, h13]
  have f2 : u τ 1 < u τ 4 := by rw [h1, h4]; linarith
  rw [five_code0, ite_eq_right f1.not_lt, ite_eq_right f1.not_gt, ite_eq_left f2]

private lemma five_code0_3 (τ : SpeciesTree (Fin 5)) (h : τ.clusters = hierarchyOf {{0, 1, 3, 4}}) :
    five_code0 τ = 3 := by
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_0_3 τ h
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {0, 1, 3, 4}) (by rw [h]; decide) (by decide)
  have k := pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)
  have f : u τ 13 < u τ 1 := by rw [h1, h13]; linarith
  rw [five_code0, ite_eq_right (lt_asymm f), ite_eq_left f]

private lemma five_code0_4 (τ : SpeciesTree (Fin 5)) (h : τ.clusters = hierarchyOf {{0, 1, 2, 4}}) :
    five_code0 τ = 4 := by
  obtain ⟨h1, h2, -, h4, -, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_0_4 τ h
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {0, 1, 2, 4}) (by rw [h]; decide) (by decide)
  have k := pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)
  have f1 : u τ 1 = u τ 13 := by rw [h1, h13]
  have f2 : u τ 1 = u τ 4 := by rw [h1, h4]
  have f3 : u τ 1 < u τ 2 := by rw [h1, h2]; linarith
  rw [five_code0, ite_eq_right f1.not_lt, ite_eq_right f1.not_gt, ite_eq_right f2.not_lt,
    ite_eq_left f3]

private lemma five_code0_5 (τ : SpeciesTree (Fin 5)) (h : τ.clusters = hierarchyOf {{0, 1, 2, 3}}) :
    five_code0 τ = 5 := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -, -, -, -, -, h13, -⟩ := rootingDist5_0_5 τ h
  obtain ⟨c0, c1⟩ := five_exp_bounds τ (A := {0, 1, 2, 3}) (by rw [h]; decide) (by decide)
  have k := pow_lt_one₀ c0.le c1 (by decide : (6 : ℕ) ≠ 0)
  have f1 : u τ 1 = u τ 13 := by rw [h1, h13]
  have f2 : u τ 1 = u τ 4 := by rw [h1, h4]
  have f3 : u τ 1 = u τ 2 := by rw [h1, h2]
  have f4 : u τ 1 < u τ 3 := by rw [h1, h3]; linarith
  rw [five_code0, ite_eq_right f1.not_lt, ite_eq_right f1.not_gt, ite_eq_right f2.not_lt,
    ite_eq_right f3.not_lt, ite_eq_left f4]

/-- The hierarchy of a rooting of `U5 0` is the one at position `five_code0 τ`. -/
private lemma five_R0_code0 (τ : SpeciesTree (Fin 5)) (hR : τ.clusters ∈ rootings5 0) :
    τ.clusters = five_R0 (five_code0 τ) := by
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h
  · rw [five_code0_0 τ h]; exact h
  · rw [five_code0_1 τ h]; exact h
  · rw [five_code0_2 τ h]; exact h
  · rw [five_code0_3 τ h]; exact h
  · rw [five_code0_4 τ h]; exact h
  · rw [five_code0_5 τ h]; exact h

/-! ### The lengths of the edges of each rooting -/

section Lengths

variable {τ τ' : SpeciesTree (Fin 5)} (hu : u τ = u τ')
include hu

omit hu in
private lemma five_same0_0 (h : τ.clusters = hierarchyOf ∅) (h' : τ'.clusters = hierarchyOf ∅) :
    τ.SameRootedMetricTree τ' :=
  five_sameRootedMetricTree_of_lengths h h' (by simp)

private lemma five_same0_1 (h : τ.clusters = hierarchyOf {{1, 2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{1, 2, 3, 4}}) : τ.SameRootedMetricTree τ' := by
  obtain ⟨f, -⟩ := rootingDist5_0_1 τ h
  obtain ⟨f', -⟩ := rootingDist5_0_1 τ' h'
  have l : τ.length {1, 2, 3, 4} = τ'.length {1, 2, 3, 4} :=
    five_length_eq (n := 6) (v := u τ' 1) (A := 1 / 90) (B := 1 / 18) (by decide) (by norm_num)
      (by rw [← hu, f]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_singleton, forall_eq]
  exact l

private lemma five_same0_2 (h : τ.clusters = hierarchyOf {{0, 2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 2, 3, 4}}) : τ.SameRootedMetricTree τ' := by
  obtain ⟨f, -⟩ := rootingDist5_0_2 τ h
  obtain ⟨f', -⟩ := rootingDist5_0_2 τ' h'
  have l : τ.length {0, 2, 3, 4} = τ'.length {0, 2, 3, 4} :=
    five_length_eq (n := 6) (v := u τ' 1) (A := 1 / 90) (B := 1 / 18) (by decide) (by norm_num)
      (by rw [← hu, f]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_singleton, forall_eq]
  exact l

private lemma five_same0_3 (h : τ.clusters = hierarchyOf {{0, 1, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1, 3, 4}}) : τ.SameRootedMetricTree τ' := by
  obtain ⟨-, f, -⟩ := rootingDist5_0_3 τ h
  obtain ⟨-, f', -⟩ := rootingDist5_0_3 τ' h'
  have l : τ.length {0, 1, 3, 4} = τ'.length {0, 1, 3, 4} :=
    five_length_eq (n := 6) (v := u τ' 2) (A := 1 / 90) (B := 1 / 18) (by decide) (by norm_num)
      (by rw [← hu, f]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_singleton, forall_eq]
  exact l

private lemma five_same0_4 (h : τ.clusters = hierarchyOf {{0, 1, 2, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1, 2, 4}}) : τ.SameRootedMetricTree τ' := by
  obtain ⟨f, -⟩ := rootingDist5_0_4 τ h
  obtain ⟨f', -⟩ := rootingDist5_0_4 τ' h'
  have l : τ.length {0, 1, 2, 4} = τ'.length {0, 1, 2, 4} :=
    five_length_eq (n := 6) (v := u τ' 1) (A := 1 / 90) (B := 1 / 18) (by decide) (by norm_num)
      (by rw [← hu, f]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_singleton, forall_eq]
  exact l

private lemma five_same0_5 (h : τ.clusters = hierarchyOf {{0, 1, 2, 3}})
    (h' : τ'.clusters = hierarchyOf {{0, 1, 2, 3}}) : τ.SameRootedMetricTree τ' := by
  obtain ⟨f, -⟩ := rootingDist5_0_5 τ h
  obtain ⟨f', -⟩ := rootingDist5_0_5 τ' h'
  have l : τ.length {0, 1, 2, 3} = τ'.length {0, 1, 2, 3} :=
    five_length_eq (n := 6) (v := u τ' 1) (A := 1 / 90) (B := 1 / 18) (by decide) (by norm_num)
      (by rw [← hu, f]) (by rw [f'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_singleton, forall_eq]
  exact l

end Lengths

/-- Two rootings of the star `U5 0` with the same unrooted gene tree probabilities have the same
rooted metric tree. -/
theorem five_sameRootedMetricTree_zero (τ τ' : SpeciesTree (Fin 5))
    (hR : τ.clusters ∈ rootings5 0) (hR' : τ'.clusters ∈ rootings5 0) (hu : u τ = u τ') :
    τ.SameRootedMetricTree τ' := by
  have hcode : five_code0 τ = five_code0 τ' := by
    unfold five_code0
    rw [hu]
  have hc : τ'.clusters = τ.clusters := by
    rw [five_R0_code0 τ' hR', ← hcode, ← five_R0_code0 τ hR]
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h
  · exact five_same0_0 h (hc.trans h)
  · exact five_same0_1 hu h (hc.trans h)
  · exact five_same0_2 hu h (hc.trans h)
  · exact five_same0_3 hu h (hc.trans h)
  · exact five_same0_4 hu h (hc.trans h)
  · exact five_same0_5 hu h (hc.trans h)

end ADR11
