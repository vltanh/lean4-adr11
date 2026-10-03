module

public import ADR11.Identifiability.FiveTaxa.Classes
public import ADR11.Identifiability.FiveTaxa.Common
public import ADR11.Nonbinary.AppendixC

/-!
# Appendix C: the classes of gene trees of the rootings of `U5 0` and `U5 1`

The proof of Proposition 11 (Appendix C of the paper) reads the shape and the labelling of a
nonbinary 5-taxon species tree off its classes of equiprobable gene trees: the least probable class
`𝒞`, the class with the second smallest probability, and the most probable gene trees. This module
computes these classes, from the gene tree distributions of Table 7 (`rootingDist5_k_j`, the
formulas of Table 7 for each labelling), for the rootings of the star `U5 0` and of `U5 1 = AB|CDE`
(`ADR11.rootings5 0`, `ADR11.rootings5 1`), and for the representatives `P₂`, `P₃` of Table 6.

## Main results

* `ac1_leastClass_eq`, `ac1_secondClass_eq`, `ac1_mostProbable_eq`, `ac1_classes_two`: the
  classes of a distribution that takes one value on a set of gene trees and larger (smaller)
  values elsewhere.
* `ac1_classes_0_j` (`j = 0, …, 5`) and `ac1_classes_1_j` (`j = 0, …, 7`): the least probable
  class of the `j`-th rooting of `U5 0` (resp. `U5 1`), with the class of the second smallest
  probability or the most probable gene tree where Appendix C uses them.
* `ac1_classes_P2`, `ac1_classes_P3`: the same for the representatives `P₂ = (a,b,c,(d,e))` and
  `P₃ = ((a,b,c,d),e)`, from Table 7.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-! ### The classes of a distribution with a given least (or greatest) value -/

/-- If `u τ` takes the value `v` on a nonempty set `S` of gene trees and larger values on the other
gene trees, then `S` is the least probable class. -/
theorem ac1_leastClass_eq {τ : SpeciesTree (Fin 5)} (S : Finset ℕ) (v : ℝ) (hS : S ⊆ Icc 1 15)
    (hne : S.Nonempty) (hu : ∀ i ∈ Icc 1 15, (i ∈ S → u τ i = v) ∧ (i ∉ S → v < u τ i)) :
    cls_leastClass τ = S := by
  ext i
  rw [cls_mem_leastClass]
  constructor
  · rintro ⟨hi, hmin⟩
    by_contra hiS
    obtain ⟨j, hj⟩ := hne
    have h1 := hmin j (hS hj)
    rw [(hu j (hS hj)).1 hj] at h1
    exact absurd ((hu i hi).2 hiS) (not_lt.2 h1)
  · intro hiS
    refine ⟨hS hiS, fun j hj => ?_⟩
    rw [(hu i (hS hiS)).1 hiS]
    by_cases hjS : j ∈ S
    · rw [(hu j hj).1 hjS]
    · exact ((hu j hj).2 hjS).le

/-- If the least probable class is `S₁`, and `u τ` takes the value `w` on a nonempty set `S₂` of
gene trees outside `S₁` and larger values on the gene trees outside `S₁ ∪ S₂`, then `S₂` is the
class with the second smallest probability. -/
theorem ac1_secondClass_eq {τ : SpeciesTree (Fin 5)} {S₁ : Finset ℕ} (h₁ : cls_leastClass τ = S₁)
    (S₂ : Finset ℕ) (w : ℝ) (hS₂ : S₂ ⊆ Icc 1 15) (hd : Disjoint S₁ S₂) (hne : S₂.Nonempty)
    (hu : ∀ i ∈ Icc 1 15, (i ∈ S₂ → u τ i = w) ∧ (i ∉ S₁ → i ∉ S₂ → w < u τ i)) :
    cls_secondClass τ = S₂ := by
  ext i
  rw [cls_mem_secondClass, h₁]
  constructor
  · rintro ⟨hi, hi₁, hmin⟩
    by_contra hiS
    obtain ⟨j, hj⟩ := hne
    have h1 := hmin j (hS₂ hj) (disjoint_right.1 hd hj)
    rw [(hu j (hS₂ hj)).1 hj] at h1
    exact absurd ((hu i hi).2 hi₁ hiS) (not_lt.2 h1)
  · intro hiS
    refine ⟨hS₂ hiS, disjoint_right.1 hd hiS, fun j hj hj₁ => ?_⟩
    rw [(hu i (hS₂ hiS)).1 hiS]
    by_cases hjS : j ∈ S₂
    · rw [(hu j hj).1 hjS]
    · exact ((hu j hj).2 hj₁ hjS).le

/-- If `u τ` takes the value `m` on a nonempty set `S` of gene trees and smaller values on the
other gene trees, then `S` is the set of the most probable gene trees. -/
theorem ac1_mostProbable_eq {τ : SpeciesTree (Fin 5)} (S : Finset ℕ) (m : ℝ) (hS : S ⊆ Icc 1 15)
    (hne : S.Nonempty) (hu : ∀ i ∈ Icc 1 15, (i ∈ S → u τ i = m) ∧ (i ∉ S → u τ i < m)) :
    cls_mostProbable τ = S := by
  ext i
  rw [cls_mem_mostProbable]
  constructor
  · rintro ⟨hi, hmax⟩
    by_contra hiS
    obtain ⟨j, hj⟩ := hne
    have h1 := hmax j (hS hj)
    rw [(hu j (hS hj)).1 hj] at h1
    exact absurd ((hu i hi).2 hiS) (not_lt.2 h1)
  · intro hiS
    refine ⟨hS hiS, fun j hj => ?_⟩
    rw [(hu i (hS hiS)).1 hiS]
    by_cases hjS : j ∈ S
    · rw [(hu j hj).1 hjS]
    · exact ((hu j hj).2 hjS).le

/-- A distribution with two classes: if `u τ` takes the value `a` on a nonempty set `C` of gene
trees and a smaller value `b` on the others (at least one), then the least probable class is the
complement of `C`, and `C` is the class with the second smallest probability. -/
theorem ac1_classes_two {τ : SpeciesTree (Fin 5)} (C : Finset ℕ) (a b : ℝ) (hC : C ⊆ Icc 1 15)
    (hne : C.Nonempty) (hne' : (Icc 1 15 \ C).Nonempty)
    (hu : ∀ i ∈ Icc 1 15, u τ i = if i ∈ C then a else b) (hba : b < a) :
    cls_leastClass τ = Icc 1 15 \ C ∧ cls_secondClass τ = C := by
  have h₁ : cls_leastClass τ = Icc 1 15 \ C := by
    refine ac1_leastClass_eq _ b sdiff_subset hne' fun i hi => ⟨fun h => ?_, fun h => ?_⟩
    · rw [hu i hi, ite_eq_right (mem_sdiff.1 h).2]
    · have hiC : i ∈ C := by
        by_contra hiC
        exact h (mem_sdiff.2 ⟨hi, hiC⟩)
      rw [hu i hi, ite_eq_left hiC]
      exact hba
  refine ⟨h₁, ac1_secondClass_eq h₁ C a hC sdiff_disjoint hne fun i hi => ⟨fun h => ?_, ?_⟩⟩
  · rw [hu i hi, ite_eq_left h]
  · intro h1 h2
    exact absurd (mem_sdiff.2 ⟨hi, h2⟩) h1

/-! ### The rootings of `U5 0` and `U5 1` -/

/-- The classes of gene trees of the rooting `hierarchyOf ∅` of `U5 0`
(`P₁ = (a,b,c,d,e)`), read off its gene tree distribution `rootingDist5_0_0`. -/
theorem ac1_classes_0_0 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf ∅) :
    cls_leastClass τ = Icc 1 15 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_0_0 τ h
  exact ac1_leastClass_eq (Icc 1 15) (1 / 15) subset_rfl ⟨1, by decide⟩ (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)

/-- The classes of gene trees of the rooting `hierarchyOf {{1, 2, 3, 4}}` of `U5 0`
(`P₃ = ((b,c,d,e),a)`), read off its gene tree distribution `rootingDist5_0_1`. -/
theorem ac1_classes_0_1 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{1, 2, 3, 4}}) :
    cls_leastClass τ = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} ∧
      cls_secondClass τ = {13, 14, 15} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_0_1 τ h
  obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {1, 2, 3, 4}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {1, 2, 3, 4}) = Z at *
  have f : Z ^ 6 < 1 := pow_lt_one₀ z0.le z1 (by norm_num)
  have i_ba : 1 / 90 * Z ^ 6 + 1 / 18 <
      -2 / 45 * Z ^ 6 + 1 / 9 := by
    linarith only [f]
  clear f
  generalize 1 / 90 * Z ^ 6 + 1 / 18 = b at *
  generalize -2 / 45 * Z ^ 6 + 1 / 9 = a at *
  have hC := ac1_leastClass_eq (τ := τ) {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} b
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  refine ⟨hC, ac1_secondClass_eq hC {13, 14, 15} a (by decide) (by decide) (by decide)
    (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> refine ⟨fun hm => ?_, fun hn hm => ?_⟩ <;>
      first | exact absurd hm (by decide) | exact absurd hn (by decide) | linarith)⟩

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 2, 3, 4}}` of `U5 0`
(`P₃ = ((a,c,d,e),b)`), read off its gene tree distribution `rootingDist5_0_2`. -/
theorem ac1_classes_0_2 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 2, 3, 4}}) :
    cls_leastClass τ = {1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15} ∧
      cls_secondClass τ = {4, 7, 10} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_0_2 τ h
  obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {0, 2, 3, 4}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {0, 2, 3, 4}) = Z at *
  have f : Z ^ 6 < 1 := pow_lt_one₀ z0.le z1 (by norm_num)
  have i_ba : 1 / 90 * Z ^ 6 + 1 / 18 <
      -2 / 45 * Z ^ 6 + 1 / 9 := by
    linarith only [f]
  clear f
  generalize 1 / 90 * Z ^ 6 + 1 / 18 = b at *
  generalize -2 / 45 * Z ^ 6 + 1 / 9 = a at *
  have hC := ac1_leastClass_eq (τ := τ) {1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15} b
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  refine ⟨hC, ac1_secondClass_eq hC {4, 7, 10} a (by decide) (by decide) (by decide)
    (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> refine ⟨fun hm => ?_, fun hn hm => ?_⟩ <;>
      first | exact absurd hm (by decide) | exact absurd hn (by decide) | linarith)⟩

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1, 3, 4}}` of `U5 0`
(`P₃ = ((a,b,d,e),c)`), read off its gene tree distribution `rootingDist5_0_3`. -/
theorem ac1_classes_0_3 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1, 3, 4}}) :
    cls_leastClass τ = {2, 3, 4, 5, 6, 7, 9, 10, 12, 13, 14, 15} ∧
      cls_secondClass τ = {1, 8, 11} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_0_3 τ h
  obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {0, 1, 3, 4}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {0, 1, 3, 4}) = Z at *
  have f : Z ^ 6 < 1 := pow_lt_one₀ z0.le z1 (by norm_num)
  have i_ba : 1 / 90 * Z ^ 6 + 1 / 18 <
      -2 / 45 * Z ^ 6 + 1 / 9 := by
    linarith only [f]
  clear f
  generalize -2 / 45 * Z ^ 6 + 1 / 9 = a at *
  generalize 1 / 90 * Z ^ 6 + 1 / 18 = b at *
  have hC := ac1_leastClass_eq (τ := τ) {2, 3, 4, 5, 6, 7, 9, 10, 12, 13, 14, 15} b
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  refine ⟨hC, ac1_secondClass_eq hC {1, 8, 11} a (by decide) (by decide) (by decide)
    (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> refine ⟨fun hm => ?_, fun hn hm => ?_⟩ <;>
      first | exact absurd hm (by decide) | exact absurd hn (by decide) | linarith)⟩

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1, 2, 4}}` of `U5 0`
(`P₃ = ((a,b,c,e),d)`), read off its gene tree distribution `rootingDist5_0_4`. -/
theorem ac1_classes_0_4 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1, 2, 4}}) :
    cls_leastClass τ = {1, 3, 4, 6, 7, 8, 9, 10, 11, 13, 14, 15} ∧
      cls_secondClass τ = {2, 5, 12} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_0_4 τ h
  obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {0, 1, 2, 4}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {0, 1, 2, 4}) = Z at *
  have f : Z ^ 6 < 1 := pow_lt_one₀ z0.le z1 (by norm_num)
  have i_ba : 1 / 90 * Z ^ 6 + 1 / 18 <
      -2 / 45 * Z ^ 6 + 1 / 9 := by
    linarith only [f]
  clear f
  generalize 1 / 90 * Z ^ 6 + 1 / 18 = b at *
  generalize -2 / 45 * Z ^ 6 + 1 / 9 = a at *
  have hC := ac1_leastClass_eq (τ := τ) {1, 3, 4, 6, 7, 8, 9, 10, 11, 13, 14, 15} b
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  refine ⟨hC, ac1_secondClass_eq hC {2, 5, 12} a (by decide) (by decide) (by decide)
    (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> refine ⟨fun hm => ?_, fun hn hm => ?_⟩ <;>
      first | exact absurd hm (by decide) | exact absurd hn (by decide) | linarith)⟩

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1, 2, 3}}` of `U5 0`
(`P₃ = ((a,b,c,d),e)`), read off its gene tree distribution `rootingDist5_0_5`. -/
theorem ac1_classes_0_5 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1, 2, 3}}) :
    cls_leastClass τ = {1, 2, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15} ∧
      cls_secondClass τ = {3, 6, 9} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_0_5 τ h
  obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {0, 1, 2, 3}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {0, 1, 2, 3}) = Z at *
  have f : Z ^ 6 < 1 := pow_lt_one₀ z0.le z1 (by norm_num)
  have i_ba : 1 / 90 * Z ^ 6 + 1 / 18 <
      -2 / 45 * Z ^ 6 + 1 / 9 := by
    linarith only [f]
  clear f
  generalize 1 / 90 * Z ^ 6 + 1 / 18 = b at *
  generalize -2 / 45 * Z ^ 6 + 1 / 9 = a at *
  have hC := ac1_leastClass_eq (τ := τ) {1, 2, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15} b
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  refine ⟨hC, ac1_secondClass_eq hC {3, 6, 9} a (by decide) (by decide) (by decide)
    (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> refine ⟨fun hm => ?_, fun hn hm => ?_⟩ <;>
      first | exact absurd hm (by decide) | exact absurd hn (by decide) | linarith)⟩

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1}}` of `U5 1`
(`P₂ = ((a,b),c,d,e)`), read off its gene tree distribution `rootingDist5_1_0`. -/
theorem ac1_classes_1_0 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}}) :
    cls_leastClass τ = {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_1_0 τ h
  obtain ⟨x0, x1⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {0, 1}) = X at *
  have i_vt : 1 / 15 * X <
      -4 / 15 * X + 1 / 3 := by
    linarith only [x1]
  generalize -4 / 15 * X + 1 / 3 = t at *
  generalize 1 / 15 * X = v at *
  have hC := ac1_leastClass_eq (τ := τ) {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} v
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  exact hC

/-- The classes of gene trees of the rooting `hierarchyOf {{2, 3, 4}}` of `U5 1`
(`P₄ = ((c,d,e),a,b)`), read off its gene tree distribution `rootingDist5_1_1`. -/
theorem ac1_classes_1_1 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {4, 7, 10, 13, 14, 15} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_1_1 τ h
  obtain ⟨y0, y1⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {2, 3, 4}) = Y at *
  have f1 : 0 < Y * ((1 - Y) * (1 + Y)) :=
    mul_pos y0 (mul_pos (sub_pos.2 y1) (by linarith only [y0]))
  have f2 : 0 < (1 - Y) ^ 2 * (2 + Y) := mul_pos (pow_pos (sub_pos.2 y1) 2) (by linarith only [y0])
  have i_vw : 1 / 15 * Y ^ 3 <
      -1 / 10 * Y ^ 3 + 1 / 6 * Y := by
    linarith only [y1, f1, f2]
  have i_vt : 1 / 15 * Y ^ 3 <
      1 / 15 * Y ^ 3 - 1 / 3 * Y + 1 / 3 := by
    linarith only [y1, f1, f2]
  have i_wt : -1 / 10 * Y ^ 3 + 1 / 6 * Y <
      1 / 15 * Y ^ 3 - 1 / 3 * Y + 1 / 3 := by
    linarith only [y1, f1, f2]
  clear f1 f2
  generalize 1 / 15 * Y ^ 3 - 1 / 3 * Y + 1 / 3 = t at *
  generalize -1 / 10 * Y ^ 3 + 1 / 6 * Y = w at *
  generalize 1 / 15 * Y ^ 3 = v at *
  have hC := ac1_leastClass_eq (τ := τ) {5, 6, 8, 9, 11, 12} v
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  refine ⟨hC, ac1_secondClass_eq hC {4, 7, 10, 13, 14, 15} w (by decide) (by decide) (by decide)
    (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> refine ⟨fun hm => ?_, fun hn hm => ?_⟩ <;>
      first | exact absurd hm (by decide) | exact absurd hn (by decide) | linarith)⟩

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1}, {2, 3, 4}}` of `U5 1`
(`P₈ = ((a,b),(c,d,e))`), read off its gene tree distribution `rootingDist5_1_2`. -/
theorem ac1_classes_1_2 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {4, 7, 10, 13, 14, 15} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_1_2 τ h
  obtain ⟨x0, x1⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨y0, y1⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {0, 1}) = X at *
  generalize exp (-τ.length {2, 3, 4}) = Y at *
  have f1 : 0 < X * (Y * ((1 - Y) * (1 + Y))) :=
    mul_pos x0 (mul_pos y0 (mul_pos (sub_pos.2 y1) (by linarith only [y0])))
  have f2 : 0 < (1 - Y) ^ 2 * (2 + Y) + (1 - X) * (Y * (3 - Y ^ 2)) :=
    add_pos (mul_pos (pow_pos (sub_pos.2 y1) 2) (by linarith only [y0]))
      (mul_pos (sub_pos.2 x1) (mul_pos y0 (by nlinarith only [y0, y1])))
  have f3 : X * Y < 1 := by nlinarith only [x0, x1, y0, y1]
  have i_vw : 1 / 15 * X * Y ^ 3 <
      -1 / 10 * X * Y ^ 3 + 1 / 6 * X * Y := by
    linarith only [f1, f2, f3]
  have i_vt : 1 / 15 * X * Y ^ 3 <
      1 / 15 * X * Y ^ 3 - 1 / 3 * X * Y + 1 / 3 := by
    linarith only [f1, f2, f3]
  have i_wt : -1 / 10 * X * Y ^ 3 + 1 / 6 * X * Y <
      1 / 15 * X * Y ^ 3 - 1 / 3 * X * Y + 1 / 3 := by
    linarith only [f1, f2, f3]
  clear f1 f2 f3
  generalize 1 / 15 * X * Y ^ 3 - 1 / 3 * X * Y + 1 / 3 = t at *
  generalize -1 / 10 * X * Y ^ 3 + 1 / 6 * X * Y = w at *
  generalize 1 / 15 * X * Y ^ 3 = v at *
  have hC := ac1_leastClass_eq (τ := τ) {5, 6, 8, 9, 11, 12} v
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  refine ⟨hC, ac1_secondClass_eq hC {4, 7, 10, 13, 14, 15} w (by decide) (by decide) (by decide)
    (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> refine ⟨fun hm => ?_, fun hn hm => ?_⟩ <;>
      first | exact absurd hm (by decide) | exact absurd hn (by decide) | linarith)⟩

/-- The classes of gene trees of the rooting `hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}` of `U5 1`
(`P₉ = (((c,d,e),b),a)`), read off its gene tree distribution `rootingDist5_1_3`. -/
theorem ac1_classes_1_3 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {4, 7, 10} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_1_3 τ h
  obtain ⟨y0, y1⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
  obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {1, 2, 3, 4}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {2, 3, 4}) = Y at *
  generalize exp (-τ.length {1, 2, 3, 4}) = Z at *
  have f1 : 0 < Y * ((1 - Y) * (1 + Y)) :=
    mul_pos y0 (mul_pos (sub_pos.2 y1) (by linarith only [y0]))
  have f2 : 0 < (1 - Y) ^ 2 * (2 + Y) := mul_pos (pow_pos (sub_pos.2 y1) 2) (by linarith only [y0])
  have f3 : Y ^ 3 * Z ^ 6 < Y ^ 3 :=
    mul_lt_of_lt_one_right (pow_pos y0 3) (pow_lt_one₀ z0.le z1 (by norm_num))
  have i_vw : 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 <
      1 / 90 * Y ^ 3 * Z ^ 6 - 1 / 9 * Y ^ 3 + 1 / 6 * Y := by
    linarith only [y1, f1, f2, f3]
  have i_vs : 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 <
      -2 / 45 * Y ^ 3 * Z ^ 6 - 1 / 18 * Y ^ 3 + 1 / 6 * Y := by
    linarith only [y1, f1, f2, f3]
  have i_vt : 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 <
      1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 - 1 / 3 * Y + 1 / 3 := by
    linarith only [y1, f1, f2, f3]
  have i_wt : 1 / 90 * Y ^ 3 * Z ^ 6 - 1 / 9 * Y ^ 3 + 1 / 6 * Y <
      1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 - 1 / 3 * Y + 1 / 3 := by
    linarith only [y1, f1, f2, f3]
  have i_ws : 1 / 90 * Y ^ 3 * Z ^ 6 - 1 / 9 * Y ^ 3 + 1 / 6 * Y <
      -2 / 45 * Y ^ 3 * Z ^ 6 - 1 / 18 * Y ^ 3 + 1 / 6 * Y := by
    linarith only [y1, f1, f2, f3]
  clear f1 f2 f3
  generalize 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 - 1 / 3 * Y + 1 / 3 = t at *
  generalize -2 / 45 * Y ^ 3 * Z ^ 6 - 1 / 18 * Y ^ 3 + 1 / 6 * Y = s at *
  generalize 1 / 90 * Y ^ 3 * Z ^ 6 - 1 / 9 * Y ^ 3 + 1 / 6 * Y = w at *
  generalize 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 = v at *
  have hC := ac1_leastClass_eq (τ := τ) {5, 6, 8, 9, 11, 12} v
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  refine ⟨hC, ac1_secondClass_eq hC {4, 7, 10} w (by decide) (by decide) (by decide)
    (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> refine ⟨fun hm => ?_, fun hn hm => ?_⟩ <;>
      first | exact absurd hm (by decide) | exact absurd hn (by decide) | linarith)⟩

/-- The classes of gene trees of the rooting `hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}}` of `U5 1`
(`P₉ = (((c,d,e),a),b)`), read off its gene tree distribution `rootingDist5_1_4`. -/
theorem ac1_classes_1_4 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {13, 14, 15} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_1_4 τ h
  obtain ⟨y0, y1⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
  obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {0, 2, 3, 4}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {2, 3, 4}) = Y at *
  generalize exp (-τ.length {0, 2, 3, 4}) = Z at *
  have f1 : 0 < Y * ((1 - Y) * (1 + Y)) :=
    mul_pos y0 (mul_pos (sub_pos.2 y1) (by linarith only [y0]))
  have f2 : 0 < (1 - Y) ^ 2 * (2 + Y) := mul_pos (pow_pos (sub_pos.2 y1) 2) (by linarith only [y0])
  have f3 : Y ^ 3 * Z ^ 6 < Y ^ 3 :=
    mul_lt_of_lt_one_right (pow_pos y0 3) (pow_lt_one₀ z0.le z1 (by norm_num))
  have i_vw : 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 <
      1 / 90 * Y ^ 3 * Z ^ 6 - 1 / 9 * Y ^ 3 + 1 / 6 * Y := by
    linarith only [y1, f1, f2, f3]
  have i_vs : 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 <
      -2 / 45 * Y ^ 3 * Z ^ 6 - 1 / 18 * Y ^ 3 + 1 / 6 * Y := by
    linarith only [y1, f1, f2, f3]
  have i_vt : 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 <
      1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 - 1 / 3 * Y + 1 / 3 := by
    linarith only [y1, f1, f2, f3]
  have i_wt : 1 / 90 * Y ^ 3 * Z ^ 6 - 1 / 9 * Y ^ 3 + 1 / 6 * Y <
      1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 - 1 / 3 * Y + 1 / 3 := by
    linarith only [y1, f1, f2, f3]
  have i_ws : 1 / 90 * Y ^ 3 * Z ^ 6 - 1 / 9 * Y ^ 3 + 1 / 6 * Y <
      -2 / 45 * Y ^ 3 * Z ^ 6 - 1 / 18 * Y ^ 3 + 1 / 6 * Y := by
    linarith only [y1, f1, f2, f3]
  clear f1 f2 f3
  generalize 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 - 1 / 3 * Y + 1 / 3 = t at *
  generalize -2 / 45 * Y ^ 3 * Z ^ 6 - 1 / 18 * Y ^ 3 + 1 / 6 * Y = s at *
  generalize 1 / 90 * Y ^ 3 * Z ^ 6 - 1 / 9 * Y ^ 3 + 1 / 6 * Y = w at *
  generalize 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 = v at *
  have hC := ac1_leastClass_eq (τ := τ) {5, 6, 8, 9, 11, 12} v
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  refine ⟨hC, ac1_secondClass_eq hC {13, 14, 15} w (by decide) (by decide) (by decide)
    (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> refine ⟨fun hm => ?_, fun hn hm => ?_⟩ <;>
      first | exact absurd hm (by decide) | exact absurd hn (by decide) | linarith)⟩

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1}, {0, 1, 3, 4}}` of `U5 1`
(`P₇ = (((a,b),d,e),c)`), read off its gene tree distribution `rootingDist5_1_5`. -/
theorem ac1_classes_1_5 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 3, 4}}) :
    cls_leastClass τ = {4, 5, 6, 7, 9, 10, 12, 13, 14, 15} ∧
      cls_mostProbable τ = {1} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_1_5 τ h
  obtain ⟨x0, x1⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {0, 1, 3, 4}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {0, 1}) = X at *
  generalize exp (-τ.length {0, 1, 3, 4}) = Z at *
  have f : X * Z ^ 6 < X := mul_lt_of_lt_one_right x0 (pow_lt_one₀ z0.le z1 (by norm_num))
  have i_vp : 1 / 90 * X * Z ^ 6 + 1 / 18 * X <
      1 / 90 * X * Z ^ 6 - 5 / 18 * X + 1 / 3 := by
    linarith only [x1, f]
  have i_vq : 1 / 90 * X * Z ^ 6 + 1 / 18 * X <
      -2 / 45 * X * Z ^ 6 + 1 / 9 * X := by
    linarith only [x1, f]
  have i_vm : 1 / 90 * X * Z ^ 6 + 1 / 18 * X <
      -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 := by
    linarith only [x1, f]
  have i_pm : 1 / 90 * X * Z ^ 6 - 5 / 18 * X + 1 / 3 <
      -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 := by
    linarith only [x1, f]
  have i_qm : -2 / 45 * X * Z ^ 6 + 1 / 9 * X <
      -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 := by
    linarith only [x1, f]
  clear f
  generalize -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 = m at *
  generalize 1 / 90 * X * Z ^ 6 - 5 / 18 * X + 1 / 3 = p at *
  generalize 1 / 90 * X * Z ^ 6 + 1 / 18 * X = v at *
  generalize -2 / 45 * X * Z ^ 6 + 1 / 9 * X = q at *
  have hC := ac1_leastClass_eq (τ := τ) {4, 5, 6, 7, 9, 10, 12, 13, 14, 15} v
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  refine ⟨hC, ac1_mostProbable_eq {1} m (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)⟩

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1}, {0, 1, 2, 4}}` of `U5 1`
(`P₇ = (((a,b),c,e),d)`), read off its gene tree distribution `rootingDist5_1_6`. -/
theorem ac1_classes_1_6 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 4}}) :
    cls_leastClass τ = {4, 6, 7, 8, 9, 10, 11, 13, 14, 15} ∧
      cls_mostProbable τ = {2} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_1_6 τ h
  obtain ⟨x0, x1⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {0, 1, 2, 4}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {0, 1}) = X at *
  generalize exp (-τ.length {0, 1, 2, 4}) = Z at *
  have f : X * Z ^ 6 < X := mul_lt_of_lt_one_right x0 (pow_lt_one₀ z0.le z1 (by norm_num))
  have i_vp : 1 / 90 * X * Z ^ 6 + 1 / 18 * X <
      1 / 90 * X * Z ^ 6 - 5 / 18 * X + 1 / 3 := by
    linarith only [x1, f]
  have i_vq : 1 / 90 * X * Z ^ 6 + 1 / 18 * X <
      -2 / 45 * X * Z ^ 6 + 1 / 9 * X := by
    linarith only [x1, f]
  have i_vm : 1 / 90 * X * Z ^ 6 + 1 / 18 * X <
      -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 := by
    linarith only [x1, f]
  have i_pm : 1 / 90 * X * Z ^ 6 - 5 / 18 * X + 1 / 3 <
      -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 := by
    linarith only [x1, f]
  have i_qm : -2 / 45 * X * Z ^ 6 + 1 / 9 * X <
      -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 := by
    linarith only [x1, f]
  clear f
  generalize 1 / 90 * X * Z ^ 6 - 5 / 18 * X + 1 / 3 = p at *
  generalize -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 = m at *
  generalize 1 / 90 * X * Z ^ 6 + 1 / 18 * X = v at *
  generalize -2 / 45 * X * Z ^ 6 + 1 / 9 * X = q at *
  have hC := ac1_leastClass_eq (τ := τ) {4, 6, 7, 8, 9, 10, 11, 13, 14, 15} v
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  refine ⟨hC, ac1_mostProbable_eq {2} m (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)⟩

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1}, {0, 1, 2, 3}}` of `U5 1`
(`P₇ = (((a,b),c,d),e)`), read off its gene tree distribution `rootingDist5_1_7`. -/
theorem ac1_classes_1_7 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 3}}) :
    cls_leastClass τ = {4, 5, 7, 8, 10, 11, 12, 13, 14, 15} ∧
      cls_mostProbable τ = {3} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    rootingDist5_1_7 τ h
  obtain ⟨x0, x1⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {0, 1, 2, 3}) (by rw [h]; decide) (by decide)
  generalize exp (-τ.length {0, 1}) = X at *
  generalize exp (-τ.length {0, 1, 2, 3}) = Z at *
  have f : X * Z ^ 6 < X := mul_lt_of_lt_one_right x0 (pow_lt_one₀ z0.le z1 (by norm_num))
  have i_vp : 1 / 90 * X * Z ^ 6 + 1 / 18 * X <
      1 / 90 * X * Z ^ 6 - 5 / 18 * X + 1 / 3 := by
    linarith only [x1, f]
  have i_vq : 1 / 90 * X * Z ^ 6 + 1 / 18 * X <
      -2 / 45 * X * Z ^ 6 + 1 / 9 * X := by
    linarith only [x1, f]
  have i_vm : 1 / 90 * X * Z ^ 6 + 1 / 18 * X <
      -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 := by
    linarith only [x1, f]
  have i_pm : 1 / 90 * X * Z ^ 6 - 5 / 18 * X + 1 / 3 <
      -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 := by
    linarith only [x1, f]
  have i_qm : -2 / 45 * X * Z ^ 6 + 1 / 9 * X <
      -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 := by
    linarith only [x1, f]
  clear f
  generalize 1 / 90 * X * Z ^ 6 - 5 / 18 * X + 1 / 3 = p at *
  generalize -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 = m at *
  generalize 1 / 90 * X * Z ^ 6 + 1 / 18 * X = v at *
  generalize -2 / 45 * X * Z ^ 6 + 1 / 9 * X = q at *
  have hC := ac1_leastClass_eq (τ := τ) {4, 5, 7, 8, 10, 11, 12, 13, 14, 15} v
    (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)
  refine ⟨hC, ac1_mostProbable_eq {3} m (by decide) (by decide) (by
    intro i hi
    rw [mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> constructor <;> intro hm <;>
      first | exact absurd hm (by decide) | linarith)⟩

/-! ### The representatives `P₂` and `P₃` (Table 7) -/

/-- Table 7 for `P₂ = (a,b,c,(d,e):z)`: the least probable class is the complement of
`{T₁, T₄, T₁₃}`, the class with the second smallest probability. -/
theorem ac1_classes_P2 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = polytomy5 2) :
    cls_leastClass σ = Icc 1 15 \ {1, 4, 13} ∧ cls_secondClass σ = {1, 4, 13} := by
  obtain ⟨z0, z1⟩ := five_exp_bounds σ (A := {3, 4}) (by rw [h]; decide) (by decide)
  exact ac1_classes_two {1, 4, 13} (1 / 3 - 4 / 15 * exp (-σ.length {3, 4}))
    (1 / 15 * exp (-σ.length {3, 4})) (by decide) (by decide) (by decide)
    (fun i hi => (table7 σ i hi).2.1 h) (by linarith)

/-- Table 7 for `P₃ = ((a,b,c,d):z,e)`: the least probable class is the complement of
`{T₃, T₆, T₉}`, the class with the second smallest probability. -/
theorem ac1_classes_P3 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = polytomy5 3) :
    cls_leastClass σ = Icc 1 15 \ {3, 6, 9} ∧ cls_secondClass σ = {3, 6, 9} := by
  obtain ⟨z0, z1⟩ := five_exp_bounds σ (A := {0, 1, 2, 3}) (by rw [h]; decide) (by decide)
  have hz : exp (-σ.length {0, 1, 2, 3}) ^ 6 < 1 := pow_lt_one₀ z0.le z1 (by norm_num)
  exact ac1_classes_two {3, 6, 9} (1 / 9 - 2 / 45 * exp (-σ.length {0, 1, 2, 3}) ^ 6)
    (1 / 18 + 1 / 90 * exp (-σ.length {0, 1, 2, 3}) ^ 6) (by decide) (by decide) (by decide)
    (fun i hi => (table7 σ i hi).2.2.1 h) (by linarith)

end ADR11
