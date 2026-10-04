module

public import ADR11.Identifiability.Proposition8
public import ADR11.Nonbinary.FiveTaxa.Shapes

/-!
# Appendix C: the labelling and the lengths for the rootings of `U5 2`

The proof of Proposition 11 (Appendix C of the paper, l. 938–995) for the five-taxon species trees
whose unrooted tree is `U5 2`, with the splits `ab|cde` and `abc|de`. Its ten rootings
(`ADR11.rootings5 2`) are the four caterpillars `((((a,b),c),d),e)`, `((((a,b),c),e),d)`,
`((((d,e),c),b),a)`, `((((d,e),c),a),b)`, the pseudocaterpillar `(((a,b),(d,e)),c)`, the balanced
trees `(((a,b),c),(d,e))` and `((a,b),(c,(d,e)))`, the polytomy `P₅ = ((a,b),(d,e),c)`, and the
two polytomies of shape `P₆`, `(((a,b),c),d,e)` and `(a,b,(c,(d,e)))`.

The shape group of the species tree has been read off the classes of gene trees before the
unrooted tree is used (`ADR11.Nonbinary.FiveTaxa.Shapes`); among the rootings of `U5 2` the groups
are the caterpillars, the pseudocaterpillar, `P₅`, and the balanced trees with `P₆`
(`ac2_group_p5`, `ac2_group_balP6`). This module carries out the remaining steps for two rootings
of `U5 2` with the same shape group.

* The labelling: for two binary trees by Proposition 8 (`proposition8`); for `P₅` by the unrooted
  tree; for the balanced trees and `P₆` by `T₇`, as for the balanced tree in the proof of
  Proposition 7 (`ac2_T7_rule`).
* The lengths: the balanced tree and `P₆` are told apart by solving the equations of the balanced
  tree for `Z`, which gives `Z < 1` for the balanced tree and `Z = 1` for `P₆`
  (`ac2_balanced_P6_rule`); the lengths of `P₅` and `P₆` are solved from the formulas of Table 7
  (`ac2_P5_lengths`, `ac2_P6_lengths`).

The formulas of the gene tree distributions of the labelled rootings are those of
`ADR11.rootingDist5_2_7`, `ADR11.rootingDist5_2_8`, … (the formulas of Table 7 and Appendix B,
with the labels permuted).

## Main results

* `ac2_rootings_two`: two species trees whose unrooted trees are `U5 2`, with the same shape group
  and the same unrooted gene tree distribution, have the same rooted metric tree.
* The rules of Appendix C for the rootings of `U5 2`: `ac2_T7_rule` (the labelling of the balanced
  trees and `P₆`), `ac2_balanced_P6_rule` (`Z < 1` versus `Z = 1`), `ac2_P5_lengths`,
  `ac2_P6_lengths` (the lengths, from Table 7); `ac2_rootings_two_polytomy` combines them.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-! ### Permuting labels: the relabelling `a ↔ d, b ↔ e` -/

/-- The relabelling `a ↔ d, b ↔ e`, which exchanges the two cherries of `U5 2`; it maps
`((a,b),(c,(d,e)))` and `(a,b,(c,(d,e)))` to the balanced tree `(((a,b),c),(d,e))` and to
`P₆ = (((a,b),c),d,e)`. -/
def ac2_flip : Equiv.Perm (Fin 5) := ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by decide, by decide⟩

/-- The permutation of the gene trees induced by `ac2_flip`: it maps `T_i` to `T_{ac2_idxFlip i}`
(`ac2_flip_idx`). -/
def ac2_idxFlip (i : ℕ) : ℕ := [0, 1, 13, 4, 3, 15, 10, 9, 8, 7, 6, 11, 14, 2, 12, 5].getD i 0

theorem ac2_flip_idx : ∀ i ∈ Icc 1 15, ac2_idxFlip i ∈ Icc 1 15 ∧
    relabelFamily ac2_flip (T5 i) = T5 (ac2_idxFlip i) := by
  decide +kernel

theorem ac2_flip_surj : ∀ j ∈ Icc 1 15, ∃ i ∈ Icc 1 15, ac2_idxFlip i = j := by
  decide

/-! ### The least probable class of `P₆` -/

/-- The least probable class of `P₆ = (((a,b),c),d,e)` is `{T₇, T₈, T₁₀, T₁₁, T₁₄, T₁₅}`
(Table 7, with the inequalities of Table 6). -/
theorem ac2_P6_leastClass (τ : SpeciesTree (Fin 5)) (h : τ.clusters = polytomy5 6) :
    cls_leastClass τ = {7, 8, 10, 11, 14, 15} := by
  obtain ⟨h12, h14, h25, h45, h57⟩ := (table6 τ).2.2.2.2.1 h
  obtain ⟨-, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ :=
    rootingDist5_2_8 τ h
  have q3 : u τ 3 = u τ 2 := by rw [e3, e2]
  have q13 : u τ 13 = u τ 4 := by rw [e13, e4]
  have q6 : u τ 6 = u τ 5 := by rw [e6, e5]
  have q9 : u τ 9 = u τ 5 := by rw [e9, e5]
  have q12 : u τ 12 = u τ 5 := by rw [e12, e5]
  refine sh_leastClass_eq (m := 7) (by decide) (by decide) ?_ ?_
  · intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e7, e8, e10, e11, e14, e15]
  · intro i hi hiC
    obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
    interval_cases i <;> first | exact (hiC (by decide)).elim | linarith

/-! ### The shape groups of the rootings of `U5 2` -/

/-- The rootings of `U5 2` with the shape of the balanced tree or of `P₆`: `(((a,b),c),(d,e))`,
`((a,b),(c,(d,e)))`, `(((a,b),c),d,e)`, `(a,b,(c,(d,e)))`. -/
abbrev ac2_balancedP6 : Finset (Finset (Finset (Fin 5))) :=
  {hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}}, hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}},
    hierarchyOf {{0, 1}, {0, 1, 2}}, hierarchyOf {{3, 4}, {2, 3, 4}}}

/-- The rootings of `U5 2` with a polytomy: `P₅ = ((a,b),(d,e),c)`, and `(((a,b),c),d,e)`,
`(a,b,(c,(d,e)))` of shape `P₆`. -/
abbrev ac2_polytomies : Finset (Finset (Finset (Fin 5))) :=
  {hierarchyOf {{0, 1}, {3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2}}, hierarchyOf {{3, 4}, {2, 3, 4}}}

/-- Among the rootings of `U5 2`, `P₅ = ((a,b),(d,e),c)` is the only one in the shape group of
`P₅`: once the shape is known, "the labeling on the unrooted tree determines that on the rooted
one". -/
theorem ac2_group_p5 {τ : SpeciesTree (Fin 5)} (hR : τ.clusters ∈ rootings5 2)
    (hg : sh_groupOf τ.clusters = .p5) : τ.clusters = hierarchyOf {{0, 1}, {3, 4}} := by
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h | h | h | h | h <;> rw [h] at hg ⊢ <;>
    first | rfl | exact absurd hg (by decide +kernel)

/-- Among the rootings of `U5 2`, those in the shape group of the balanced tree and `P₆` are the two
balanced trees and the two rootings of shape `P₆`. -/
theorem ac2_group_balP6 {τ : SpeciesTree (Fin 5)} (hR : τ.clusters ∈ rootings5 2)
    (hg : sh_groupOf τ.clusters = .balP6) : τ.clusters ∈ ac2_balancedP6 := by
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h | h | h | h | h <;> rw [h] at hg ⊢ <;>
    first | decide +kernel | exact absurd hg (by decide +kernel)

/-! ### The labelling of the balanced trees and `P₆`: `T₇` -/

/-- Appendix C, the labelling of the balanced trees and `P₆`, determined "as it was for the
balanced tree in the proof of Proposition 7": from the splits, a balanced species tree is
`(((a,b),c),(d,e))` or `((a,b),(c,(d,e)))`, and one of shape `P₆` is `(((a,b),c),d,e)` or
`(a,b,(c,(d,e)))`; the gene tree `T₇` (splits `AD|BCE`, `ABD|CE`) falls into the least probable
class for the first tree of each pair but not for the second. -/
theorem ac2_T7_rule (τ : SpeciesTree (Fin 5)) :
    (τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}} → 7 ∈ cls_leastClass τ) ∧
    (τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}} → 7 ∈ cls_leastClass τ) ∧
    (τ.clusters = hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}} → 7 ∉ cls_leastClass τ) ∧
    (τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}} → 7 ∉ cls_leastClass τ) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h h7 => ?_, fun h h7 => ?_⟩
  · have hc : cls_leastClass τ = {7, 8, 10, 11, 14, 15} := (balanced_extremeClasses τ h).1
    rw [hc]
    decide
  · rw [ac2_P6_leastClass τ h]
    decide
  · -- permuting the labels `a ↔ d, b ↔ e` maps `τ` to `(((a,b),c),(d,e))` and `T₇` to `T₉`
    obtain ⟨hL, -, -⟩ := sh_classes_idx ac2_flip_idx ac2_flip_surj τ
    have h0 : (τ.relabel ac2_flip).clusters = balanced5 := by
      rw [SpeciesTree.relabel_clusters, h]
      decide +kernel
    have hc : cls_leastClass (τ.relabel ac2_flip) = {7, 8, 10, 11, 14, 15} :=
      (balanced_extremeClasses _ h0).1
    have h9 : ac2_idxFlip 7 ∈ cls_leastClass (τ.relabel ac2_flip) := by
      rw [hL]
      exact mem_image_of_mem _ h7
    rw [hc] at h9
    exact absurd h9 (by decide)
  · -- permuting the labels `a ↔ d, b ↔ e` maps `τ` to `(((a,b),c),d,e)` and `T₇` to `T₉`
    obtain ⟨hL, -, -⟩ := sh_classes_idx ac2_flip_idx ac2_flip_surj τ
    have h0 : (τ.relabel ac2_flip).clusters = polytomy5 6 := by
      rw [SpeciesTree.relabel_clusters, h]
      decide +kernel
    have h9 : ac2_idxFlip 7 ∈ cls_leastClass (τ.relabel ac2_flip) := by
      rw [hL]
      exact mem_image_of_mem _ h7
    rw [ac2_P6_leastClass _ h0] at h9
    exact absurd h9 (by decide)

/-! ### The balanced tree versus `P₆`: `Z < 1` versus `Z = 1` -/

/-- `Z = e^{-z}` solved from the equations (11) of the balanced tree `(((a,b):x,c):y,(d,e):z)`:
by equation (7), `XYZ = 6u₅ + 9u₇` and `XY³Z = 15u₇`, so `Y⁻² = (2u₅ + 3u₇)/(5u₇)`; and
`YZ = 3u₂ + 3u₅ + 9u₇`. -/
noncomputable def ac2_solveZ (u₂ u₅ u₇ : ℝ) : ℝ :=
  (3 * u₂ + 3 * u₅ + 9 * u₇) * √((2 * u₅ + 3 * u₇) / (5 * u₇))

/-- Solving the equations (11) of the balanced tree for `Z`. -/
theorem ac2_solveZ_eq {u₂ u₅ u₇ X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (h₂ : u₂ = 1 / 3 * Y * Z - 1 / 6 * X * Y * Z - 1 / 10 * X * Y ^ 3 * Z)
    (h₅ : u₅ = 1 / 6 * X * Y * Z - 1 / 10 * X * Y ^ 3 * Z) (h₇ : u₇ = 1 / 15 * X * Y ^ 3 * Z) :
    ac2_solveZ u₂ u₅ u₇ = Z := by
  have hX' := hX.ne'
  have hY' := hY.ne'
  have hZ' := hZ.ne'
  have e1 : 3 * u₂ + 3 * u₅ + 9 * u₇ = Y * Z := by
    rw [h₂, h₅, h₇]
    ring
  have e2 : (2 * u₅ + 3 * u₇) / (5 * u₇) = Y⁻¹ ^ 2 := by
    rw [h₅, h₇]
    field_simp
    ring
  rw [ac2_solveZ, e1, e2, Real.sqrt_sq (inv_nonneg.2 hY.le)]
  field_simp

/-- Appendix C, the balanced tree versus `P₆`: "solving the system of equations for the balanced
tree, the species tree is the balanced tree if `Z < 1` and is `P₆` if `Z = 1`". For
`(((a,b):x,c):y,(d,e):z)` the solved `Z` is `e^{-z} < 1`; for `P₆ = (((a,b):x,c):y,d,e)` the
formulas of Table 7 are those of the balanced tree with `Z = 1`. Likewise for
`((a,b):z,(c,(d,e):x):y)` and `(a,b,(c,(d,e):x):y)`, with the labels `a ↔ d`, `b ↔ e` permuted
(`T₂, T₅, T₇` become `T₁₃, T₁₅, T₉`). -/
theorem ac2_balanced_P6_rule (τ : SpeciesTree (Fin 5)) :
    (τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}} →
      ac2_solveZ (u τ 2) (u τ 5) (u τ 7) = exp (-τ.length {3, 4}) ∧ exp (-τ.length {3, 4}) < 1) ∧
    (τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}} → ac2_solveZ (u τ 2) (u τ 5) (u τ 7) = 1) ∧
    (τ.clusters = hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}} →
      ac2_solveZ (u τ 13) (u τ 15) (u τ 9) = exp (-τ.length {0, 1}) ∧
        exp (-τ.length {0, 1}) < 1) ∧
    (τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}} → ac2_solveZ (u τ 13) (u τ 15) (u τ 9) = 1) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨-, e2, -, -, e5, -, e7, -⟩ := rootingDist5_2_5 τ h
    obtain ⟨x0, -⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
    obtain ⟨y0, -⟩ := five_exp_bounds τ (A := {0, 1, 2}) (by rw [h]; decide) (by decide)
    obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {3, 4}) (by rw [h]; decide) (by decide)
    exact ⟨ac2_solveZ_eq x0 y0 z0 (by rw [e2]; ring) (by rw [e5]; ring) (by rw [e7]; ring), z1⟩
  · obtain ⟨-, e2, -, -, e5, -, e7, -⟩ := rootingDist5_2_8 τ h
    obtain ⟨x0, -⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
    obtain ⟨y0, -⟩ := five_exp_bounds τ (A := {0, 1, 2}) (by rw [h]; decide) (by decide)
    exact ac2_solveZ_eq x0 y0 one_pos (by rw [e2]; ring) (by rw [e5]; ring) (by rw [e7]; ring)
  · obtain ⟨-, -, -, -, -, -, -, -, e9, -, -, -, e13, -, e15⟩ := rootingDist5_2_6 τ h
    obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
    obtain ⟨x0, -⟩ := five_exp_bounds τ (A := {3, 4}) (by rw [h]; decide) (by decide)
    obtain ⟨y0, -⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
    exact ⟨ac2_solveZ_eq x0 y0 z0 (by rw [e13]; ring) (by rw [e15]; ring) (by rw [e9]; ring), z1⟩
  · obtain ⟨-, -, -, -, -, -, -, -, e9, -, -, -, e13, -, e15⟩ := rootingDist5_2_9 τ h
    obtain ⟨x0, -⟩ := five_exp_bounds τ (A := {3, 4}) (by rw [h]; decide) (by decide)
    obtain ⟨y0, -⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
    exact ac2_solveZ_eq x0 y0 one_pos (by rw [e13]; ring) (by rw [e15]; ring) (by rw [e9]; ring)

/-! ### The lengths of `P₅` and `P₆`, from Table 7 -/

/-- Appendix C, the lengths of `P₅ = ((a,b):x,(d,e):y,c)`, solved from the formulas of Table 7:
`X = 3u₄ + 12u₅` and `Y = 3u₂ + 12u₅`. -/
theorem ac2_P5_lengths (τ : SpeciesTree (Fin 5)) (h : τ.clusters = hierarchyOf {{0, 1}, {3, 4}}) :
    τ.length {0, 1} = -log (3 * u τ 4 + 12 * u τ 5) ∧
      τ.length {3, 4} = -log (3 * u τ 2 + 12 * u τ 5) := by
  obtain ⟨-, e2, -, e4, e5, -⟩ := rootingDist5_2_7 τ h
  constructor
  · rw [show 3 * u τ 4 + 12 * u τ 5 = exp (-τ.length {0, 1}) by rw [e4, e5]; ring, log_exp,
      neg_neg]
  · rw [show 3 * u τ 2 + 12 * u τ 5 = exp (-τ.length {3, 4}) by rw [e2, e5]; ring, log_exp,
      neg_neg]

/-- Appendix C, the lengths of `P₆ = (((a,b):x,c):y,d,e)`, solved from the formulas of Table 7:
`X = 3u₄ + 6u₅ + 6u₇` and `Y = 3u₂ + 3u₅ + 9u₇`; likewise for `(a,b,(c,(d,e):x):y)`, with the
labels `a ↔ d`, `b ↔ e` permuted. -/
theorem ac2_P6_lengths (τ : SpeciesTree (Fin 5)) :
    (τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}} →
      τ.length {0, 1} = -log (3 * u τ 4 + 6 * u τ 5 + 6 * u τ 7) ∧
        τ.length {0, 1, 2} = -log (3 * u τ 2 + 3 * u τ 5 + 9 * u τ 7)) ∧
    (τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}} →
      τ.length {3, 4} = -log (3 * u τ 3 + 6 * u τ 15 + 6 * u τ 9) ∧
        τ.length {2, 3, 4} = -log (3 * u τ 13 + 3 * u τ 15 + 9 * u τ 9)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨-, e2, -, e4, e5, -, e7, -⟩ := rootingDist5_2_8 τ h
    constructor
    · rw [show 3 * u τ 4 + 6 * u τ 5 + 6 * u τ 7 = exp (-τ.length {0, 1}) by
        rw [e4, e5, e7]; ring, log_exp, neg_neg]
    · rw [show 3 * u τ 2 + 3 * u τ 5 + 9 * u τ 7 = exp (-τ.length {0, 1, 2}) by
        rw [e2, e5, e7]; ring, log_exp, neg_neg]
  · obtain ⟨-, -, e3, -, -, -, -, -, e9, -, -, -, e13, -, e15⟩ := rootingDist5_2_9 τ h
    constructor
    · rw [show 3 * u τ 3 + 6 * u τ 15 + 6 * u τ 9 = exp (-τ.length {3, 4}) by
        rw [e3, e15, e9]; ring, log_exp, neg_neg]
    · rw [show 3 * u τ 13 + 3 * u τ 15 + 9 * u τ 9 = exp (-τ.length {2, 3, 4}) by
        rw [e13, e15, e9]; ring, log_exp, neg_neg]

/-- Two copies of `P₅ = ((a,b),(d,e),c)` with the same distribution have the same lengths
(`ac2_P5_lengths`). -/
theorem ac2_P5_same {τ τ' : SpeciesTree (Fin 5)} (h : τ.unrootedDist id = τ'.unrootedDist id)
    (hτ : τ.clusters = hierarchyOf {{0, 1}, {3, 4}})
    (hτ' : τ'.clusters = hierarchyOf {{0, 1}, {3, 4}}) : τ.SameRootedMetricTree τ' := by
  obtain ⟨l1, l2⟩ := ac2_P5_lengths τ hτ
  obtain ⟨l1', l2'⟩ := ac2_P5_lengths τ' hτ'
  simp only [cls_u_congr h] at l1 l2
  refine five_sameRootedMetricTree_of_lengths hτ hτ' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨l1.trans l1'.symm, l2.trans l2'.symm⟩

/-- Two copies of `P₆ = (((a,b),c),d,e)`, or of `(a,b,(c,(d,e)))`, with the same distribution have
the same lengths (`ac2_P6_lengths`). -/
theorem ac2_P6_same {τ τ' : SpeciesTree (Fin 5)} (h : τ.unrootedDist id = τ'.unrootedDist id)
    {H : Finset (Finset (Fin 5))}
    (hH : H = hierarchyOf {{0, 1}, {0, 1, 2}} ∨ H = hierarchyOf {{3, 4}, {2, 3, 4}})
    (hτ : τ.clusters = H) (hτ' : τ'.clusters = H) : τ.SameRootedMetricTree τ' := by
  rcases hH with rfl | rfl
  · obtain ⟨l1, l2⟩ := (ac2_P6_lengths τ).1 hτ
    obtain ⟨l1', l2'⟩ := (ac2_P6_lengths τ').1 hτ'
    simp only [cls_u_congr h] at l1 l2
    refine five_sameRootedMetricTree_of_lengths hτ hτ' ?_
    simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
    exact ⟨l1.trans l1'.symm, l2.trans l2'.symm⟩
  · obtain ⟨l1, l2⟩ := (ac2_P6_lengths τ).2 hτ
    obtain ⟨l1', l2'⟩ := (ac2_P6_lengths τ').2 hτ'
    simp only [cls_u_congr h] at l1 l2
    refine five_sameRootedMetricTree_of_lengths hτ hτ' ?_
    simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
    exact ⟨l1.trans l1'.symm, l2.trans l2'.symm⟩

/-! ### The rootings of `U5 2` -/

section Binary

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

set_option synthInstance.maxSize 1000 in
/-- The seven binary rootings of `U5 2` are binary hierarchies. -/
theorem ac2_binaryRootings_isBinary : ∀ H ∈ binaryRootings5, ∀ A ∈ H, 2 ≤ #A →
    ∃ B ∈ H, ∃ C ∈ H, Disjoint B C ∧ B ∪ C = A := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
/-- The rootings of `U5 2` other than `P₅` and the two `P₆` are the binary ones. -/
theorem ac2_rootings5_two_cases :
    ∀ H ∈ rootings5 2, H ∉ ac2_polytomies → H ∈ binaryRootings5 := by
  decide +kernel

end Binary

/-- The rootings of `U5 2` other than `P₅` and the two `P₆` are binary. -/
theorem ac2_isBinary {τ : SpeciesTree (Fin 5)} (hR : τ.clusters ∈ rootings5 2)
    (hn : τ.clusters ∉ ac2_polytomies) : τ.IsBinary :=
  ac2_binaryRootings_isBinary _ (ac2_rootings5_two_cases _ hR hn)

/-- Appendix C for a rooting `τ` of `U5 2` with a polytomy, `P₅` or `P₆`, and any rooting `τ'` of
`U5 2` with the same shape group and the same distribution. For `P₅`, the labelling is that of the
unrooted tree (`ac2_group_p5`). For `P₆`, `τ'` is a balanced tree or of shape `P₆`
(`ac2_group_balP6`); the labelling is given by `T₇` (`ac2_T7_rule`), and the balanced tree is told
apart from `P₆` by `Z < 1` versus `Z = 1` (`ac2_balanced_P6_rule`). The lengths: Table 7. -/
theorem ac2_rootings_two_polytomy (τ τ' : SpeciesTree (Fin 5)) (hn : τ.clusters ∈ ac2_polytomies)
    (hR' : τ'.clusters ∈ rootings5 2) (hg : sh_groupOf τ.clusters = sh_groupOf τ'.clusters)
    (h : τ.unrootedDist id = τ'.unrootedDist id) : τ.SameRootedMetricTree τ' := by
  have hC := cls_leastClass_congr h
  have hu := cls_u_congr h
  simp only [ac2_polytomies, mem_insert, mem_singleton] at hn
  rcases hn with hτ | hτ | hτ
  · -- `P₅`: the labelling is that of the unrooted tree
    have g5 : sh_groupOf τ'.clusters = .p5 := by
      rw [← hg, hτ]
      decide +kernel
    exact ac2_P5_same h hτ (ac2_group_p5 hR' g5)
  · -- `P₆ = (((a,b),c),d,e)`: `τ'` is a balanced tree or of shape `P₆`
    have hs : τ'.clusters ∈ ac2_balancedP6 := ac2_group_balP6 hR' (by
      rw [← hg, hτ]
      decide +kernel)
    -- the labelling: `T₇ ∈ 𝒞`
    have h7 : 7 ∈ cls_leastClass τ' := by rw [← hC]; exact (ac2_T7_rule τ).2.1 hτ
    simp only [ac2_balancedP6, mem_insert, mem_singleton] at hs
    rcases hs with hτ' | hτ' | hτ' | hτ'
    · -- the balanced tree `(((a,b),c),(d,e))` has `Z < 1`, `P₆` has `Z = 1`
      exfalso
      have z := (ac2_balanced_P6_rule τ).2.1 hτ
      obtain ⟨z', z1⟩ := (ac2_balanced_P6_rule τ').1 hτ'
      simp only [hu] at z
      rw [z] at z'
      linarith
    · exact absurd h7 ((ac2_T7_rule τ').2.2.1 hτ')
    · exact ac2_P6_same h (Or.inl rfl) hτ hτ'
    · exact absurd h7 ((ac2_T7_rule τ').2.2.2 hτ')
  · -- `P₆ = (a,b,(c,(d,e)))`: `τ'` is a balanced tree or of shape `P₆`
    have hs : τ'.clusters ∈ ac2_balancedP6 := ac2_group_balP6 hR' (by
      rw [← hg, hτ]
      decide +kernel)
    -- the labelling: `T₇ ∉ 𝒞`
    have h7 : 7 ∉ cls_leastClass τ' := by rw [← hC]; exact (ac2_T7_rule τ).2.2.2 hτ
    simp only [ac2_balancedP6, mem_insert, mem_singleton] at hs
    rcases hs with hτ' | hτ' | hτ' | hτ'
    · exact absurd ((ac2_T7_rule τ').1 hτ') h7
    · -- the balanced tree `((a,b),(c,(d,e)))` has `Z < 1`, `(a,b,(c,(d,e)))` has `Z = 1`
      exfalso
      have z := (ac2_balanced_P6_rule τ).2.2.2 hτ
      obtain ⟨z', z1⟩ := (ac2_balanced_P6_rule τ').2.2.1 hτ'
      simp only [hu] at z
      rw [z] at z'
      linarith
    · exact absurd ((ac2_T7_rule τ').2.1 hτ') h7
    · exact ac2_P6_same h (Or.inr rfl) hτ hτ'

/-- Appendix C (proof of Proposition 11) for the unrooted tree `U5 2` (splits `ab|cde`,
`abc|de`): two species trees whose unrooted trees are `U5 2`, with the same shape group (read off
the gene tree classes, `sh_group_eq`) and the same unrooted gene tree distribution, have the same
rooted metric tree. If both are binary, the labelling and the lengths are given by Proposition 8;
if one of them has a polytomy (`P₅` or `P₆`), by `ac2_rootings_two_polytomy`. -/
theorem ac2_rootings_two (τ τ' : SpeciesTree (Fin 5)) (hk : unroot τ.clusters = U5 2)
    (hk' : unroot τ'.clusters = U5 2) (hg : sh_groupOf τ.clusters = sh_groupOf τ'.clusters)
    (h : τ.unrootedDist id = τ'.unrootedDist id) : τ.SameRootedMetricTree τ' := by
  have hR := classify_mem_rootings5 τ 2 (by simp) hk
  have hR' := classify_mem_rootings5 τ' 2 (by simp) hk'
  by_cases hn : τ.clusters ∈ ac2_polytomies
  · exact ac2_rootings_two_polytomy τ τ' hn hR' hg h
  by_cases hn' : τ'.clusters ∈ ac2_polytomies
  · exact (ac2_rootings_two_polytomy τ' τ hn' hR hg.symm h.symm).symm
  -- both trees are binary: Proposition 8
  exact proposition8 (Fintype.card_fin 5) τ τ' (ac2_isBinary hR hn) (ac2_isBinary hR' hn') h

end ADR11
