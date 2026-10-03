module

public import ADR11.Identifiability.Proposition8
public import ADR11.Identifiability.FiveTaxa.Classes
public import ADR11.Identifiability.FiveTaxa.Common
public import ADR11.Nonbinary.AppendixC

/-!
# Appendix C for the rootings of `U5 2`

The proof of Proposition 11 (Appendix C of the paper, l. 938–995) for the five-taxon species trees
whose unrooted tree is `U5 2`, with the splits `ab|cde` and `abc|de`. Its ten rootings
(`ADR11.rootings5 2`) are the four caterpillars `((((a,b),c),d),e)`, `((((a,b),c),e),d)`,
`((((d,e),c),b),a)`, `((((d,e),c),a),b)`, the pseudocaterpillar `(((a,b),(d,e)),c)`, the balanced
trees `(((a,b),c),(d,e))` and `((a,b),(c,(d,e)))`, the polytomy `P₅ = ((a,b),(d,e),c)`, and the
two polytomies of shape `P₆`, `(((a,b),c),d,e)` and `(a,b,(c,(d,e)))`. Following the paper, the
rooted metric tree is read off the distribution in three steps.

* The shape, from the size of the least probable class `𝒞` and of the class with the second
  smallest probability: `|𝒞| = 10` only for `P₅`, `|𝒞| = 8` for the pseudocaterpillar, and
  `|𝒞| = 6` for the others, with a second class of two trees for the caterpillars and of four
  trees for the balanced trees and `P₆` (`ac2_classSizes`, from `appendixC_leastClass` by
  permuting labels; `ac2_P5_shape`, `ac2_balanced_P6_shape`).
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

* `ac2_rootings_two`: two species trees whose unrooted trees are `U5 2`, with the same unrooted
  gene tree distribution, have the same rooted metric tree.
* The rules of Appendix C for the rootings of `U5 2`: `ac2_classSizes`, `ac2_P5_shape`,
  `ac2_balanced_P6_shape` (the shape), `ac2_T7_rule` (the labelling of the balanced trees and
  `P₆`), `ac2_balanced_P6_rule` (`Z < 1` versus `Z = 1`), `ac2_P5_lengths`, `ac2_P6_lengths` (the
  lengths, from Table 7); `ac2_rootings_two_polytomy` combines them.
* `ac2_P5_P7_rule`: the rule of Appendix C telling `P₅` from `P₇` (both with `|𝒞| = 10`) by the
  cherries of the trees of their two 2-element classes, also when these merge into one 4-element
  class; `ac2_P5_P7_distinguish`: the rule separates the two representatives.
* `ac2_classes_transport`, `ac2_classes_relabel`: relabelling the taxa permutes the classes
  ("permuting labels").
-/

@[expose] public section

namespace ADR11

open Finset Real

/-! ### Permuting labels: transport of the classes -/

/-- If `s` permutes the indices `[1, 15]` and `u τ₀ (s i) = u τ i`, then `T_i` is in the least
probable class of `τ` iff `T_{s i}` is in that of `τ₀`, and the least probable classes, and the
classes with the second smallest probability, of `τ` and `τ₀` have the same sizes. -/
theorem ac2_classes_transport {τ τ₀ : SpeciesTree (Fin 5)} {s : ℕ → ℕ}
    (hs : (Icc 1 15).image s = Icc 1 15) (hu : ∀ i ∈ Icc 1 15, u τ₀ (s i) = u τ i) :
    (∀ i ∈ Icc 1 15, (i ∈ cls_leastClass τ ↔ s i ∈ cls_leastClass τ₀)) ∧
      #(cls_leastClass τ₀) = #(cls_leastClass τ) ∧
      #(cls_secondClass τ₀) = #(cls_secondClass τ) := by
  have hmaps : ∀ i ∈ Icc 1 15, s i ∈ Icc 1 15 := fun i hi => hs ▸ mem_image_of_mem s hi
  have hsurj : ∀ j ∈ Icc 1 15, ∃ i ∈ Icc 1 15, s i = j := fun j hj =>
    mem_image.1 (hs.symm ▸ hj)
  have hinj : Set.InjOn s (Icc 1 15 : Finset ℕ) := by
    rw [← Finset.card_image_iff, hs]
  have hL : ∀ i ∈ Icc 1 15, (i ∈ cls_leastClass τ ↔ s i ∈ cls_leastClass τ₀) := by
    intro i hi
    simp only [cls_leastClass, mem_filter]
    constructor
    · rintro ⟨-, h⟩
      refine ⟨hmaps i hi, fun j hj => ?_⟩
      obtain ⟨k, hk, rfl⟩ := hsurj j hj
      rw [hu i hi, hu k hk]
      exact h k hk
    · rintro ⟨-, h⟩
      refine ⟨hi, fun j hj => ?_⟩
      rw [← hu i hi, ← hu j hj]
      exact h _ (hmaps j hj)
  have hC2 : ∀ i ∈ Icc 1 15, (i ∈ cls_secondClass τ ↔ s i ∈ cls_secondClass τ₀) := by
    intro i hi
    simp only [cls_secondClass, mem_filter]
    constructor
    · rintro ⟨-, hiL, h⟩
      refine ⟨hmaps i hi, fun h' => hiL ((hL i hi).2 h'), fun j hj hjL => ?_⟩
      obtain ⟨k, hk, rfl⟩ := hsurj j hj
      rw [hu i hi, hu k hk]
      exact h k hk fun h' => hjL ((hL k hk).1 h')
    · rintro ⟨-, hiL, h⟩
      refine ⟨hi, fun h' => hiL ((hL i hi).1 h'), fun j hj hjL => ?_⟩
      rw [← hu i hi, ← hu j hj]
      exact h _ (hmaps j hj) fun h' => hjL ((hL j hj).2 h')
  have himg : ∀ A : SpeciesTree (Fin 5) → Finset ℕ, (∀ σ, A σ ⊆ Icc 1 15) →
      (∀ i ∈ Icc 1 15, (i ∈ A τ ↔ s i ∈ A τ₀)) → #(A τ₀) = #(A τ) := by
    intro A hA hmem
    have : A τ₀ = (A τ).image s := by
      ext j
      constructor
      · intro hj
        obtain ⟨i, hi, rfl⟩ := hsurj j (hA τ₀ hj)
        exact mem_image_of_mem s ((hmem i hi).2 hj)
      · intro hj
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hj
        exact (hmem i (hA τ hi)).1 hi
    rw [this, card_image_of_injOn (Set.InjOn.mono (coe_subset.2 (hA τ)) hinj)]
  refine ⟨hL, himg cls_leastClass (fun _ _ hi => ?_) hL,
    himg cls_secondClass (fun _ _ hi => ?_) hC2⟩
  · simp only [cls_leastClass, mem_filter] at hi
    exact hi.1
  · simp only [cls_secondClass, mem_filter] at hi
    exact hi.1

/-- Relabelling the taxa along `e`, which maps each gene tree `T_i` to `T_{s i}`, permutes the
classes ("permuting labels immediately gives the distribution for other choices", l. 319). -/
theorem ac2_classes_relabel {e : Equiv.Perm (Fin 5)} {s : ℕ → ℕ}
    (hT : ∀ i ∈ Icc 1 15, relabelFamily e (T5 i) = T5 (s i))
    (hs : (Icc 1 15).image s = Icc 1 15) (τ : SpeciesTree (Fin 5)) :
    (∀ i ∈ Icc 1 15, (i ∈ cls_leastClass τ ↔ s i ∈ cls_leastClass (τ.relabel e))) ∧
      #(cls_leastClass (τ.relabel e)) = #(cls_leastClass τ) ∧
      #(cls_secondClass (τ.relabel e)) = #(cls_secondClass τ) :=
  ac2_classes_transport hs fun i hi => cls_u_relabel τ e (hT i hi)

/-- The relabelling `d ↔ e`; it maps `((((a,b),c),e),d)` to the caterpillar `((((a,b),c),d),e)`. -/
def ac2_swapDE : Equiv.Perm (Fin 5) := ⟨![0, 1, 2, 4, 3], ![0, 1, 2, 4, 3], by decide, by decide⟩

/-- The relabelling `a ↦ e ↦ b ↦ d ↦ a`; it maps `((((d,e),c),b),a)` to the caterpillar
`((((a,b),c),d),e)`. -/
def ac2_cycle : Equiv.Perm (Fin 5) := ⟨![4, 3, 2, 0, 1], ![3, 4, 2, 1, 0], by decide, by decide⟩

/-- The relabelling `a ↔ d, b ↔ e`, which exchanges the two cherries of `U5 2`; it maps
`((((d,e),c),a),b)`, `((a,b),(c,(d,e)))` and `(a,b,(c,(d,e)))` to the caterpillar
`((((a,b),c),d),e)`, the balanced tree `(((a,b),c),(d,e))` and `P₆ = (((a,b),c),d,e)`. -/
def ac2_flip : Equiv.Perm (Fin 5) := ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by decide, by decide⟩

/-- `ac2_swapDE` maps `T_i` to `T_{ac2_idxDE i}` (`ac2_swapDE_T5`). -/
def ac2_idxDE (i : ℕ) : ℕ := [0, 1, 3, 2, 4, 6, 5, 10, 11, 12, 7, 8, 9, 13, 15, 14].getD i 0

/-- `ac2_cycle` maps `T_i` to `T_{ac2_idxCycle i}` (`ac2_cycle_T5`). -/
def ac2_idxCycle (i : ℕ) : ℕ := [0, 1, 13, 4, 2, 14, 7, 12, 11, 10, 5, 8, 15, 3, 9, 6].getD i 0

/-- `ac2_flip` maps `T_i` to `T_{ac2_idxFlip i}` (`ac2_flip_T5`). -/
def ac2_idxFlip (i : ℕ) : ℕ := [0, 1, 13, 4, 3, 15, 10, 9, 8, 7, 6, 11, 14, 2, 12, 5].getD i 0

/-- `ac2_swapDE` maps each gene tree `T_i` to `T_{ac2_idxDE i}`. -/
theorem ac2_swapDE_T5 : ∀ i ∈ Icc 1 15, relabelFamily ac2_swapDE (T5 i) = T5 (ac2_idxDE i) := by
  decide +kernel

/-- `ac2_cycle` maps each gene tree `T_i` to `T_{ac2_idxCycle i}`. -/
theorem ac2_cycle_T5 : ∀ i ∈ Icc 1 15, relabelFamily ac2_cycle (T5 i) = T5 (ac2_idxCycle i) := by
  decide +kernel

/-- `ac2_flip` maps each gene tree `T_i` to `T_{ac2_idxFlip i}`. -/
theorem ac2_flip_T5 : ∀ i ∈ Icc 1 15, relabelFamily ac2_flip (T5 i) = T5 (ac2_idxFlip i) := by
  decide +kernel

/-- `ac2_idxDE` permutes `[1, 15]`. -/
theorem ac2_idxDE_image : (Icc 1 15).image ac2_idxDE = Icc 1 15 := by
  decide +kernel

/-- `ac2_idxCycle` permutes `[1, 15]`. -/
theorem ac2_idxCycle_image : (Icc 1 15).image ac2_idxCycle = Icc 1 15 := by
  decide +kernel

/-- `ac2_idxFlip` permutes `[1, 15]`. -/
theorem ac2_idxFlip_image : (Icc 1 15).image ac2_idxFlip = Icc 1 15 := by
  decide +kernel

/-! ### Classes given by explicit values -/

/-- A set `C ⊆ [1, 15]` of equiprobable trees, less probable than all the others, is the least
probable class. -/
theorem ac2_leastClass_eq {τ : SpeciesTree (Fin 5)} {C : Finset ℕ} {m : ℕ} (hC : C ⊆ Icc 1 15)
    (hm : m ∈ C) (heq : ∀ i ∈ C, u τ i = u τ m) (hlt : ∀ i ∈ Icc 1 15, i ∉ C → u τ m < u τ i) :
    cls_leastClass τ = C := by
  ext i
  simp only [cls_leastClass, mem_filter]
  constructor
  · rintro ⟨hi, h⟩
    by_contra hiC
    exact absurd (h m (hC hm)) (not_le.2 (hlt i hi hiC))
  · intro hiC
    refine ⟨hC hiC, fun j hj => ?_⟩
    rw [heq i hiC]
    by_cases hjC : j ∈ C
    · rw [heq j hjC]
    · exact (hlt j hj hjC).le

/-- A set `C ⊆ [1, 15]` of equiprobable trees, more probable than all the others, is the set of
the most probable trees. -/
theorem ac2_mostProbable_eq {τ : SpeciesTree (Fin 5)} {C : Finset ℕ} {m : ℕ} (hC : C ⊆ Icc 1 15)
    (hm : m ∈ C) (heq : ∀ i ∈ C, u τ i = u τ m) (hlt : ∀ i ∈ Icc 1 15, i ∉ C → u τ i < u τ m) :
    cls_mostProbable τ = C := by
  ext i
  simp only [cls_mostProbable, mem_filter]
  constructor
  · rintro ⟨hi, h⟩
    by_contra hiC
    exact absurd (h m (hC hm)) (not_le.2 (hlt i hi hiC))
  · intro hiC
    refine ⟨hC hiC, fun j hj => ?_⟩
    rw [heq i hiC]
    by_cases hjC : j ∈ C
    · rw [heq j hjC]
    · exact (hlt j hj hjC).le

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
  refine ac2_leastClass_eq (m := 7) (by decide) (by decide) ?_ ?_
  · intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e7, e8, e10, e11, e14, e15]
  · intro i hi hiC
    obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
    interval_cases i <;> first | exact (hiC (by decide)).elim | linarith

/-! ### The shape: the sizes of the classes -/

/-- The four caterpillar rootings of `U5 2`: `((((a,b),c),d),e)`, `((((a,b),c),e),d)`,
`((((d,e),c),b),a)`, `((((d,e),c),a),b)`. -/
abbrev ac2_caterpillars : Finset (Finset (Finset (Fin 5))) :=
  {hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}, hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}},
    hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}, hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}}}

/-- The rootings of `U5 2` with the shape of the balanced tree or of `P₆`: `(((a,b),c),(d,e))`,
`((a,b),(c,(d,e)))`, `(((a,b),c),d,e)`, `(a,b,(c,(d,e)))`. -/
abbrev ac2_balancedP6 : Finset (Finset (Finset (Fin 5))) :=
  {hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}}, hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}},
    hierarchyOf {{0, 1}, {0, 1, 2}}, hierarchyOf {{3, 4}, {2, 3, 4}}}

/-- The rootings of `U5 2` with a polytomy: `P₅ = ((a,b),(d,e),c)`, and `(((a,b),c),d,e)`,
`(a,b,(c,(d,e)))` of shape `P₆`. -/
abbrev ac2_polytomies : Finset (Finset (Finset (Fin 5))) :=
  {hierarchyOf {{0, 1}, {3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2}}, hierarchyOf {{3, 4}, {2, 3, 4}}}

/-- Appendix C, the sizes of the classes for the rootings of `U5 2` (those of the representatives,
`appendixC_leastClass`, with the labels permuted): the least probable class `𝒞` has six trees and
the class with the second smallest probability two for the four caterpillars; `|𝒞| = 8` for the
pseudocaterpillar `(((a,b),(d,e)),c)`; `|𝒞| = 6` and a second class of four trees for the
balanced trees and the two `P₆`; `|𝒞| = 10` for `P₅ = ((a,b),(d,e),c)`. -/
theorem ac2_classSizes (τ : SpeciesTree (Fin 5)) :
    (τ.clusters ∈ ac2_caterpillars → #(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 2) ∧
    (τ.clusters = hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}} → #(cls_leastClass τ) = 8) ∧
    (τ.clusters ∈ ac2_balancedP6 → #(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 4) ∧
    (τ.clusters = hierarchyOf {{0, 1}, {3, 4}} → #(cls_leastClass τ) = 10) := by
  refine ⟨fun h => ?_, fun h => (appendixC_leastClass τ).2.2.2.2.2.1 h, fun h => ?_,
    fun h => (appendixC_leastClass τ).2.2.2.1 h⟩
  · simp only [ac2_caterpillars, mem_insert, mem_singleton] at h
    rcases h with h | h | h | h
    · exact (appendixC_leastClass τ).2.2.2.2.2.2.1 h
    · obtain ⟨-, e1, e2⟩ := ac2_classes_relabel ac2_swapDE_T5 ac2_idxDE_image τ
      have h0 : (τ.relabel ac2_swapDE).clusters = caterpillar5 := by
        rw [SpeciesTree.relabel_clusters, h]
        decide +kernel
      rw [← e1, ← e2]
      exact (appendixC_leastClass _).2.2.2.2.2.2.1 h0
    · obtain ⟨-, e1, e2⟩ := ac2_classes_relabel ac2_cycle_T5 ac2_idxCycle_image τ
      have h0 : (τ.relabel ac2_cycle).clusters = caterpillar5 := by
        rw [SpeciesTree.relabel_clusters, h]
        decide +kernel
      rw [← e1, ← e2]
      exact (appendixC_leastClass _).2.2.2.2.2.2.1 h0
    · obtain ⟨-, e1, e2⟩ := ac2_classes_relabel ac2_flip_T5 ac2_idxFlip_image τ
      have h0 : (τ.relabel ac2_flip).clusters = caterpillar5 := by
        rw [SpeciesTree.relabel_clusters, h]
        decide +kernel
      rw [← e1, ← e2]
      exact (appendixC_leastClass _).2.2.2.2.2.2.1 h0
  · simp only [ac2_balancedP6, mem_insert, mem_singleton] at h
    rcases h with h | h | h | h
    · exact (appendixC_leastClass τ).2.2.2.2.2.2.2.1 h
    · obtain ⟨-, e1, e2⟩ := ac2_classes_relabel ac2_flip_T5 ac2_idxFlip_image τ
      have h0 : (τ.relabel ac2_flip).clusters = balanced5 := by
        rw [SpeciesTree.relabel_clusters, h]
        decide +kernel
      rw [← e1, ← e2]
      exact (appendixC_leastClass _).2.2.2.2.2.2.2.1 h0
    · exact (appendixC_leastClass τ).2.2.2.2.2.2.2.2.2.1 h
    · obtain ⟨-, e1, e2⟩ := ac2_classes_relabel ac2_flip_T5 ac2_idxFlip_image τ
      have h0 : (τ.relabel ac2_flip).clusters = polytomy5 6 := by
        rw [SpeciesTree.relabel_clusters, h]
        decide +kernel
      rw [← e1, ← e2]
      exact (appendixC_leastClass _).2.2.2.2.2.2.2.2.2.1 h0

/-- Appendix C, `|𝒞| = 10`: among the rootings of `U5 2`, the least probable class has ten trees
exactly for `P₅ = ((a,b),(d,e),c)`. As this is the only rooting of `U5 2` of shape `P₅`, "the
labeling on the unrooted tree determines that on the rooted one". -/
theorem ac2_P5_shape (τ : SpeciesTree (Fin 5)) (hR : τ.clusters ∈ rootings5 2) :
    #(cls_leastClass τ) = 10 ↔ τ.clusters = hierarchyOf {{0, 1}, {3, 4}} := by
  obtain ⟨hc, hp, hb, h5⟩ := ac2_classSizes τ
  have cat (h : τ.clusters ∈ ac2_caterpillars) :
      #(cls_leastClass τ) = 10 ↔ τ.clusters = hierarchyOf {{0, 1}, {3, 4}} := by
    refine iff_of_false (fun h' => absurd (h'.symm.trans (hc h).1) (by decide)) fun h' => ?_
    rw [h'] at h
    exact absurd h (by decide +kernel)
  have bal (h : τ.clusters ∈ ac2_balancedP6) :
      #(cls_leastClass τ) = 10 ↔ τ.clusters = hierarchyOf {{0, 1}, {3, 4}} := by
    refine iff_of_false (fun h' => absurd (h'.symm.trans (hb h).1) (by decide)) fun h' => ?_
    rw [h'] at h
    exact absurd h (by decide +kernel)
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h | h | h | h | h
  · exact cat (by rw [h]; decide +kernel)
  · exact cat (by rw [h]; decide +kernel)
  · exact cat (by rw [h]; decide +kernel)
  · exact cat (by rw [h]; decide +kernel)
  · refine iff_of_false (fun h' => absurd (h'.symm.trans (hp h)) (by decide)) ?_
    rw [h]
    decide +kernel
  · exact bal (by rw [h]; decide +kernel)
  · exact bal (by rw [h]; decide +kernel)
  · exact iff_of_true (h5 h) h
  · exact bal (by rw [h]; decide +kernel)
  · exact bal (by rw [h]; decide +kernel)

/-- Appendix C, `|𝒞| = 6`: among the rootings of `U5 2`, the least probable class has six trees
and the class with the second smallest probability four exactly for the balanced trees and `P₆`
(the caterpillars have a second class of two trees, the pseudocaterpillar has `|𝒞| = 8`, and
`P₅` has `|𝒞| = 10`). -/
theorem ac2_balanced_P6_shape (τ : SpeciesTree (Fin 5)) (hR : τ.clusters ∈ rootings5 2) :
    (#(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 4) ↔ τ.clusters ∈ ac2_balancedP6 := by
  obtain ⟨hc, hp, hb, h5⟩ := ac2_classSizes τ
  have cat (h : τ.clusters ∈ ac2_caterpillars) (hn : τ.clusters ∉ ac2_balancedP6) :
      (#(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 4) ↔ τ.clusters ∈ ac2_balancedP6 :=
    iff_of_false (fun h' => absurd (h'.2.symm.trans (hc h).2) (by decide)) hn
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h | h | h | h | h
  · exact cat (by rw [h]; decide +kernel) (by rw [h]; decide +kernel)
  · exact cat (by rw [h]; decide +kernel) (by rw [h]; decide +kernel)
  · exact cat (by rw [h]; decide +kernel) (by rw [h]; decide +kernel)
  · exact cat (by rw [h]; decide +kernel) (by rw [h]; decide +kernel)
  · refine iff_of_false (fun h' => absurd (h'.1.symm.trans (hp h)) (by decide)) ?_
    rw [h]
    decide +kernel
  · exact iff_of_true (hb (by rw [h]; decide +kernel)) (by rw [h]; decide +kernel)
  · exact iff_of_true (hb (by rw [h]; decide +kernel)) (by rw [h]; decide +kernel)
  · refine iff_of_false (fun h' => absurd (h'.1.symm.trans (h5 h)) (by decide)) ?_
    rw [h]
    decide +kernel
  · exact iff_of_true (hb (by rw [h]; decide +kernel)) (by rw [h]; decide +kernel)
  · exact iff_of_true (hb (by rw [h]; decide +kernel)) (by rw [h]; decide +kernel)

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
  · obtain ⟨hL, -, -⟩ := ac2_classes_relabel ac2_flip_T5 ac2_idxFlip_image τ
    have h0 : (τ.relabel ac2_flip).clusters = balanced5 := by
      rw [SpeciesTree.relabel_clusters, h]
      decide +kernel
    have hc : cls_leastClass (τ.relabel ac2_flip) = {7, 8, 10, 11, 14, 15} :=
      (balanced_extremeClasses _ h0).1
    have := (hL 7 (by decide)).1 h7
    rw [hc] at this
    exact absurd this (by decide)
  · obtain ⟨hL, -, -⟩ := ac2_classes_relabel ac2_flip_T5 ac2_idxFlip_image τ
    have h0 : (τ.relabel ac2_flip).clusters = polytomy5 6 := by
      rw [SpeciesTree.relabel_clusters, h]
      decide +kernel
    have := (hL 7 (by decide)).1 h7
    rw [ac2_P6_leastClass _ h0] at this
    exact absurd this (by decide)

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
`U5 2` with the same distribution. The shape: `P₅` is the only rooting with `|𝒞| = 10`; the
balanced trees and `P₆` are those with `|𝒞| = 6` and a second class of four trees. The labelling:
for `P₅` by the unrooted tree; for the balanced trees and `P₆` by `T₇`. The balanced tree versus
`P₆`: `Z < 1` versus `Z = 1`. The lengths: Table 7. -/
theorem ac2_rootings_two_polytomy (τ τ' : SpeciesTree (Fin 5)) (hn : τ.clusters ∈ ac2_polytomies)
    (hR' : τ'.clusters ∈ rootings5 2) (h : τ.unrootedDist id = τ'.unrootedDist id) :
    τ.SameRootedMetricTree τ' := by
  have hC := cls_leastClass_congr h
  have hC2 := cls_secondClass_congr h
  have hu := cls_u_congr h
  obtain ⟨-, -, hb, h5⟩ := ac2_classSizes τ
  simp only [ac2_polytomies, mem_insert, mem_singleton] at hn
  rcases hn with hτ | hτ | hτ
  · -- `P₅`: `|𝒞| = 10`, and the labelling is that of the unrooted tree
    have h10 : #(cls_leastClass τ') = 10 := by rw [← hC]; exact h5 hτ
    exact ac2_P5_same h hτ ((ac2_P5_shape τ' hR').1 h10)
  · -- `P₆ = (((a,b),c),d,e)`: `|𝒞| = 6`, second class of four trees
    obtain ⟨c6, c4⟩ := hb (by rw [hτ]; decide +kernel)
    have hs := (ac2_balanced_P6_shape τ' hR').1 ⟨by rw [← hC]; exact c6, by rw [← hC2]; exact c4⟩
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
  · -- `P₆ = (a,b,(c,(d,e)))`: `|𝒞| = 6`, second class of four trees
    obtain ⟨c6, c4⟩ := hb (by rw [hτ]; decide +kernel)
    have hs := (ac2_balanced_P6_shape τ' hR').1 ⟨by rw [← hC]; exact c6, by rw [← hC2]; exact c4⟩
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
`abc|de`): two species trees whose unrooted trees are `U5 2`, with the same unrooted gene tree
distribution, have the same rooted metric tree. If both are binary, this is Proposition 8; if one
of them has a polytomy (`P₅` or `P₆`), its shape, labelling and lengths are determined as in
`ac2_rootings_two_polytomy`. -/
theorem ac2_rootings_two (τ τ' : SpeciesTree (Fin 5)) (hk : unroot τ.clusters = U5 2)
    (hk' : unroot τ'.clusters = U5 2) (h : τ.unrootedDist id = τ'.unrootedDist id) :
    τ.SameRootedMetricTree τ' := by
  have hR := classify_mem_rootings5 τ 2 (by simp) hk
  have hR' := classify_mem_rootings5 τ' 2 (by simp) hk'
  by_cases hn : τ.clusters ∈ ac2_polytomies
  · exact ac2_rootings_two_polytomy τ τ' hn hR' h
  by_cases hn' : τ'.clusters ∈ ac2_polytomies
  · exact (ac2_rootings_two_polytomy τ' τ hn' hR h.symm).symm
  -- both trees are binary: Proposition 8
  exact proposition8 (Fintype.card_fin 5) τ τ' (ac2_isBinary hR hn) (ac2_isBinary hR' hn') h

/-! ### `P₅` versus `P₇` -/

/-- The gene trees neither in the least probable class nor most probable. For `P₅` and `P₇` these
are the trees of the two 2-element classes, or of the 4-element class into which they can merge. -/
noncomputable def ac2_middle (τ : SpeciesTree (Fin 5)) : Finset ℕ :=
  (Icc 1 15).filter fun i => i ∉ cls_leastClass τ ∧ i ∉ cls_mostProbable τ

/-- The number of pairs of gene trees `T_i`, `T_j` (`i < j` in `S`) with a cherry in common. -/
def ac2_cherryPairs (S : Finset ℕ) : ℕ :=
  #((S ×ˢ S).filter fun p => p.1 < p.2 ∧ (cls_cherries (T5 p.1) ∩ cls_cherries (T5 p.2)).Nonempty)

/-- `ac2_middle` depends only on the distribution. -/
theorem ac2_middle_congr {τ τ' : SpeciesTree (Fin 5)}
    (h : τ.unrootedDist id = τ'.unrootedDist id) : ac2_middle τ = ac2_middle τ' := by
  unfold ac2_middle
  rw [cls_leastClass_congr h, cls_mostProbable_congr h]

/-- Appendix C, `|𝒞| = 10`: `P₅ = ((a,b),(d,e),c)` and `P₇ = (((a,b),d,e),c)` are told apart "by
considering the two 2-element classes for both". For `P₅`, the trees of each of the classes
`{T₂, T₃}` and `{T₄, T₁₃}` have a cherry in common; for `P₇`, those of `{T₂, T₃}` have a cherry in
common, those of `{T₈, T₁₁}` do not. The two classes can merge into one 4-element class
(`appendixC_degenerate`); in all cases their union is `ac2_middle`, the trees neither least nor
most probable, and "counting the number of trees with a cherry in common in the larger degenerate
class" gives two pairs for `P₅` and one for `P₇`. -/
theorem ac2_P5_P7_rule (σ : SpeciesTree (Fin 5)) :
    (σ.clusters = polytomy5 5 →
      ac2_middle σ = {2, 3, 4, 13} ∧ u σ 2 = u σ 3 ∧ u σ 4 = u σ 13 ∧
        (cls_cherries (T5 2) ∩ cls_cherries (T5 3)).Nonempty ∧
        (cls_cherries (T5 4) ∩ cls_cherries (T5 13)).Nonempty ∧
        ac2_cherryPairs (ac2_middle σ) = 2) ∧
    (σ.clusters = polytomy5 7 →
      ac2_middle σ = {2, 3, 8, 11} ∧ u σ 2 = u σ 3 ∧ u σ 8 = u σ 11 ∧
        (cls_cherries (T5 2) ∩ cls_cherries (T5 3)).Nonempty ∧
        cls_cherries (T5 8) ∩ cls_cherries (T5 11) = ∅ ∧
        ac2_cherryPairs (ac2_middle σ) = 1) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- `P₅`: Table 7 and the inequalities `u₁ > u₂, u₄ > u₅` of Table 6
    obtain ⟨h12, h14, h25, h45⟩ := (table6 σ).2.2.2.1 h
    obtain ⟨-, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ :=
      rootingDist5_2_7 σ h
    have q3 : u σ 3 = u σ 2 := by rw [e3, e2]
    have q13 : u σ 13 = u σ 4 := by rw [e13, e4]
    have hL : cls_leastClass σ = {5, 6, 7, 8, 9, 10, 11, 12, 14, 15} := by
      refine ac2_leastClass_eq (m := 5) (by decide) (by decide) ?_ ?_
      · intro i hi
        simp only [mem_insert, mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [e5, e6, e7, e8, e9, e10, e11, e12, e14, e15]
      · intro i hi hiC
        obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
        interval_cases i <;> first | exact (hiC (by decide)).elim | linarith
    have hM : cls_mostProbable σ = {1} := by
      refine ac2_mostProbable_eq (m := 1) (by decide) (by decide) ?_ ?_
      · intro i hi
        rw [mem_singleton.1 hi]
      · intro i hi hiC
        obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
        interval_cases i <;> first | exact (hiC (by decide)).elim | linarith
    have hmid : ac2_middle σ = {2, 3, 4, 13} := by
      unfold ac2_middle
      rw [hL, hM]
      decide
    refine ⟨hmid, q3.symm, q13.symm, by decide, by decide, ?_⟩
    rw [hmid]
    decide
  · -- `P₇`: Table 7 and the inequalities `u₁ > u₂, u₈ > u₄` of Table 6
    obtain ⟨h12, h18, h24, h84⟩ := (table6 σ).2.2.2.2.2.1 h
    obtain ⟨-, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ :=
      rootingDist5_1_5 σ h
    have q3 : u σ 3 = u σ 2 := by rw [e3, e2]
    have q11 : u σ 11 = u σ 8 := by rw [e11, e8]
    have hL : cls_leastClass σ = {4, 5, 6, 7, 9, 10, 12, 13, 14, 15} := by
      refine ac2_leastClass_eq (m := 4) (by decide) (by decide) ?_ ?_
      · intro i hi
        simp only [mem_insert, mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [e4, e5, e6, e7, e9, e10, e12, e13, e14, e15]
      · intro i hi hiC
        obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
        interval_cases i <;> first | exact (hiC (by decide)).elim | linarith
    have hM : cls_mostProbable σ = {1} := by
      refine ac2_mostProbable_eq (m := 1) (by decide) (by decide) ?_ ?_
      · intro i hi
        rw [mem_singleton.1 hi]
      · intro i hi hiC
        obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
        interval_cases i <;> first | exact (hiC (by decide)).elim | linarith
    have hmid : ac2_middle σ = {2, 3, 8, 11} := by
      unfold ac2_middle
      rw [hL, hM]
      decide
    refine ⟨hmid, q3.symm, q11.symm, by decide, by decide, ?_⟩
    rw [hmid]
    decide

/-- The rule of `ac2_P5_P7_rule` separates `P₅` from `P₇`: the number of pairs of trees with a
cherry in common in `ac2_middle`, a function of the distribution, is `2` for `P₅` and `1` for
`P₇`. -/
theorem ac2_P5_P7_distinguish {σ σ' : SpeciesTree (Fin 5)} (hσ : σ.clusters = polytomy5 5)
    (hσ' : σ'.clusters = polytomy5 7) : σ.unrootedDist id ≠ σ'.unrootedDist id := by
  intro h
  have := congrArg ac2_cherryPairs (ac2_middle_congr h)
  rw [((ac2_P5_P7_rule σ).1 hσ).2.2.2.2.2, ((ac2_P5_P7_rule σ').2 hσ').2.2.2.2.2] at this
  exact absurd this (by decide)

end ADR11
