module

public import ADR11.Identifiability.FiveTaxa.Classes
public import ADR11.Trees.Classify
public import ADR11.FiveTaxa.Balanced
public import ADR11.FiveTaxa.Caterpillar
public import ADR11.FiveTaxa.Pseudocaterpillar

/-!
# The binary rootings of `ab|cde, abc|de` and their classes of gene trees

The proof of Proposition 7 (`prop:cases`) names the taxa so that the unrooted species tree `ψ⁻`
has the splits `ab|cde` and `abc|de` (`U5 2`). The rooted tree `ψ⁺` is then one of the seven
binary rootings of `U5 2` (`binaryRootings5`): the four caterpillars `((((a,b),c),d),e)`,
`((((a,b),c),e),d)`, `((((d,e),c),b),a)`, `((((d,e),c),a),b)`, the two balanced trees
`(((a,b),c),(d,e))`, `((a,b),(c,(d,e)))`, and the pseudocaterpillar `(((a,b),(d,e)),c)`. This
module computes, for each of them, the classes of gene trees that the proof reads off the
distribution. The classes of the representatives of Section 4.2 come from the inequalities
(4)–(6) (`caterpillar_extremeClasses`, `balanced_extremeClasses`, `pseudocaterpillar_minClass`);
those of the other labellings by permuting labels (`cls_leastClass_relabel`,
`cls_secondClass_relabel`).

* `p78_swap`, `p78_flip`: the relabellings `d ↔ e` and `a ↔ e, b ↔ d`; `p78_swapIdx`,
  `p78_flipIdx`: the permutations of the gene trees `T₁, …, T₁₅` that they induce.
* `p78_caterpillars`, `p78_balanced`: the caterpillar and the balanced rootings of `U5 2`;
  `p78_shapes`: every binary rooting of `U5 2` is one of them or the pseudocaterpillar.
* `p78_classes_cat0`, …, `p78_classes_cat3`, `p78_classes_bal0`, `p78_classes_bal1`,
  `p78_leastClass_pse`: the least probable class and the class of the second smallest
  probability of each rooting.
* `p78_card_caterpillar`, `p78_card_balanced`, `p78_card_pseudocaterpillar`: the least probable
  class has 6 elements for the caterpillars and the balanced trees and 8 for the
  pseudocaterpillar; the second class has 2 elements for the caterpillars and 4 for the balanced
  trees.
* `p78_mem_leastClass_seven_iff`: `T₇` lies in the least probable class of `(((a,b),c),(d,e))` but
  not of `((a,b),(c,(d,e)))`; `p78_balanced_eq`: the balanced case of Proposition 7.
* `p78_twoClade`: the 2-clade of a caterpillar is the set of taxa in cherries with `c` in the two
  trees of the second class; `p78_sign_cat0`, …, `p78_sign_cat3`: `ℙ(T₃) > ℙ(T₂)` on
  `((((a,b),c),d),e)` (inequality (5)) and its images; `p78_caterpillar_eq`: the caterpillar case
  of Proposition 7.
* `p78_exists_relabel_rep`: every binary 5-taxon species tree is, after relabelling, the balanced
  tree, the caterpillar or the pseudocaterpillar of Section 4.2 (the reduction in the proof of
  Proposition 8).
-/

@[expose] public section

namespace ADR11

open Finset

/-! ### Two relabellings of the taxa -/

/-- The relabelling `d ↔ e` of the taxa. -/
def p78_swap : Fin 5 ≃ Fin 5 := Equiv.swap 3 4

/-- The relabelling `a ↔ e`, `b ↔ d` of the taxa (`c` is fixed). -/
def p78_flip : Fin 5 ≃ Fin 5 := (Equiv.swap 0 4).trans (Equiv.swap 1 3)

/-- The permutation of the gene trees induced by `p78_swap`: it maps `T_i` to `T_{p78_swapIdx i}`
(`p78_swapIdx_spec`). -/
def p78_swapIdx : ℕ → ℕ
  | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | 7 => 10 | 10 => 7 | 8 => 11 | 11 => 8 | 9 => 12
  | 12 => 9 | 14 => 15 | 15 => 14 | i => i

/-- The permutation of the gene trees induced by `p78_flip`: it maps `T_i` to `T_{p78_flipIdx i}`
(`p78_flipIdx_spec`). -/
def p78_flipIdx : ℕ → ℕ
  | 2 => 4 | 4 => 2 | 3 => 13 | 13 => 3 | 5 => 7 | 7 => 5 | 6 => 14 | 14 => 6 | 9 => 15
  | 15 => 9 | 10 => 12 | 12 => 10 | i => i

theorem p78_swapIdx_spec : ∀ i ∈ Icc 1 15, p78_swapIdx i ∈ Icc 1 15 ∧
    relabelFamily p78_swap (T5 i) = T5 (p78_swapIdx i) := by
  decide +kernel

theorem p78_swapIdx_surj : ∀ j ∈ Icc 1 15, ∃ i ∈ Icc 1 15, p78_swapIdx i = j := by
  decide

theorem p78_flipIdx_spec : ∀ i ∈ Icc 1 15, p78_flipIdx i ∈ Icc 1 15 ∧
    relabelFamily p78_flip (T5 i) = T5 (p78_flipIdx i) := by
  decide +kernel

theorem p78_flipIdx_surj : ∀ j ∈ Icc 1 15, ∃ i ∈ Icc 1 15, p78_flipIdx i = j := by
  decide

/-- `d ↔ e` maps `((((a,b),c),d),e)` to `((((a,b),c),e),d)`. -/
theorem p78_swap_cat0 :
    relabelFamily p78_swap caterpillar5 = hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}} := by
  decide +kernel

/-- `a ↔ e, b ↔ d` maps `((((a,b),c),d),e)` to `((((d,e),c),b),a)`. -/
theorem p78_flip_cat0 :
    relabelFamily p78_flip caterpillar5 = hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}} := by
  decide +kernel

/-- `a ↔ e, b ↔ d` maps `((((a,b),c),e),d)` to `((((d,e),c),a),b)`. -/
theorem p78_flip_cat1 : relabelFamily p78_flip (hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}}) =
    hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}} := by
  decide +kernel

/-- `a ↔ e, b ↔ d` maps `(((a,b),c),(d,e))` to `((a,b),(c,(d,e)))`. -/
theorem p78_flip_bal0 :
    relabelFamily p78_flip balanced5 = hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}} := by
  decide +kernel

/-- Relabelling back: if `τ` is the relabelling by `π` of a tree with clusters `H`, then `τ`
relabelled by `π⁻¹` has the clusters `H`. -/
theorem p78_relabel_symm_clusters {τ : SpeciesTree (Fin 5)} {π : Fin 5 ≃ Fin 5}
    {H : Finset (Finset (Fin 5))} (hτ : τ.clusters = relabelFamily π H) :
    (τ.relabel π.symm).clusters = H := by
  rw [SpeciesTree.relabel_clusters, hτ, relabelFamily_symm]

/-! ### The shapes of the binary rootings of `ab|cde, abc|de` -/

/-- The caterpillar rootings of `U5 2`: `((((a,b),c),d),e)`, `((((a,b),c),e),d)` (2-clade
`{a,b}`), `((((d,e),c),b),a)` and `((((d,e),c),a),b)` (2-clade `{d,e}`). -/
def p78_caterpillars : Finset (Finset (Finset (Fin 5))) :=
  {hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}, hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}},
   hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}, hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}}}

/-- The balanced rootings of `U5 2`: `(((a,b),c),(d,e))` and `((a,b),(c,(d,e)))`. -/
def p78_balanced : Finset (Finset (Finset (Fin 5))) :=
  {hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}}, hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}}}

/-- A binary rooting of `ab|cde, abc|de` is a caterpillar, a balanced tree, or the
pseudocaterpillar `(((a,b),(d,e)),c)`. -/
theorem p78_shapes {H : Finset (Finset (Fin 5))} (hH : H ∈ binaryRootings5) :
    H ∈ p78_caterpillars ∨ H ∈ p78_balanced ∨ H = pseudocaterpillar5 := by
  simp only [binaryRootings5, mem_insert, mem_singleton] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by simp [p78_caterpillars])
  · exact Or.inl (by simp [p78_caterpillars])
  · exact Or.inl (by simp [p78_caterpillars])
  · exact Or.inl (by simp [p78_caterpillars])
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (by simp [p78_balanced]))
  · exact Or.inr (Or.inl (by simp [p78_balanced]))

/-! ### The classes of the seven rootings -/

variable {τ : SpeciesTree (Fin 5)}

/-- Section 4.2.2: on the caterpillar `((((a,b),c),d),e)` the least probable class is
`{T₇, T₈, T₁₀, T₁₁, T₁₄, T₁₅}` and the class of the second smallest probability is
`{T₅, T₁₂}`. -/
theorem p78_classes_cat0 (hτ : τ.clusters = caterpillar5) :
    cls_leastClass τ = {7, 8, 10, 11, 14, 15} ∧ cls_secondClass τ = {5, 12} := by
  obtain ⟨h1, h2⟩ := caterpillar_extremeClasses τ hτ
  have hL : cls_leastClass τ = {7, 8, 10, 11, 14, 15} := h1
  refine ⟨hL, ?_⟩
  rw [cls_secondClass_eq_filter (m := 7) (by rw [hL]; decide)]
  exact h2

/-- The classes of `((((a,b),c),e),d)`, by permuting the labels `d ↔ e` in
`p78_classes_cat0`. -/
theorem p78_classes_cat1 (hτ : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}}) :
    cls_leastClass τ = {7, 8, 10, 11, 14, 15} ∧ cls_secondClass τ = {6, 9} := by
  have hρ := p78_classes_cat0 (p78_relabel_symm_clusters (hτ.trans p78_swap_cat0.symm))
  rw [cls_leastClass_relabel τ p78_swap p78_swapIdx_spec p78_swapIdx_surj,
    cls_secondClass_relabel τ p78_swap p78_swapIdx_spec p78_swapIdx_surj, hρ.1, hρ.2]
  decide

/-- The classes of `((((d,e),c),b),a)`, by permuting the labels `a ↔ e, b ↔ d` in
`p78_classes_cat0`. -/
theorem p78_classes_cat2 (hτ : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {7, 10} := by
  have hρ := p78_classes_cat0 (p78_relabel_symm_clusters (hτ.trans p78_flip_cat0.symm))
  rw [cls_leastClass_relabel τ p78_flip p78_flipIdx_spec p78_flipIdx_surj,
    cls_secondClass_relabel τ p78_flip p78_flipIdx_spec p78_flipIdx_surj, hρ.1, hρ.2]
  decide

/-- The classes of `((((d,e),c),a),b)`, by permuting the labels `a ↔ e, b ↔ d` in
`p78_classes_cat1`. -/
theorem p78_classes_cat3 (hτ : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {14, 15} := by
  have hρ := p78_classes_cat1 (p78_relabel_symm_clusters (hτ.trans p78_flip_cat1.symm))
  rw [cls_leastClass_relabel τ p78_flip p78_flipIdx_spec p78_flipIdx_surj,
    cls_secondClass_relabel τ p78_flip p78_flipIdx_spec p78_flipIdx_surj, hρ.1, hρ.2]
  decide

/-- Section 4.2.1: on the balanced tree `(((a,b),c),(d,e))` the least probable class is
`{T₇, T₈, T₁₀, T₁₁, T₁₄, T₁₅}` and the class of the second smallest probability is
`{T₅, T₆, T₉, T₁₂}`. -/
theorem p78_classes_bal0 (hτ : τ.clusters = balanced5) :
    cls_leastClass τ = {7, 8, 10, 11, 14, 15} ∧ cls_secondClass τ = {5, 6, 9, 12} := by
  obtain ⟨h1, h2, -⟩ := balanced_extremeClasses τ hτ
  have hL : cls_leastClass τ = {7, 8, 10, 11, 14, 15} := h1
  refine ⟨hL, ?_⟩
  rw [cls_secondClass_eq_filter (m := 7) (by rw [hL]; decide)]
  exact h2

/-- The classes of `((a,b),(c,(d,e)))`, by permuting the labels `a ↔ e, b ↔ d` in
`p78_classes_bal0`. -/
theorem p78_classes_bal1 (hτ : τ.clusters = hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {7, 10, 14, 15} := by
  have hρ := p78_classes_bal0 (p78_relabel_symm_clusters (hτ.trans p78_flip_bal0.symm))
  rw [cls_leastClass_relabel τ p78_flip p78_flipIdx_spec p78_flipIdx_surj,
    cls_secondClass_relabel τ p78_flip p78_flipIdx_spec p78_flipIdx_surj, hρ.1, hρ.2]
  decide

/-- Section 4.2.3: on the pseudocaterpillar `(((a,b),(d,e)),c)` the least probable class is
`{T₅, T₆, T₇, T₉, T₁₀, T₁₂, T₁₄, T₁₅}`. -/
theorem p78_leastClass_pse (hτ : τ.clusters = pseudocaterpillar5) :
    cls_leastClass τ = {5, 6, 7, 9, 10, 12, 14, 15} :=
  pseudocaterpillar_minClass τ hτ

/-! ### Proof of Proposition 7: the class sizes give the unlabelled shape -/

/-- For a caterpillar the least probable class has 6 elements, and the class of the second
smallest probability has 2. -/
theorem p78_card_caterpillar (hτ : τ.clusters ∈ p78_caterpillars) :
    #(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 2 := by
  simp only [p78_caterpillars, mem_insert, mem_singleton] at hτ
  rcases hτ with h | h | h | h
  · rw [(p78_classes_cat0 h).1, (p78_classes_cat0 h).2]; decide
  · rw [(p78_classes_cat1 h).1, (p78_classes_cat1 h).2]; decide
  · rw [(p78_classes_cat2 h).1, (p78_classes_cat2 h).2]; decide
  · rw [(p78_classes_cat3 h).1, (p78_classes_cat3 h).2]; decide

/-- For a balanced tree the least probable class has 6 elements, and the class of the second
smallest probability has 4. -/
theorem p78_card_balanced (hτ : τ.clusters ∈ p78_balanced) :
    #(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 4 := by
  simp only [p78_balanced, mem_insert, mem_singleton] at hτ
  rcases hτ with h | h
  · rw [(p78_classes_bal0 h).1, (p78_classes_bal0 h).2]; decide
  · rw [(p78_classes_bal1 h).1, (p78_classes_bal1 h).2]; decide

/-- For the pseudocaterpillar the least probable class has 8 elements. -/
theorem p78_card_pseudocaterpillar (hτ : τ.clusters = pseudocaterpillar5) :
    #(cls_leastClass τ) = 8 := by
  rw [p78_leastClass_pse hτ]
  decide

/-! ### Proof of Proposition 7: the balanced case -/

/-- `T₇` (splits `AD|BCE`, `ABD|CE`) lies in the least probable class of `(((a,b),c),(d,e))`, but
not in that of `((a,b),(c,(d,e)))`. -/
theorem p78_mem_leastClass_seven_iff (hτ : τ.clusters ∈ p78_balanced) :
    7 ∈ cls_leastClass τ ↔ τ.clusters = balanced5 := by
  simp only [p78_balanced, mem_insert, mem_singleton] at hτ
  rcases hτ with h | h
  · rw [(p78_classes_bal0 h).1]
    exact ⟨fun _ => h, fun _ => by decide⟩
  · rw [(p78_classes_bal1 h).1, h]
    exact ⟨fun h7 => absurd h7 (by decide), fun h' => absurd h' (by decide +kernel)⟩

/-- The balanced case of Proposition 7: the least probable class tells the two balanced rootings
apart, by `T₇`. -/
theorem p78_balanced_eq {τ τ' : SpeciesTree (Fin 5)} (hb : τ.clusters ∈ p78_balanced)
    (hb' : τ'.clusters ∈ p78_balanced) (hL : cls_leastClass τ = cls_leastClass τ') :
    τ.clusters = τ'.clusters := by
  have h7 := (p78_mem_leastClass_seven_iff hb).symm.trans
    ((iff_of_eq (congrArg (7 ∈ ·) hL)).trans (p78_mem_leastClass_seven_iff hb'))
  simp only [p78_balanced, mem_insert, mem_singleton] at hb hb'
  rcases hb with h | h <;> rcases hb' with h' | h'
  · rw [h, h']
  · exact absurd (h7.1 h) (by rw [h']; decide +kernel)
  · exact absurd (h7.2 h') (by rw [h]; decide +kernel)
  · rw [h, h']

/-! ### Proof of Proposition 7: the caterpillar case -/

/-- The 2-clade of a caterpillar rooting of `ab|cde, abc|de` is `{a,b}` or `{d,e}`, and it is the
set of taxa that appear in cherries with `c` in the two trees of the class of the second smallest
probability. -/
theorem p78_twoClade (hτ : τ.clusters ∈ p78_caterpillars) :
    (cls_partners 2 (cls_secondClass τ) = {0, 1} ∧
        (τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}} ∨
          τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}})) ∨
      (cls_partners 2 (cls_secondClass τ) = {3, 4} ∧
        (τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}} ∨
          τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}})) := by
  simp only [p78_caterpillars, mem_insert, mem_singleton] at hτ
  rcases hτ with h | h | h | h
  · exact Or.inl ⟨by rw [(p78_classes_cat0 h).2]; decide, Or.inl h⟩
  · exact Or.inl ⟨by rw [(p78_classes_cat1 h).2]; decide, Or.inr h⟩
  · exact Or.inr ⟨by rw [(p78_classes_cat2 h).2]; decide, Or.inl h⟩
  · exact Or.inr ⟨by rw [(p78_classes_cat3 h).2]; decide, Or.inr h⟩

/-- Inequality (5): `ℙ(T₃) > ℙ(T₂)` on `((((a,b),c),d),e)`. -/
theorem p78_sign_cat0 (hτ : τ.clusters = caterpillar5) : u τ 2 < u τ 3 :=
  (equation5 τ hτ).2.2.2.2.2.1

/-- `ℙ(T₂) > ℙ(T₃)` on `((((a,b),c),e),d)`: permuting the labels `d ↔ e` exchanges `T₂` and
`T₃`. -/
theorem p78_sign_cat1 (hτ : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}}) :
    u τ 3 < u τ 2 := by
  have hρ := p78_sign_cat0 (p78_relabel_symm_clusters (hτ.trans p78_swap_cat0.symm))
  rwa [cls_u_relabel_symm τ p78_swap (i := 2) (j := 3) (by decide +kernel),
    cls_u_relabel_symm τ p78_swap (i := 3) (j := 2) (by decide +kernel)]

/-- `ℙ(T₁₃) > ℙ(T₄)` on `((((d,e),c),b),a)`: permuting the labels `a ↔ e, b ↔ d` maps `T₂` to
`T₄` and `T₃` to `T₁₃`. -/
theorem p78_sign_cat2 (hτ : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}) :
    u τ 4 < u τ 13 := by
  have hρ := p78_sign_cat0 (p78_relabel_symm_clusters (hτ.trans p78_flip_cat0.symm))
  rwa [cls_u_relabel_symm τ p78_flip (i := 2) (j := 4) (by decide +kernel),
    cls_u_relabel_symm τ p78_flip (i := 3) (j := 13) (by decide +kernel)]

/-- `ℙ(T₄) > ℙ(T₁₃)` on `((((d,e),c),a),b)`, by permuting the labels `a ↔ e, b ↔ d` in
`p78_sign_cat1`. -/
theorem p78_sign_cat3 (hτ : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}}) :
    u τ 13 < u τ 4 := by
  have hρ := p78_sign_cat1 (p78_relabel_symm_clusters (hτ.trans p78_flip_cat1.symm))
  rwa [cls_u_relabel_symm τ p78_flip (i := 2) (j := 4) (by decide +kernel),
    cls_u_relabel_symm τ p78_flip (i := 3) (j := 13) (by decide +kernel)]

/-- The caterpillar case of Proposition 7: the taxa in cherries with `c` in the trees of the
second class give the 2-clade; with 2-clade `{a,b}`, the tree is `((((a,b),c),d),e)` if
`ℙ(T₃) > ℙ(T₂)` and `((((a,b),c),e),d)` if `ℙ(T₂) > ℙ(T₃)`, and with 2-clade `{d,e}` the same
holds after permuting the labels `a ↔ e, b ↔ d`. -/
theorem p78_caterpillar_eq {τ τ' : SpeciesTree (Fin 5)} (hc : τ.clusters ∈ p78_caterpillars)
    (hc' : τ'.clusters ∈ p78_caterpillars) (hS : cls_secondClass τ = cls_secondClass τ')
    (hu : ∀ i, u τ i = u τ' i) : τ.clusters = τ'.clusters := by
  rcases p78_twoClade hc with ⟨hP, h | h⟩ | ⟨hP, h | h⟩ <;>
    rcases p78_twoClade hc' with ⟨hP', h' | h'⟩ | ⟨hP', h' | h'⟩ <;>
    first
      | exact h.trans h'.symm
      | (rw [hS, hP'] at hP; exact absurd hP (by decide))
      | (have := p78_sign_cat0 h; have := p78_sign_cat1 h'; linarith [hu 2, hu 3])
      | (have := p78_sign_cat1 h; have := p78_sign_cat0 h'; linarith [hu 2, hu 3])
      | (have := p78_sign_cat2 h; have := p78_sign_cat3 h'; linarith [hu 4, hu 13])
      | (have := p78_sign_cat3 h; have := p78_sign_cat2 h'; linarith [hu 4, hu 13])

/-! ### The reduction to the representatives (proof of Proposition 8) -/

/-- Every binary species tree on five taxa is, after relabelling, the balanced tree
`(((a,b),c),(d,e))`, the caterpillar `((((a,b),c),d),e)` or the pseudocaterpillar
`(((a,b),(d,e)),c)`. -/
theorem p78_exists_relabel_rep {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 5)
    (σ : SpeciesTree X) (hσ : σ.IsBinary) :
    ∃ e : X ≃ Fin 5, (σ.relabel e).clusters = balanced5 ∨ (σ.relabel e).clusters = caterpillar5 ∨
      (σ.relabel e).clusters = pseudocaterpillar5 := by
  obtain ⟨e, he⟩ := exists_equiv_unroot_eq_U5_two_of_isBinary hX σ hσ
  have hR := mem_binaryRootings5 _ ((σ.isBinary_relabel_iff e.symm).2 hσ) he
  have key : ∀ (π : Fin 5 ≃ Fin 5) (H : Finset (Finset (Fin 5))),
      (σ.relabel e.symm).clusters = relabelFamily π H →
        (σ.relabel (e.symm.trans π.symm)).clusters = H := by
    intro π H h
    rw [SpeciesTree.relabel_clusters, ← classify_relabelFamily_trans,
      ← SpeciesTree.relabel_clusters, h, relabelFamily_symm]
  have h3 : relabelFamily (p78_swap.trans p78_flip) caterpillar5 =
      hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}} := by
    rw [← classify_relabelFamily_trans, p78_swap_cat0, p78_flip_cat1]
  simp only [binaryRootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h | h
  · exact ⟨e.symm, Or.inr (Or.inl h)⟩
  · exact ⟨_, Or.inr (Or.inl (key _ _ (h.trans p78_swap_cat0.symm)))⟩
  · exact ⟨_, Or.inr (Or.inl (key _ _ (h.trans p78_flip_cat0.symm)))⟩
  · exact ⟨_, Or.inr (Or.inl (key _ _ (h.trans h3.symm)))⟩
  · exact ⟨e.symm, Or.inr (Or.inr h)⟩
  · exact ⟨e.symm, Or.inl h⟩
  · exact ⟨_, Or.inl (key _ _ (h.trans p78_flip_bal0.symm))⟩

end ADR11
