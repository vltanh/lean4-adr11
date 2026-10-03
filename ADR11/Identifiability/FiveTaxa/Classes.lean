module

public import ADR11.SmallTrees
public import ADR11.MSC.Relabel

/-!
# Classes of five-taxon gene trees

The paper's arguments on five taxa (the proof of Proposition 7, and Appendix C for nonbinary
species trees) read the shape and the labelling of the species tree off the classes of unrooted
gene trees with equal probabilities: the least probable class, the class with the second smallest
probability, the most probable trees, and the cherries of the trees of a class. This module
defines them as functions of the distribution `u τ` (`u τ i = ℙ_τ(T_i)`), and transports
probabilities along relabellings of the taxa ("permuting labels", l. 319 of the paper).

* `cls_leastClass τ`, `cls_secondClass τ`, `cls_mostProbable τ`: the indices `i ∈ [1, 15]` of
  the gene trees `T_i` of least probability, of the second smallest probability, and of greatest
  probability.
* `cls_leastClass_congr`, `cls_secondClass_congr`, `cls_mostProbable_congr`: they depend only on
  the distribution.
* `cls_u_relabel`: relabelling the taxa by `π` permutes the gene tree probabilities:
  `u (τ.relabel π) j = u τ i` when `π` maps `T_i` to `T_j`.
* `cls_cherries T`: the cherries of an unrooted 5-taxon tree (its 2-element split sides);
  `cls_partners c S`: the taxa that form a cherry with `c` in some tree `T_i`, `i ∈ S`.
* `cls_mem_leastClass`, `cls_mem_secondClass`, `cls_mem_mostProbable`: membership in the classes.
* `cls_u_relabel_symm`: the same transport, read from the relabelled tree back to `τ`.
* `cls_leastClass_relabel`, `cls_secondClass_relabel`, `cls_mostProbable_relabel`: if `π` maps
  each `T_i` to `T_{p i}` (and every `T_j` is such an image), the classes of `τ` are the images
  under `p` of those of `τ` relabelled by `π⁻¹`.
* `cls_not_mem_leastClass_iff`, `cls_secondClass_eq_filter`: membership in the least probable
  class and the second class, compared with the probability of a member `m` of the least probable
  class (the form of `balanced_extremeClasses` and `caterpillar_extremeClasses`).
-/

@[expose] public section

namespace ADR11

open Finset

open scoped Classical in
/-- The least probable class: the indices `i ∈ [1, 15]` of the gene trees `T_i` of least
probability. -/
noncomputable def cls_leastClass (τ : SpeciesTree (Fin 5)) : Finset ℕ :=
  {i ∈ Icc 1 15 | ∀ j ∈ Icc 1 15, u τ i ≤ u τ j}

open scoped Classical in
/-- The class with the second smallest probability: the indices outside the least probable class
whose probability is least among them. -/
noncomputable def cls_secondClass (τ : SpeciesTree (Fin 5)) : Finset ℕ :=
  {i ∈ Icc 1 15 | i ∉ cls_leastClass τ ∧ ∀ j ∈ Icc 1 15, j ∉ cls_leastClass τ → u τ i ≤ u τ j}

open scoped Classical in
/-- The most probable gene trees: the indices `i ∈ [1, 15]` of greatest probability. -/
noncomputable def cls_mostProbable (τ : SpeciesTree (Fin 5)) : Finset ℕ :=
  {i ∈ Icc 1 15 | ∀ j ∈ Icc 1 15, u τ j ≤ u τ i}

theorem cls_u_congr {τ τ' : SpeciesTree (Fin 5)}
    (h : τ.unrootedDist id = τ'.unrootedDist id) (i : ℕ) : u τ i = u τ' i := by
  unfold u
  rw [h]

theorem cls_leastClass_congr {τ τ' : SpeciesTree (Fin 5)}
    (h : τ.unrootedDist id = τ'.unrootedDist id) : cls_leastClass τ = cls_leastClass τ' := by
  ext i
  simp only [cls_leastClass, mem_filter, cls_u_congr h]

theorem cls_secondClass_congr {τ τ' : SpeciesTree (Fin 5)}
    (h : τ.unrootedDist id = τ'.unrootedDist id) : cls_secondClass τ = cls_secondClass τ' := by
  ext i
  simp only [cls_secondClass, mem_filter, cls_leastClass_congr h, cls_u_congr h]

theorem cls_mostProbable_congr {τ τ' : SpeciesTree (Fin 5)}
    (h : τ.unrootedDist id = τ'.unrootedDist id) : cls_mostProbable τ = cls_mostProbable τ' := by
  ext i
  simp only [cls_mostProbable, mem_filter, cls_u_congr h]

/-- Relabelling the taxa permutes the gene tree probabilities: if `π` maps `T_i` to `T_j`, then
`T_j` has the same probability under the relabelled species tree as `T_i` under `τ`. -/
theorem cls_u_relabel (τ : SpeciesTree (Fin 5)) (π : Fin 5 ≃ Fin 5) {i j : ℕ}
    (h : relabelFamily π (T5 i) = T5 j) : u (τ.relabel π) j = u τ i := by
  unfold u
  rw [← h, SpeciesTree.unrootedDist_relabel]

/-- The cherries of an unrooted tree on five taxa: the sides of its splits with two taxa. -/
def cls_cherries (T : Finset (Finset (Fin 5))) : Finset (Finset (Fin 5)) :=
  T.filter fun A => #A = 2

/-- The taxa that form a cherry with `c` in some gene tree `T_i`, `i ∈ S`. -/
def cls_partners (c : Fin 5) (S : Finset ℕ) : Finset (Fin 5) :=
  univ.filter fun x => x ≠ c ∧ ∃ i ∈ S, ({c, x} : Finset (Fin 5)) ∈ cls_cherries (T5 i)

/-! ### Membership in the classes -/

theorem cls_mem_leastClass {τ : SpeciesTree (Fin 5)} {i : ℕ} :
    i ∈ cls_leastClass τ ↔ i ∈ Icc 1 15 ∧ ∀ j ∈ Icc 1 15, u τ i ≤ u τ j := by
  simp only [cls_leastClass, mem_filter]

theorem cls_mem_secondClass {τ : SpeciesTree (Fin 5)} {i : ℕ} :
    i ∈ cls_secondClass τ ↔ i ∈ Icc 1 15 ∧ i ∉ cls_leastClass τ ∧
      ∀ j ∈ Icc 1 15, j ∉ cls_leastClass τ → u τ i ≤ u τ j := by
  simp only [cls_secondClass, mem_filter]

theorem cls_mem_mostProbable {τ : SpeciesTree (Fin 5)} {i : ℕ} :
    i ∈ cls_mostProbable τ ↔ i ∈ Icc 1 15 ∧ ∀ j ∈ Icc 1 15, u τ j ≤ u τ i := by
  simp only [cls_mostProbable, mem_filter]

/-! ### Relabelling the taxa permutes the classes -/

/-- Relabelling back: if `π` maps `T_i` to `T_j`, then `T_j` has the same probability under `τ`
as `T_i` under `τ` relabelled by `π⁻¹`. -/
theorem cls_u_relabel_symm (τ : SpeciesTree (Fin 5)) (π : Fin 5 ≃ Fin 5) {i j : ℕ}
    (h : relabelFamily π (T5 i) = T5 j) : u τ j = u (τ.relabel π.symm) i := by
  have := cls_u_relabel (τ.relabel π.symm) π h
  rwa [show (τ.relabel π.symm).relabel π = τ by simpa using τ.relabel_relabel_symm π.symm]
    at this

section IndexMap

/-! In this section `π` maps each gene tree `T_i` (`i ∈ [1, 15]`) to `T_{p i}`, and every `T_j` is
such an image. -/

variable (τ : SpeciesTree (Fin 5)) (π : Fin 5 ≃ Fin 5) {p : ℕ → ℕ}
  (hp : ∀ i ∈ Icc 1 15, p i ∈ Icc 1 15 ∧ relabelFamily π (T5 i) = T5 (p i))
  (hs : ∀ j ∈ Icc 1 15, ∃ i ∈ Icc 1 15, p i = j)

include hp hs in
/-- `T_{p i}` is in the least probable class of `τ` iff `T_i` is in that of `τ` relabelled by
`π⁻¹`. -/
theorem cls_mem_leastClass_relabel_iff {i : ℕ} (hi : i ∈ Icc 1 15) :
    p i ∈ cls_leastClass τ ↔ i ∈ cls_leastClass (τ.relabel π.symm) := by
  have hu : ∀ k ∈ Icc 1 15, u τ (p k) = u (τ.relabel π.symm) k := fun k hk =>
    cls_u_relabel_symm τ π (hp k hk).2
  rw [cls_mem_leastClass, cls_mem_leastClass]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hi, fun l hl => ?_⟩
    rw [← hu i hi, ← hu l hl]
    exact h _ (hp l hl).1
  · rintro ⟨-, h⟩
    refine ⟨(hp i hi).1, fun k hk => ?_⟩
    obtain ⟨l, hl, rfl⟩ := hs k hk
    rw [hu i hi, hu l hl]
    exact h l hl

include hp hs in
/-- The least probable class of `τ` is the image under `p` of that of `τ` relabelled by `π⁻¹`. -/
theorem cls_leastClass_relabel :
    cls_leastClass τ = (cls_leastClass (τ.relabel π.symm)).image p := by
  ext j
  rw [mem_image]
  constructor
  · intro hj
    obtain ⟨i, hi, rfl⟩ := hs j (cls_mem_leastClass.1 hj).1
    exact ⟨i, (cls_mem_leastClass_relabel_iff τ π hp hs hi).1 hj, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact (cls_mem_leastClass_relabel_iff τ π hp hs (cls_mem_leastClass.1 hi).1).2 hi

include hp hs in
/-- The class of the second smallest probability of `τ` is the image under `p` of that of `τ`
relabelled by `π⁻¹`. -/
theorem cls_secondClass_relabel :
    cls_secondClass τ = (cls_secondClass (τ.relabel π.symm)).image p := by
  have hu : ∀ k ∈ Icc 1 15, u τ (p k) = u (τ.relabel π.symm) k := fun k hk =>
    cls_u_relabel_symm τ π (hp k hk).2
  have hL : ∀ i ∈ Icc 1 15,
      (p i ∈ cls_leastClass τ ↔ i ∈ cls_leastClass (τ.relabel π.symm)) := fun i hi =>
    cls_mem_leastClass_relabel_iff τ π hp hs hi
  ext j
  rw [mem_image]
  simp only [cls_mem_secondClass]
  constructor
  · rintro ⟨hj, hjL, h⟩
    obtain ⟨i, hi, rfl⟩ := hs j hj
    refine ⟨i, ⟨hi, fun hiL => hjL ((hL i hi).2 hiL), fun l hl hlL => ?_⟩, rfl⟩
    rw [← hu i hi, ← hu l hl]
    exact h _ (hp l hl).1 fun h' => hlL ((hL l hl).1 h')
  · rintro ⟨i, ⟨hi, hiL, h⟩, rfl⟩
    refine ⟨(hp i hi).1, fun h' => hiL ((hL i hi).1 h'), fun k hk hkL => ?_⟩
    obtain ⟨l, hl, rfl⟩ := hs k hk
    rw [hu i hi, hu l hl]
    exact h l hl fun h' => hkL ((hL l hl).2 h')

include hp hs in
/-- The most probable trees of `τ` are the images under `p` of those of `τ` relabelled by
`π⁻¹`. -/
theorem cls_mostProbable_relabel :
    cls_mostProbable τ = (cls_mostProbable (τ.relabel π.symm)).image p := by
  have hu : ∀ k ∈ Icc 1 15, u τ (p k) = u (τ.relabel π.symm) k := fun k hk =>
    cls_u_relabel_symm τ π (hp k hk).2
  ext j
  rw [mem_image]
  simp only [cls_mem_mostProbable]
  constructor
  · rintro ⟨hj, h⟩
    obtain ⟨i, hi, rfl⟩ := hs j hj
    refine ⟨i, ⟨hi, fun l hl => ?_⟩, rfl⟩
    rw [← hu i hi, ← hu l hl]
    exact h _ (hp l hl).1
  · rintro ⟨i, ⟨hi, h⟩, rfl⟩
    refine ⟨(hp i hi).1, fun k hk => ?_⟩
    obtain ⟨l, hl, rfl⟩ := hs k hk
    rw [hu i hi, hu l hl]
    exact h l hl

end IndexMap

/-! ### The least probable class and the next one -/

/-- Outside the least probable class, the probability exceeds that of any member `m` of it. -/
theorem cls_not_mem_leastClass_iff {τ : SpeciesTree (Fin 5)} {m i : ℕ}
    (hm : m ∈ cls_leastClass τ) (hi : i ∈ Icc 1 15) :
    i ∉ cls_leastClass τ ↔ u τ m < u τ i := by
  rw [cls_mem_leastClass] at hm ⊢
  constructor
  · intro h
    by_contra hle
    exact h ⟨hi, fun j hj => (not_lt.1 hle).trans (hm.2 j hj)⟩
  · rintro hlt ⟨-, h⟩
    exact absurd (h m hm.1) (not_le.2 hlt)

open scoped Classical in
/-- The class of the second smallest probability: the trees of least probability among those
more probable than a member `m` of the least probable class. -/
theorem cls_secondClass_eq_filter {τ : SpeciesTree (Fin 5)} {m : ℕ}
    (hm : m ∈ cls_leastClass τ) :
    cls_secondClass τ =
      {i ∈ Icc 1 15 | u τ m < u τ i ∧ ∀ j ∈ Icc 1 15, u τ m < u τ j → u τ i ≤ u τ j} := by
  ext i
  simp only [cls_mem_secondClass, mem_filter]
  constructor
  · rintro ⟨hi, hni, h⟩
    exact ⟨hi, (cls_not_mem_leastClass_iff hm hi).1 hni,
      fun j hj hj' => h j hj ((cls_not_mem_leastClass_iff hm hj).2 hj')⟩
  · rintro ⟨hi, hlt, h⟩
    exact ⟨hi, (cls_not_mem_leastClass_iff hm hi).2 hlt,
      fun j hj hj' => h j hj ((cls_not_mem_leastClass_iff hm hj).1 hj')⟩

end ADR11
