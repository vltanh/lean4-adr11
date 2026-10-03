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

end ADR11
