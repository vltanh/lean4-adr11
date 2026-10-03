module

public import ADR11.SmallTrees
public import ADR11.Computation.FourTaxa
public import ADR11.Introduction.Counts
public import ADR11.Rootings.Support

/-!
# Section 4.1: four taxa

With four taxa `a, b, c, d` (`Fin 4`), the unrooted gene trees are `T_{AB|CD}`, `T_{AC|BD}` and
`T_{AD|BC}` (`treeOfClusters {{0,1}}`, `treeOfClusters {{0,2}}`, `treeOfClusters {{0,3}}`).

* `fourTaxa_card_shapes`: of the 15 rooted binary species tree topologies on four taxa, three are
  labelled balanced trees and twelve are labelled caterpillars.
* `fourTaxa_balanced`, `fourTaxa_caterpillar`: the unrooted gene tree distributions of the
  balanced species tree `((a,b):x,(c,d):y)` and of the rooted caterpillar `(((a,b):x,c):y,d)`.
* `fourTaxa_sameDistribution`: the five rooted species trees `(((a,b):x,c):y₁,d)`,
  `(((a,b):x,d):y₂,c)`, `(((c,d):x,a):y₃,b)`, `(((c,d):x,b):y₄,a)` and `((a,b):z,(c,d):x-z)`
  give the same unrooted gene tree distribution.
* `fourTaxa_recovery` and `proposition3` are in `ADR11.Identifiability.Proposition3`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

open scoped Classical in
/-- Section 4.1 (l.319): "Of the 15 possibilities for `ψ⁺`, there are three labeled balanced tree
topologies, and 12 labeled caterpillar topologies." Among the rooted binary trees on four taxa
(`IsBinaryHierarchy`, counted by `section1_card_rooted`), three are balanced (two clusters of size
2) and twelve are caterpillars (a cluster of size 2 inside a cluster of size 3).

Proof: every rooted binary tree on `Fin 4` is one of the code lists `root_binEnum 3 15`
(`root_binEnum_complete_univ`), all of which are rooted binary trees (`root_binHierB`); the two
counts are computed on this list by `decide`. -/
theorem fourTaxa_card_shapes :
    #{G : Finset (Finset (Fin 4)) | IsBinaryHierarchy G} = 15 ∧
    #{G : Finset (Finset (Fin 4)) | IsBinaryHierarchy G ∧
        ∃ A ∈ G, ∃ B ∈ G, #A = 2 ∧ #B = 2 ∧ A ≠ B} = 3 ∧
    #{G : Finset (Finset (Fin 4)) | IsBinaryHierarchy G ∧
        ∃ A ∈ G, ∃ B ∈ G, #A = 2 ∧ #B = 3 ∧ A ⊆ B} = 12 := by
  have hB : ∀ l ∈ root_binEnum 3 15, root_binHierB 4 l = true := by decide +kernel
  -- the rooted binary trees on `Fin 4` are the trees of the enumeration
  have hE : ∀ G : Finset (Finset (Fin 4)),
      IsBinaryHierarchy G ↔ G ∈ ((root_binEnum 3 15).map (Computation.decF 4)).toFinset := by
    intro G
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨⟨hu, -, hne, hlam⟩, hbin⟩
      exact root_binEnum_complete_univ ⟨hu, fun A _ => subset_univ A, hne, hlam, hbin⟩
    · rintro ⟨l, hl, rfl⟩
      exact root_isBinHier_of_binHierB (hB l hl)
  refine ⟨?_, ?_, ?_⟩
  · rw [section1_card_rooted 4 (by norm_num)]
    rfl
  · calc #{G : Finset (Finset (Fin 4)) | IsBinaryHierarchy G ∧
            ∃ A ∈ G, ∃ B ∈ G, #A = 2 ∧ #B = 2 ∧ A ≠ B}
        = #(((root_binEnum 3 15).map (Computation.decF 4)).toFinset.filter
            fun G => ∃ A ∈ G, ∃ B ∈ G, #A = 2 ∧ #B = 2 ∧ A ≠ B) := by
          congr 1
          ext G
          simp only [mem_filter, mem_univ, true_and, hE]
      _ = 3 := by decide +kernel
  · calc #{G : Finset (Finset (Fin 4)) | IsBinaryHierarchy G ∧
            ∃ A ∈ G, ∃ B ∈ G, #A = 2 ∧ #B = 3 ∧ A ⊆ B}
        = #(((root_binEnum 3 15).map (Computation.decF 4)).toFinset.filter
            fun G => ∃ A ∈ G, ∃ B ∈ G, #A = 2 ∧ #B = 3 ∧ A ⊆ B) := by
          congr 1
          ext G
          simp only [mem_filter, mem_univ, true_and, hE]
      _ = 12 := by decide +kernel

/-- Section 4.1: for the balanced species tree `((a,b):x,(c,d):y)`,
`ℙ(T_{AB|CD}) = 1 - (2/3) e^{-(x+y)}` and `ℙ(T_{AC|BD}) = ℙ(T_{AD|BC}) = (1/3) e^{-(x+y)}`. -/
theorem fourTaxa_balanced (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters = balanced4) :
    σ.unrootedDist id (treeOfClusters {{0, 1}}) =
        1 - 2 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id (treeOfClusters {{0, 2}}) =
        1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id (treeOfClusters {{0, 3}}) =
        1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) := by
  have h := Computation.unrootedDist_bal4 σ hσ
  refine ⟨?_, ?_, ?_⟩
  · rw [h, Computation.ite₃_eq_first]
  · rw [h, Computation.ite₃_eq_second _ _ _ _ Computation.quartet_ne_01_02]
  · rw [h, Computation.ite₃_eq_third _ _ _ Computation.quartet_ne_01_03
      Computation.quartet_ne_02_03]

/-- Section 4.1: for the rooted caterpillar species tree `(((a,b):x,c):y,d)`,
`ℙ(T_{AB|CD}) = 1 - (2/3) e^{-x}` and `ℙ(T_{AC|BD}) = ℙ(T_{AD|BC}) = (1/3) e^{-x}`. -/
theorem fourTaxa_caterpillar (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters = caterpillar4) :
    σ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 * exp (-σ.length {0, 1}) := by
  have h := Computation.unrootedDist_cat4_0123 σ hσ
  refine ⟨?_, ?_, ?_⟩
  · rw [h, Computation.ite₃_eq_first]
  · rw [h, Computation.ite₃_eq_second _ _ _ _ Computation.quartet_ne_01_02]
  · rw [h, Computation.ite₃_eq_third _ _ _ Computation.quartet_ne_01_03
      Computation.quartet_ne_02_03]

/-- Section 4.1: for `x > 0`, `yᵢ > 0` and `x > z > 0`, the rooted species trees
`(((a,b):x,c):y₁,d)`, `(((a,b):x,d):y₂,c)`, `(((c,d):x,a):y₃,b)`, `(((c,d):x,b):y₄,a)` and
`((a,b):z,(c,d):x-z)` produce the same unrooted gene tree distribution. The trees are given by
their clusters and the lengths of their internal edges. -/
theorem fourTaxa_sameDistribution (σ₁ σ₂ σ₃ σ₄ σ₅ : SpeciesTree (Fin 4))
    (h₁ : σ₁.clusters = hierarchyOf {{0, 1}, {0, 1, 2}})
    (h₂ : σ₂.clusters = hierarchyOf {{0, 1}, {0, 1, 3}})
    (h₃ : σ₃.clusters = hierarchyOf {{2, 3}, {0, 2, 3}})
    (h₄ : σ₄.clusters = hierarchyOf {{2, 3}, {1, 2, 3}})
    (h₅ : σ₅.clusters = hierarchyOf {{0, 1}, {2, 3}})
    (hx₂ : σ₂.length {0, 1} = σ₁.length {0, 1}) (hx₃ : σ₃.length {2, 3} = σ₁.length {0, 1})
    (hx₄ : σ₄.length {2, 3} = σ₁.length {0, 1})
    (hx₅ : σ₅.length {0, 1} + σ₅.length {2, 3} = σ₁.length {0, 1}) :
    σ₂.unrootedDist id = σ₁.unrootedDist id ∧ σ₃.unrootedDist id = σ₁.unrootedDist id ∧
      σ₄.unrootedDist id = σ₁.unrootedDist id ∧ σ₅.unrootedDist id = σ₁.unrootedDist id := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext U
  · rw [Computation.unrootedDist_cat4_0132 σ₂ h₂ U, Computation.unrootedDist_cat4_0123 σ₁ h₁ U,
      hx₂]
  · rw [Computation.unrootedDist_cat4_2301 σ₃ h₃ U, Computation.unrootedDist_cat4_0123 σ₁ h₁ U,
      hx₃]
  · rw [Computation.unrootedDist_cat4_2310 σ₄ h₄ U, Computation.unrootedDist_cat4_0123 σ₁ h₁ U,
      hx₄]
  · rw [Computation.unrootedDist_bal4 σ₅ h₅ U, Computation.unrootedDist_cat4_0123 σ₁ h₁ U, hx₅]

end ADR11
