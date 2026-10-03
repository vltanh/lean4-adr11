module

public import ADR11.SmallTrees
public import ADR11.Computation.ThreeTaxa

/-!
# Section 1: rooted gene trees

* `equation1`: for the 3-taxon species tree `((a,b):t,c)`, the rooted gene trees have
  probabilities `p₁ = 1 - (2/3) e^{-t}` and `p₂ = p₃ = (1/3) e^{-t}` [Nei 1987], so that the
  invariant `p₂ - p₃ = 0` of equation (1) holds; `p₁ > p₂`; and the invariant holds on the
  distribution of a binary 3-taxon species tree exactly when its topology is `((a,b),c)`.
* `introduction_tripleLength`: `t = -log((3/2)(1-p))` for the probability `p` of the rooted triple
  matching the species tree.
* `proposition1` and `corollary2` are in `ADR11.Introduction.Proposition1`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Equation (1) and the probabilities of rooted 3-taxon gene trees [Nei 1987]: for the species
tree `((a,b):t,c)`, `p₁ = ℙ((A,B),C) = 1 - (2/3)e^{-t}`, `p₂ = ℙ((A,C),B) = (1/3)e^{-t}`,
`p₃ = ℙ((B,C),A) = (1/3)e^{-t}`, hence `p₂ - p₃ = 0` and `p₁ > p₂`. -/
theorem equation1 (σ : SpeciesTree (Fin 3)) (hσ : σ.clusters = clusters3) :
    σ.rootedDist id (rootedTree3 {0, 1}) = 1 - 2 / 3 * exp (-σ.length {0, 1}) ∧
    σ.rootedDist id (rootedTree3 {0, 2}) = 1 / 3 * exp (-σ.length {0, 1}) ∧
    σ.rootedDist id (rootedTree3 {1, 2}) = 1 / 3 * exp (-σ.length {0, 1}) ∧
    σ.rootedDist id (rootedTree3 {0, 2}) - σ.rootedDist id (rootedTree3 {1, 2}) = 0 ∧
    σ.rootedDist id (rootedTree3 {0, 1}) > σ.rootedDist id (rootedTree3 {0, 2}) := by
  have h := Computation.rootedDist_three_01 σ hσ
  have h₁ : σ.rootedDist id (rootedTree3 {0, 1}) = 1 - 2 / 3 * exp (-σ.length {0, 1}) := by
    rw [h, Computation.ite₃_eq_first]
  have h₂ : σ.rootedDist id (rootedTree3 {0, 2}) = 1 / 3 * exp (-σ.length {0, 1}) := by
    rw [h, Computation.ite₃_eq_second _ _ _ _ Computation.rootedTree3_ne_01_02]
  have h₃ : σ.rootedDist id (rootedTree3 {1, 2}) = 1 / 3 * exp (-σ.length {0, 1}) := by
    rw [h, Computation.ite₃_eq_third _ _ _ Computation.rootedTree3_ne_01_12
      Computation.rootedTree3_ne_02_12]
  have hX : exp (-σ.length {0, 1}) < 1 := by
    rw [Real.exp_lt_one_iff, neg_lt_zero]
    exact σ.length_pos {0, 1} (by rw [hσ]; decide) (by decide)
  refine ⟨h₁, h₂, h₃, by rw [h₂, h₃, sub_self], ?_⟩
  rw [h₁, h₂]
  linarith

/-- The invariant of equation (1) holds on the rooted gene tree distribution of a binary 3-taxon
species tree if, and only if, the species tree has topology `((a,b),c)`. -/
theorem equation1_iff (σ : SpeciesTree (Fin 3)) (hσ : σ.IsBinary) :
    σ.rootedDist id (rootedTree3 {0, 2}) - σ.rootedDist id (rootedTree3 {1, 2}) = 0 ↔
      σ.clusters = clusters3 := by
  refine ⟨fun h => ?_, fun hc => (equation1 σ hc).2.2.2.1⟩
  rcases Computation.clusters_eq_of_isBinary_three σ hσ with hc | hc | hc
  · exact hc
  · exfalso
    have hd := Computation.rootedDist_three_02 σ hc
    rw [hd, hd, Computation.ite₃_eq_second _ _ _ _ Computation.rootedTree3_ne_01_02,
      Computation.ite₃_eq_third _ _ _ Computation.rootedTree3_ne_01_12
        Computation.rootedTree3_ne_02_12] at h
    have hX : exp (-σ.length {0, 2}) < 1 := by
      rw [Real.exp_lt_one_iff, neg_lt_zero]
      exact σ.length_pos {0, 2} (by rw [hc]; decide) (by decide)
    linarith
  · exfalso
    have hd := Computation.rootedDist_three_12 σ hc
    rw [hd, hd, Computation.ite₃_eq_second _ _ _ _ Computation.rootedTree3_ne_01_02,
      Computation.ite₃_eq_third _ _ _ Computation.rootedTree3_ne_01_12
        Computation.rootedTree3_ne_02_12] at h
    have hX : exp (-σ.length {1, 2}) < 1 := by
      rw [Real.exp_lt_one_iff, neg_lt_zero]
      exact σ.length_pos {1, 2} (by rw [hc]; decide) (by decide)
    linarith

/-- The internal branch length of a 3-taxon species tree `((a,b):t,c)` is recovered from the
probability `p` that the rooted gene tree has `A` and `B` as a cherry: `t = -log((3/2)(1-p))`. -/
theorem introduction_tripleLength (σ : SpeciesTree (Fin 3)) (hσ : σ.clusters = clusters3) :
    σ.length {0, 1} = -log (3 / 2 * (1 - σ.rootedDist id (rootedTree3 {0, 1}))) := by
  rw [(equation1 σ hσ).1]
  have h : 3 / 2 * (1 - (1 - 2 / 3 * exp (-σ.length {0, 1}))) = exp (-σ.length {0, 1}) := by
    ring
  rw [h, Real.log_exp, neg_neg]

end ADR11
