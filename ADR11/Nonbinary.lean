module

public import ADR11.FiveTaxa.Basic
public import ADR11.MSC.Basic
public import ADR11.MSC.Contract
public import ADR11.Computation.ThreeTaxa
public import ADR11.Computation.FourTaxa

/-!
# Section 5: nonbinary species trees

* `section5_threeTaxa`: for the unresolved 3-taxon species tree the three rooted gene trees are
  equiprobable; for a resolved one exactly one has probability greater than `1/3`.
* `section5_triples`, `section5_proposition1`, `section5_corollary2` are in
  `ADR11.Nonbinary.Triples`.
* `section5_limit`: the distributions of a nonbinary species tree are limits of those of a binary
  resolution as the added branch lengths tend to `0`.
* `section5_fourTaxa`: `(a,b,c,d)` and `((a,b,c):y,d)` give the same unrooted distribution, and so
  do `(((a,b):x,c):y,d)` and `((a,b):x,c,d)`, with `ℙ(T_{AB|CD}) = 1 - (2/3) e^{-x}`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Section 5, three taxa: for the unresolved species tree `(a,b,c)` the three rooted gene trees
have probability `1/3`; for the resolved species tree `((a,b):t,c)` exactly one rooted gene tree
has probability greater than `1/3`. -/
theorem section5_threeTaxa (σ σ' : SpeciesTree (Fin 3)) (hσ : σ.clusters = hierarchyOf ∅)
    (hσ' : σ'.clusters = clusters3) :
    (σ.rootedDist id (rootedTree3 {0, 1}) = 1 / 3 ∧ σ.rootedDist id (rootedTree3 {0, 2}) = 1 / 3 ∧
        σ.rootedDist id (rootedTree3 {1, 2}) = 1 / 3) ∧
      (1 / 3 < σ'.rootedDist id (rootedTree3 {0, 1}) ∧
        σ'.rootedDist id (rootedTree3 {0, 2}) < 1 / 3 ∧
        σ'.rootedDist id (rootedTree3 {1, 2}) < 1 / 3) := by
  have hs := Computation.rootedDist_three_star σ hσ
  have hr := Computation.rootedDist_three_01 σ' hσ'
  have hX : exp (-σ'.length {0, 1}) < 1 := by
    rw [Real.exp_lt_one_iff, neg_lt_zero]
    exact σ'.length_pos {0, 1} (by rw [hσ']; decide) (by decide)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hs, Computation.ite₃_eq_first]
  · rw [hs, Computation.ite₃_eq_second _ _ _ _ Computation.rootedTree3_ne_01_02]
  · rw [hs, Computation.ite₃_eq_third _ _ _ Computation.rootedTree3_ne_01_12
      Computation.rootedTree3_ne_02_12]
  · rw [hr, Computation.ite₃_eq_first]
    linarith
  · rw [hr, Computation.ite₃_eq_second _ _ _ _ Computation.rootedTree3_ne_01_02]
    linarith
  · rw [hr, Computation.ite₃_eq_third _ _ _ Computation.rootedTree3_ne_01_12
      Computation.rootedTree3_ne_02_12]
    linarith

/-- Section 5, four taxa: `(a,b,c,d)` and `((a,b,c):y,d)` give the same unrooted gene tree
distribution, and so do `(((a,b):x,c):y,d)` and `((a,b):x,c,d)` (with the same `x`), with
`ℙ(T_{AB|CD}) = 1 - (2/3) e^{-x}`. -/
theorem section5_fourTaxa (σ₁ σ₂ σ₃ σ₄ : SpeciesTree (Fin 4))
    (h₁ : σ₁.clusters = hierarchyOf ∅) (h₂ : σ₂.clusters = hierarchyOf {{0, 1, 2}})
    (h₃ : σ₃.clusters = caterpillar4) (h₄ : σ₄.clusters = hierarchyOf {{0, 1}})
    (hx : σ₄.length {0, 1} = σ₃.length {0, 1}) :
    σ₁.unrootedDist id = σ₂.unrootedDist id ∧ σ₃.unrootedDist id = σ₄.unrootedDist id ∧
      σ₄.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * exp (-σ₄.length {0, 1}) := by
  refine ⟨?_, ?_, ?_⟩
  · funext U
    rw [Computation.unrootedDist_star4 σ₁ h₁ U, Computation.unrootedDist_triple4 σ₂ h₂ U]
  · funext U
    rw [Computation.unrootedDist_cat4_0123 σ₃ h₃ U, Computation.unrootedDist_cherry4 σ₄ h₄ U, hx]
  · rw [Computation.unrootedDist_cherry4 σ₄ h₄, Computation.ite₃_eq_first]

/-- Section 5: the gene tree probabilities of a nonbinary species tree are the limits of those of a
binary resolution `H` of it as the lengths of the added edges tend to `0`. -/
theorem section5_limit (σ : SpeciesTree X) {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hsub : σ.clusters ⊆ H) (T : Finset (Finset X)) :
    Filter.Tendsto
      (fun ε : ℝ => unrootedDistOf H (fun A => if A ∈ σ.clusters then σ.length A else ε) id T)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (σ.unrootedDist id T)) :=
  -- the distribution is continuous in `ε`, and at `ε = 0` the added edges contract
  (σ.tendsto_unrootedDistOf hH hsub id T).mono_left nhdsWithin_le_nhds

end ADR11
