module

public import ADR11.FiveTaxa.Basic

/-!
# Section 5 and Appendix C: nonbinary species trees

* `section5_threeTaxa`: for the unresolved 3-taxon species tree the three rooted gene trees are
  equiprobable; for a resolved one exactly one has probability greater than `1/3`.
* `section5_triples`: a species tree has no cluster separating one of three taxa from the other
  two exactly when the three rooted triples on them are equiprobable.
* `section5_fourTaxa`: `(a,b,c,d)` and `((a,b,c):y,d)` give the same unrooted distribution, and so
  do `(((a,b):x,c):y,d)` and `((a,b):x,c,d)`, with `ℙ(T_{AB|CD}) = 1 - (2/3) e^{-x}`.
* `proposition11_*`: Proposition 11, the extension of Proposition 3, Corollary 6,
  Propositions 7 and 8, Theorem 9 and Corollary 10 to nonbinary species trees.
* `table6`, `table7`: the inequalities and the unrooted gene tree distributions of the nine
  nonbinary 5-taxon representatives `P₁, …, P₉` (`ADR11.polytomy5`).
* `appendixC_leastClass`: the least probable class `𝒞` of gene trees is well defined, with the
  sizes listed in the proof of Proposition 11 for the twelve rooted 5-taxon shapes; and the sizes
  of the next class used there.
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
  sorry

/-- Section 5: polytomies are identified by rooted triples. For distinct taxa `a, b, c`, no cluster
of the species tree contains exactly two of them if and only if the three rooted triples on them
are equiprobable. -/
theorem section5_triples (σ : SpeciesTree X) (a b c : X) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    (∀ C ∈ σ.clusters, ¬ ((a ∈ C ∧ b ∈ C ∧ c ∉ C) ∨ (a ∈ C ∧ c ∈ C ∧ b ∉ C) ∨
        (b ∈ C ∧ c ∈ C ∧ a ∉ C))) ↔
      (σ.rootedTripleProb a b c = σ.rootedTripleProb a c b ∧
        σ.rootedTripleProb a b c = σ.rootedTripleProb b c a) := by
  sorry

/-- Section 5, four taxa: `(a,b,c,d)` and `((a,b,c):y,d)` give the same unrooted gene tree
distribution, and so do `(((a,b):x,c):y,d)` and `((a,b):x,c,d)` (with the same `x`), with
`ℙ(T_{AB|CD}) = 1 - (2/3) e^{-x}`. -/
theorem section5_fourTaxa (σ₁ σ₂ σ₃ σ₄ : SpeciesTree (Fin 4))
    (h₁ : σ₁.clusters = hierarchyOf ∅) (h₂ : σ₂.clusters = hierarchyOf {{0, 1, 2}})
    (h₃ : σ₃.clusters = caterpillar4) (h₄ : σ₄.clusters = hierarchyOf {{0, 1}})
    (hx : σ₄.length {0, 1} = σ₃.length {0, 1}) :
    σ₁.unrootedDist id = σ₂.unrootedDist id ∧ σ₃.unrootedDist id = σ₄.unrootedDist id ∧
      σ₄.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * exp (-σ₄.length {0, 1}) := by
  sorry

/-- **Proposition 11** (Proposition 3 for nonbinary species trees). For `|X| = 4`, `σ⁻` is
identifiable from `ℙ_{σ⁺}`, but `σ⁺` is not. -/
theorem proposition11_proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.unrootedDist id = σ'.unrootedDist id →
        σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.unrootedDist id = σ'.unrootedDist id ∧
        ¬ σ.SameRootedMetricTree σ' := by
  sorry

/-- **Proposition 11** (Corollary 6 for nonbinary species trees). For any `X`, `ℙ_{σ⁺}` determines
`σ⁻`. -/
theorem proposition11_corollary6 (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' := by
  sorry

/-- **Proposition 11** (Proposition 7 for nonbinary species trees). -/
theorem proposition11_proposition7 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.clusters = σ'.clusters := by
  sorry

/-- **Proposition 11** (Proposition 8 for nonbinary species trees). -/
theorem proposition11_proposition8 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  sorry

/-- **Proposition 11** (Theorem 9 for nonbinary species trees, `|X| ≥ 5`). -/
theorem proposition11_theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  sorry

/-- **Proposition 11** (Theorem 9 for nonbinary species trees, `|X| = 4`). -/
theorem proposition11_theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  sorry

/-- **Proposition 11** (Corollary 10 for nonbinary species trees). -/
theorem proposition11_corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := by
  sorry

/-- **Table 6**: the inequalities between unrooted gene tree probabilities for the nonbinary
5-taxon representatives (`u₁ > u₂` for `P₂`; `u₃ > u₁` for `P₃`; `u₁ > u₂ > u₇` for `P₄` and
`P₈`; `u₁ > u₂, u₄ > u₅` for `P₅`; `u₁ > u₂, u₄ > u₅ > u₇` for `P₆`; `u₁ > u₂, u₈ > u₄` for `P₇`;
`u₁, u₃ > u₂ > u₇` for `P₉`). -/
theorem table6 (σ : SpeciesTree (Fin 5)) :
    (σ.clusters = polytomy5 2 → u σ 1 > u σ 2) ∧
    (σ.clusters = polytomy5 3 → u σ 3 > u σ 1) ∧
    (σ.clusters = polytomy5 4 → u σ 1 > u σ 2 ∧ u σ 2 > u σ 7) ∧
    (σ.clusters = polytomy5 5 → u σ 1 > u σ 2 ∧ u σ 1 > u σ 4 ∧ u σ 2 > u σ 5 ∧ u σ 4 > u σ 5) ∧
    (σ.clusters = polytomy5 6 → u σ 1 > u σ 2 ∧ u σ 1 > u σ 4 ∧ u σ 2 > u σ 5 ∧ u σ 4 > u σ 5 ∧
      u σ 5 > u σ 7) ∧
    (σ.clusters = polytomy5 7 → u σ 1 > u σ 2 ∧ u σ 1 > u σ 8 ∧ u σ 2 > u σ 4 ∧ u σ 8 > u σ 4) ∧
    (σ.clusters = polytomy5 8 → u σ 1 > u σ 2 ∧ u σ 2 > u σ 7) ∧
    (σ.clusters = polytomy5 9 → u σ 1 > u σ 2 ∧ u σ 3 > u σ 2 ∧ u σ 2 > u σ 7) := by
  sorry

/-- **Table 7**: the equivalence classes of equiprobable gene trees and the unrooted gene tree
distributions of the nonbinary 5-taxon representatives `P₁, …, P₉`, in terms of the transformed
lengths of their internal edges. For each representative the value of `u_i` is given for every
`i`; `X`, `Y`, `Z` denote `e^{-x}`, `e^{-y}`, `e^{-z}` for the edges labelled `x`, `y`, `z` in
Table 6. -/
theorem table7 (σ : SpeciesTree (Fin 5)) (i : ℕ) (hi : i ∈ Icc 1 15) :
    (σ.clusters = polytomy5 1 → u σ i = 1 / 15) ∧
    (σ.clusters = polytomy5 2 →
      let Z := exp (-σ.length {3, 4})
      u σ i = if i ∈ ({1, 4, 13} : Finset ℕ) then 1 / 3 - 4 / 15 * Z else 1 / 15 * Z) ∧
    (σ.clusters = polytomy5 3 →
      let Z := exp (-σ.length {0, 1, 2, 3})
      u σ i = if i ∈ ({3, 6, 9} : Finset ℕ) then 1 / 9 - 2 / 45 * Z ^ 6
        else 1 / 18 + 1 / 90 * Z ^ 6) ∧
    (σ.clusters = polytomy5 4 →
      let Y := exp (-σ.length {0, 1, 2})
      u σ i = if i ∈ ({1, 4, 13} : Finset ℕ) then 1 / 3 - 1 / 3 * Y + 1 / 15 * Y ^ 3
        else if i ∈ ({2, 3, 5, 6, 9, 12} : Finset ℕ) then 1 / 6 * Y - 1 / 10 * Y ^ 3
        else 1 / 15 * Y ^ 3) ∧
    (σ.clusters = polytomy5 5 →
      let X := exp (-σ.length {0, 1})
      let Y := exp (-σ.length {3, 4})
      u σ i = if i = 1 then 1 - 2 / 3 * X - 2 / 3 * Y + 2 / 5 * X * Y
        else if i ∈ ({2, 3} : Finset ℕ) then 1 / 3 * Y - 4 / 15 * X * Y
        else if i ∈ ({4, 13} : Finset ℕ) then 1 / 3 * X - 4 / 15 * X * Y
        else 1 / 15 * X * Y) ∧
    (σ.clusters = polytomy5 6 →
      let X := exp (-σ.length {0, 1})
      let Y := exp (-σ.length {0, 1, 2})
      u σ i = if i = 1 then 1 - 2 / 3 * X - 2 / 3 * Y + 1 / 3 * X * Y + 1 / 15 * X * Y ^ 3
        else if i ∈ ({2, 3} : Finset ℕ) then 1 / 3 * Y - 1 / 6 * X * Y - 1 / 10 * X * Y ^ 3
        else if i ∈ ({4, 13} : Finset ℕ) then 1 / 3 * X - 1 / 3 * X * Y + 1 / 15 * X * Y ^ 3
        else if i ∈ ({5, 6, 9, 12} : Finset ℕ) then 1 / 6 * X * Y - 1 / 10 * X * Y ^ 3
        else 1 / 15 * X * Y ^ 3) ∧
    (σ.clusters = polytomy5 7 →
      let X := exp (-σ.length {0, 1})
      let Z := exp (-σ.length {0, 1, 3, 4})
      u σ i = if i = 1 then 1 / 3 - 2 / 9 * X - 2 / 45 * X * Z ^ 6
        else if i ∈ ({2, 3} : Finset ℕ) then 1 / 3 - 5 / 18 * X + 1 / 90 * X * Z ^ 6
        else if i ∈ ({8, 11} : Finset ℕ) then 1 / 9 * X - 2 / 45 * X * Z ^ 6
        else 1 / 18 * X + 1 / 90 * X * Z ^ 6) ∧
    (σ.clusters = polytomy5 8 →
      let Y := exp (-σ.length {0, 1, 2})
      let Z := exp (-σ.length {3, 4})
      u σ i = if i ∈ ({1, 4, 13} : Finset ℕ) then 1 / 3 - 1 / 3 * Y * Z + 1 / 15 * Y ^ 3 * Z
        else if i ∈ ({2, 3, 5, 6, 9, 12} : Finset ℕ) then 1 / 6 * Y * Z - 1 / 10 * Y ^ 3 * Z
        else 1 / 15 * Y ^ 3 * Z) ∧
    (σ.clusters = polytomy5 9 →
      let Y := exp (-σ.length {0, 1, 2})
      let Z := exp (-σ.length {0, 1, 2, 3})
      u σ i = if i ∈ ({1, 4, 13} : Finset ℕ) then
          1 / 3 - 1 / 3 * Y + 1 / 18 * Y ^ 3 + 1 / 90 * Y ^ 3 * Z ^ 6
        else if i ∈ ({2, 5, 12} : Finset ℕ) then
          1 / 6 * Y - 1 / 9 * Y ^ 3 + 1 / 90 * Y ^ 3 * Z ^ 6
        else if i ∈ ({3, 6, 9} : Finset ℕ) then
          1 / 6 * Y - 1 / 18 * Y ^ 3 - 2 / 45 * Y ^ 3 * Z ^ 6
        else 1 / 18 * Y ^ 3 + 1 / 90 * Y ^ 3 * Z ^ 6) := by
  sorry

open scoped Classical in
/-- Appendix C (proof of Proposition 11): for every rooted 5-taxon species tree shape the least
probable class `𝒞` of gene trees has probability strictly smaller than all others, and
`|𝒞| = 15` for `P₁`, `12` for `P₂` and `P₃`, `10` for `P₅` and `P₇`, `8` for the resolved
pseudocaterpillar, and `6` for the resolved caterpillar and balanced trees and for `P₄`, `P₆`,
`P₈`, `P₉`. When `|𝒞| = 6`, the class with the second smallest probability has cardinality `2`
only for the caterpillar, `3` only for `P₉`, `6` only for `P₄` and `P₈`, and `4` for the balanced
tree and `P₆`. -/
theorem appendixC_leastClass (σ : SpeciesTree (Fin 5)) :
    let C := {i ∈ Icc 1 15 | ∀ j ∈ Icc 1 15, u σ i ≤ u σ j}
    let C₂ := {i ∈ Icc 1 15 | i ∉ C ∧ ∀ j ∈ Icc 1 15, j ∉ C → u σ i ≤ u σ j}
    (σ.clusters = polytomy5 1 → #C = 15) ∧
    (σ.clusters = polytomy5 2 → #C = 12) ∧ (σ.clusters = polytomy5 3 → #C = 12) ∧
    (σ.clusters = polytomy5 5 → #C = 10) ∧ (σ.clusters = polytomy5 7 → #C = 10) ∧
    (σ.clusters = pseudocaterpillar5 → #C = 8) ∧
    (σ.clusters = caterpillar5 → #C = 6 ∧ #C₂ = 2) ∧
    (σ.clusters = balanced5 → #C = 6 ∧ #C₂ = 4) ∧
    (σ.clusters = polytomy5 4 → #C = 6 ∧ #C₂ = 6) ∧
    (σ.clusters = polytomy5 6 → #C = 6 ∧ #C₂ = 4) ∧
    (σ.clusters = polytomy5 8 → #C = 6 ∧ #C₂ = 6) ∧
    (σ.clusters = polytomy5 9 → #C = 6 ∧ #C₂ = 3) := by
  sorry

end ADR11
