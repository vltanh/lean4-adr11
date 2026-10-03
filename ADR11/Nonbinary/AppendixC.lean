module

public import ADR11.FiveTaxa.Basic

/-!
# Appendix C: nonbinary 5-taxon species trees

* `table6`, `table7`: the inequalities and the unrooted gene tree distributions of the nine
  nonbinary 5-taxon representatives `P₁, …, P₉` (`ADR11.polytomy5`).
* `appendixC_leastClass`: the least probable class `𝒞` of gene trees is well defined, with the
  sizes listed in the proof of Proposition 11 for the twelve rooted 5-taxon shapes, and the sizes
  of the next class used there.
* `table7_classes`: the equivalence classes of Table 7.
* `appendixC_degenerate`: the two 2-element classes of `P₅` and of `P₇` can merge.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

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

/-- The class of `T_i` for the nonbinary representative `P_k` in Table 7, named by its smallest
index. -/
def polytomyClass : ℕ → ℕ → ℕ
  | 1, _ => 1
  | 2, i => if i ∈ ({1, 4, 13} : Finset ℕ) then 1 else 2
  | 3, i => if i ∈ ({3, 6, 9} : Finset ℕ) then 3 else 1
  | 4, i => if i ∈ ({1, 4, 13} : Finset ℕ) then 1
      else if i ∈ ({2, 3, 5, 6, 9, 12} : Finset ℕ) then 2 else 7
  | 5, i => if i = 1 then 1 else if i ∈ ({2, 3} : Finset ℕ) then 2
      else if i ∈ ({4, 13} : Finset ℕ) then 4 else 5
  | 6, i => if i = 1 then 1 else if i ∈ ({2, 3} : Finset ℕ) then 2
      else if i ∈ ({4, 13} : Finset ℕ) then 4 else if i ∈ ({5, 6, 9, 12} : Finset ℕ) then 5 else 7
  | 7, i => if i = 1 then 1 else if i ∈ ({2, 3} : Finset ℕ) then 2
      else if i ∈ ({8, 11} : Finset ℕ) then 8 else 4
  | 8, i => if i ∈ ({1, 4, 13} : Finset ℕ) then 1
      else if i ∈ ({2, 3, 5, 6, 9, 12} : Finset ℕ) then 2 else 7
  | 9, i => if i ∈ ({1, 4, 13} : Finset ℕ) then 1 else if i ∈ ({2, 5, 12} : Finset ℕ) then 2
      else if i ∈ ({3, 6, 9} : Finset ℕ) then 3 else 7
  | _, i => i

/-- **Table 7**, equivalence classes: for each nonbinary representative `P_k`, two gene trees have
the same probability for all branch lengths exactly when they lie in the same class of Table 7. -/
theorem table7_classes (k : ℕ) (hk : k ∈ Icc 1 9) (i j : ℕ) (hi : i ∈ Icc 1 15)
    (hj : j ∈ Icc 1 15) :
    (∀ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 k → u σ i = u σ j) ↔
      polytomyClass k i = polytomyClass k j := by
  sorry

/-- Appendix C: for `P₅` and `P₇` the two classes of size 2 can degenerate to a single class of
size 4. -/
theorem appendixC_degenerate :
    (∃ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 5 ∧ u σ 2 = u σ 4) ∧
      ∃ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 7 ∧ u σ 2 = u σ 8 := by
  sorry

end ADR11
