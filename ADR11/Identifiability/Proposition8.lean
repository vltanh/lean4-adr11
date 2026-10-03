module

public import ADR11.FiveTaxa.Basic
public import ADR11.Nonbinary.Proposition11

/-!
# Propositions 7 and 8: five taxa

* `proposition7`: for `|X| = 5`, `ℙ_{σ⁺}` determines the rooted topology `ψ⁺`.
* `proposition8`: for `|X| = 5`, `ℙ_{σ⁺}` determines `σ⁺`.
* `equation7`, `equation8`, `equation9`: the remaining branch length of the balanced, caterpillar
  and pseudocaterpillar trees (proof of Proposition 8), with arguments of the logarithms greater
  than `1`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Proposition 7.** For `|X| = 5` the rooted species tree topology `ψ⁺` is determined by
`ℙ_{σ⁺}`. -/
theorem proposition7 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.clusters = σ'.clusters :=
  proposition11_proposition7 hX σ σ' h

/-- **Proposition 8.** For `|X| = 5`, `ℙ_{σ⁺}` determines `σ⁺ = (ψ⁺, λ⁺)`. -/
theorem proposition8 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' :=
  proposition11_proposition8 hX σ σ' h

/-- **Equation (7)** (proof of Proposition 8, balanced case): for `(((a,b):x,c):y,(d,e):z)`,
`XYZ = 6u₅ + 9u₇`, `XY³Z = 15u₇`, hence `y = (1/2) log((2u₅ + 3u₇)/(5u₇))`, and the argument of
the logarithm is greater than `1`. -/
theorem equation7 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = balanced5) :
    exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) * exp (-σ.length {3, 4}) =
        6 * u σ 5 + 9 * u σ 7 ∧
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 * exp (-σ.length {3, 4}) =
        15 * u σ 7 ∧
      σ.length {0, 1, 2} = 1 / 2 * log ((2 * u σ 5 + 3 * u σ 7) / (5 * u σ 7)) ∧
      1 < (2 * u σ 5 + 3 * u σ 7) / (5 * u σ 7) := by
  sorry

/-- **Equation (8)** (proof of Proposition 8, caterpillar case): for
`((((a,b):x,c):y,d):z,e)`, `XY³ = 3(-u₂ + u₃ + 5u₇)`, `XY³Z⁶ = 15(u₂ - u₃ + u₇)`, hence
`z = (1/6) log((-u₂ + u₃ + 5u₇)/(5u₂ - 5u₃ + 5u₇))`, and the argument of the logarithm is greater
than `1`. -/
theorem equation8 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 =
        3 * (-u σ 2 + u σ 3 + 5 * u σ 7) ∧
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 *
          exp (-σ.length {0, 1, 2, 3}) ^ 6 = 15 * (u σ 2 - u σ 3 + u σ 7) ∧
      σ.length {0, 1, 2, 3} =
        1 / 6 * log ((-u σ 2 + u σ 3 + 5 * u σ 7) / (5 * u σ 2 - 5 * u σ 3 + 5 * u σ 7)) ∧
      1 < (-u σ 2 + u σ 3 + 5 * u σ 7) / (5 * u σ 2 - 5 * u σ 3 + 5 * u σ 7) := by
  sorry

/-- **Equation (9)** (proof of Proposition 8, pseudocaterpillar case): for
`(((a,b):x,(d,e):y):z,c)`, `XY = 12u₅ + 3u₈`, `XYZ⁶ = 30u₅ - 15u₈`, hence
`z = (1/6) log((4u₅ + u₈)/(10u₅ - 5u₈))`, and the argument of the logarithm is greater than `1`. -/
theorem equation9 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) :
    exp (-σ.length {0, 1}) * exp (-σ.length {3, 4}) = 12 * u σ 5 + 3 * u σ 8 ∧
      exp (-σ.length {0, 1}) * exp (-σ.length {3, 4}) * exp (-σ.length {0, 1, 3, 4}) ^ 6 =
        30 * u σ 5 - 15 * u σ 8 ∧
      σ.length {0, 1, 3, 4} = 1 / 6 * log ((4 * u σ 5 + u σ 8) / (10 * u σ 5 - 5 * u σ 8)) ∧
      1 < (4 * u σ 5 + u σ 8) / (10 * u σ 5 - 5 * u σ 8) := by
  sorry

end ADR11
