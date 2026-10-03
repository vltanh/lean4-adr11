module

public import ADR11.FiveTaxa.Basic

/-!
# Section 4.3: species tree identifiability for 5 or more taxa

* `corollary6`: for any `X`, `ℙ_{σ⁺}` determines `σ⁻`.
* `proposition7`: for `|X| = 5`, `ℙ_{σ⁺}` determines the rooted topology `ψ⁺`.
* `proposition8`: for `|X| = 5`, `ℙ_{σ⁺}` determines `σ⁺`; `equation7`, `equation8`,
  `equation9` give the remaining branch length of the balanced, caterpillar and pseudocaterpillar
  trees, with arguments of the logarithms greater than `1`.
* `theorem9`, `theorem9_four`: the main theorem.
* `corollary10`: several lineages sampled per taxon.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Corollary 6.** For any `X`, `ℙ_{σ⁺}` determines `σ⁻`. -/
theorem corollary6 (σ σ' : SpeciesTree X) (hσ : σ.IsBinary) (hσ' : σ'.IsBinary)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' := by
  sorry

/-- **Proposition 7.** For `|X| = 5` the rooted species tree topology `ψ⁺` is determined by
`ℙ_{σ⁺}`. -/
theorem proposition7 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.clusters = σ'.clusters := by
  sorry

/-- **Proposition 8.** For `|X| = 5`, `ℙ_{σ⁺}` determines `σ⁺ = (ψ⁺, λ⁺)`. -/
theorem proposition8 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := by
  sorry

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

/-- **Theorem 9** (`|X| ≥ 5`). The unrooted topological gene tree distribution `ℙ_{σ⁺}` arising
from the multispecies coalescent model for samples of one lineage per taxon determines the metric
species tree `σ⁺` provided `|X| ≥ 5`. -/
theorem theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := by
  sorry

/-- **Theorem 9** (`|X| = 4`). If `|X| = 4`, `ℙ_{σ⁺}` determines only the unrooted metric species
tree `σ⁻`: two species trees have the same unrooted gene tree distribution exactly when they have
the same unrooted metric tree. -/
theorem theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  sorry

/-- **Corollary 10.** Consider the distribution of unrooted topological gene trees under the
multispecies coalescent with `ℓ_x > 0` lineages sampled from each taxon `x` (lineages
`(x, k)`, `k < ℓ_x`). Suppose that either `|X| ≥ 4` and some `ℓ_x ≥ 2`, or `|X| = 3` and at least
two of the `ℓ_x` are `≥ 2`. Then the gene tree distribution determines the species tree's rooted
topology, its internal edge lengths, and the length of the pendant edge of every taxon `x` with
`ℓ_x > 1`. -/
theorem corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X) (hσ : σ.IsBinary) (hσ' : σ'.IsBinary)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := by
  sorry

end ADR11
