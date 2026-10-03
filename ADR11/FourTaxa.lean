module

public import ADR11.SmallTrees

/-!
# Section 4.1: four taxa

With four taxa `a, b, c, d` (`Fin 4`), the unrooted gene trees are `T_{AB|CD}`, `T_{AC|BD}` and
`T_{AD|BC}` (`treeOfClusters {{0,1}}`, `treeOfClusters {{0,2}}`, `treeOfClusters {{0,3}}`).

* `fourTaxa_balanced`, `fourTaxa_caterpillar`: the unrooted gene tree distributions of the
  balanced species tree `((a,b):x,(c,d):y)` and of the rooted caterpillar `(((a,b):x,c):y,d)`.
* `fourTaxa_recovery`: for any binary 4-taxon species tree, the most probable unrooted gene tree
  has the topology of the unrooted species tree, and the internal edge length of the unrooted
  species tree is `-log((3/2)(1 - ℙ(T)))`.
* `fourTaxa_sameDistribution`: the five rooted species trees `(((a,b):x,c):y₁,d)`,
  `(((a,b):x,d):y₂,c)`, `(((c,d):x,a):y₃,b)`, `(((c,d):x,b):y₄,a)` and `((a,b):z,(c,d):x-z)`
  give the same unrooted gene tree distribution.
* `proposition3`: for `|X| = 4`, `σ⁻` is identifiable from `ℙ_σ`, but `σ⁺` is not.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Section 4.1: for the balanced species tree `((a,b):x,(c,d):y)`,
`ℙ(T_{AB|CD}) = 1 - (2/3) e^{-(x+y)}` and `ℙ(T_{AC|BD}) = ℙ(T_{AD|BC}) = (1/3) e^{-(x+y)}`. -/
theorem fourTaxa_balanced (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters = balanced4) :
    σ.unrootedDist id (treeOfClusters {{0, 1}}) =
        1 - 2 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id (treeOfClusters {{0, 2}}) =
        1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id (treeOfClusters {{0, 3}}) =
        1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) := by
  sorry

/-- Section 4.1: for the rooted caterpillar species tree `(((a,b):x,c):y,d)`,
`ℙ(T_{AB|CD}) = 1 - (2/3) e^{-x}` and `ℙ(T_{AC|BD}) = ℙ(T_{AD|BC}) = (1/3) e^{-x}`. -/
theorem fourTaxa_caterpillar (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters = caterpillar4) :
    σ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 * exp (-σ.length {0, 1}) := by
  sorry

/-- Section 4.1: for any binary species tree on four taxa, with nontrivial split `A | Aᶜ` of its
unrooted topology, the unrooted gene tree `T` with that split is strictly the most probable, and
the internal edge length of `σ⁻` is `-log((3/2)(1 - ℙ(T)))`. -/
theorem fourTaxa_recovery (hX : Fintype.card X = 4) (σ : SpeciesTree X) (hσ : σ.IsBinary)
    (A : Finset X) (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    (∀ B : Finset X, #B = 2 → B ≠ A → B ≠ Aᶜ →
        σ.unrootedDist id (treeOfClusters {B}) < σ.unrootedDist id (treeOfClusters {A})) ∧
      σ.unrootedLength A = -log (3 / 2 * (1 - σ.unrootedDist id (treeOfClusters {A}))) := by
  sorry

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
  sorry

/-- **Proposition 3.** For `|X| = 4` taxa, `σ⁻` is identifiable from `ℙ_{σ⁺}`, but `σ⁺` is not. -/
theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
        σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
        σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  sorry

end ADR11
