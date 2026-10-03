module

public import ADR11.Model
public import ADR11.FourTaxa
public import ADR11.Identifiability.Theorem9
public import ADR11.Identifiability.Corollary10
public import ADR11.Nonbinary.Proposition11

/-!
# Solution: the Challenge's theorems, proved from the library

Each theorem of `Challenge.lean` is restated verbatim, with the same name, and proved from the
development. The definitions it uses are those of `ADR11.Defs`, of which `Challenge.lean` holds a
verbatim copy.
-/

@[expose] public section

namespace ADR11.Challenge

open ADR11 Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The unrooted gene tree probabilities are nonnegative. -/
theorem unrootedDist_nonneg {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) (T : Finset (Finset L)) : 0 ≤ σ.unrootedDist s T := ADR11.unrootedDist_nonneg σ s T

/-- The unrooted gene tree probabilities sum to `1`. -/
theorem unrootedDist_sum {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) : ∑ T, σ.unrootedDist s T = 1 := ADR11.unrootedDist_sum σ s

/-- Section 4.1, balanced species tree `((a,b):x,(c,d):y)` on `Fin 4`: the unrooted gene trees
`AB|CD`, `AC|BD`, `AD|BC` (each given by the sides of its splits, trivial ones included) have
probabilities `1 - (2/3)e^{-(x+y)}`, `(1/3)e^{-(x+y)}`, `(1/3)e^{-(x+y)}`. -/
theorem fourTaxa_balanced (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {2, 3}, {0}, {1}, {2}, {3}}) :
    σ.unrootedDist id {{0, 1}, {2, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 - 2 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id {{0, 2}, {1, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id {{0, 3}, {1, 2}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) := by
  have h4 : (balanced4 : Finset (Finset (Fin 4))) = {univ, {0, 1}, {2, 3}, {0}, {1}, {2}, {3}} := by
    decide
  have t1 : treeOfClusters ({{0, 1}} : Finset (Finset (Fin 4))) =
      {{0, 1}, {2, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} := by decide
  have t2 : treeOfClusters ({{0, 2}} : Finset (Finset (Fin 4))) =
      {{0, 2}, {1, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} := by decide
  have t3 : treeOfClusters ({{0, 3}} : Finset (Finset (Fin 4))) =
      {{0, 3}, {1, 2}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} := by decide
  have := ADR11.fourTaxa_balanced σ (hσ.trans h4.symm)
  rwa [t1, t2, t3] at this

/-- Section 4.1, rooted caterpillar species tree `(((a,b):x,c):y,d)` on `Fin 4`: the unrooted gene
trees `AB|CD`, `AC|BD`, `AD|BC` have probabilities `1 - (2/3)e^{-x}`, `(1/3)e^{-x}`,
`(1/3)e^{-x}`. -/
theorem fourTaxa_caterpillar (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {0, 1, 2}, {0}, {1}, {2}, {3}}) :
    σ.unrootedDist id {{0, 1}, {2, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 - 2 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id {{0, 2}, {1, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id {{0, 3}, {1, 2}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-σ.length {0, 1}) := by
  have h4 : (caterpillar4 : Finset (Finset (Fin 4))) =
      {univ, {0, 1}, {0, 1, 2}, {0}, {1}, {2}, {3}} := by decide
  have t1 : treeOfClusters ({{0, 1}} : Finset (Finset (Fin 4))) =
      {{0, 1}, {2, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} := by decide
  have t2 : treeOfClusters ({{0, 2}} : Finset (Finset (Fin 4))) =
      {{0, 2}, {1, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} := by decide
  have t3 : treeOfClusters ({{0, 3}} : Finset (Finset (Fin 4))) =
      {{0, 3}, {1, 2}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} := by decide
  have := ADR11.fourTaxa_caterpillar σ (hσ.trans h4.symm)
  rwa [t1, t2, t3] at this

/-- **Theorem 9** (`|X| ≥ 5`): the unrooted topological gene tree distribution arising from the
multispecies coalescent for samples of one lineage per taxon determines the binary metric species
tree. -/
theorem theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := ADR11.theorem9 hX σ σ' hσ hσ' h

/-- **Theorem 9** (`|X| = 4`): the unrooted gene tree distribution determines only the unrooted
metric species tree. -/
theorem theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := ADR11.theorem9_four hX σ σ' hσ hσ'

/-- **Proposition 3**: for `|X| = 4` taxa, `σ⁻` is identifiable from the unrooted gene tree
distribution, but `σ⁺` is not. -/
theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
        σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
        σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := ADR11.proposition3 hX

/-- **Corollary 10**: with `ℓ x > 0` lineages `(x, k)`, `k < ℓ x`, sampled from each taxon `x`, if
`|X| ≥ 4` and some `ℓ x ≥ 2`, or `|X| = 3` and two of the `ℓ x` are `≥ 2`, the unrooted gene tree
distribution determines the binary rooted species tree, its internal edge lengths, and the
pendant edge length of every taxon `x` with `ℓ x ≥ 2`. -/
theorem corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X) (hσ : σ.IsBinary) (hσ' : σ'.IsBinary)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := ADR11.corollary10 ℓ hℓ hcond σ σ' hσ hσ' h

/-- **Proposition 11** (Theorem 9, `|X| ≥ 5`, for species trees that need not be binary). -/
theorem proposition11_theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := ADR11.proposition11_theorem9 hX σ σ' h

/-- **Proposition 11** (Theorem 9, `|X| = 4`, for species trees that need not be binary). -/
theorem proposition11_theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := ADR11.proposition11_theorem9_four hX σ σ'

/-- **Proposition 11** (Corollary 10 for species trees that need not be binary). -/
theorem proposition11_corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := ADR11.proposition11_corollary10 ℓ hℓ hcond σ σ' h

end ADR11.Challenge
