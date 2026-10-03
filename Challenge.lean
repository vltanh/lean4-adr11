module

public import Mathlib

/-!
# Challenge: identifying the rooted species tree from unrooted gene trees

The main results of E. S. Allman, J. H. Degnan and J. A. Rhodes, *Identifying the rooted species
tree from the distribution of unrooted gene trees under the coalescent*, J. Math. Biol. 62 (2011)
833–862 (arXiv:0912.4472v2), stated in the vocabulary of Mathlib.

## The model (the shared definitions below)

* Taxa form a finite type `X`, gene lineages a finite type `L`, and `s : L → X` says from which
  taxon each lineage is sampled; with one lineage per taxon, `L = X` and `s = id`.
* A rooted tree, or a forest of rooted trees, is identified with its set of clusters (the sets of
  leaves below its nodes). A `SpeciesTree X` is a hierarchy of clusters on `X` (nonempty, pairwise
  nested or disjoint, containing `X` and every singleton) with a strictly positive length, in
  coalescent units, on the edge above every cluster other than `X`. `IsBinary` says that every
  internal node has two children.
* Kingman's coalescent on forests: from a forest with `k` roots (maximal clusters), each of the
  `k.choose 2` pairs of roots merges at rate `1`. Its transition probabilities over time `t` are
  the matrix exponential `exp(t • Q)` of the generator `Q` (`kingmanTransition t`); over an
  infinite time they are the limits as `t → ∞` (`kingmanAbsorption`).
* The multispecies coalescent (`forestDist`): the forest entering the population above a cluster
  `A` is the union of the independent forests leaving the populations of the children of `A`,
  together with the singletons of the lineages sampled at `A`; it then evolves by Kingman's
  coalescent for the length of the edge above `A`, or for an infinite time above the root.
  `rootedDist σ s G` is the probability of the rooted gene tree `G`.
* An unrooted tree is identified with the set of sides of its splits (`unroot`), trivial splits
  included; `unrootedDist σ s T` is the probability of the unrooted gene tree `T`, the sum of the
  probabilities of its rooted versions.
* `SameRootedMetricTree σ σ'`: the same rooted topology and the same internal edge lengths (the
  paper's `σ⁺`). `SameUnrootedMetricTree σ σ'`: the same unrooted topology and the same lengths of
  the internal edges of the unrooted tree, in which the two edges below the root merge (the
  paper's `σ⁻`).

## The theorems

* `unrootedDist_nonneg`, `unrootedDist_sum`: the unrooted gene tree probabilities form a
  probability distribution.
* `fourTaxa_balanced`, `fourTaxa_caterpillar` (Section 4.1): on four taxa `a, b, c, d = 0, 1, 2, 3`,
  the species trees `((a,b):x,(c,d):y)` and `(((a,b):x,c):y,d)` give the unrooted gene tree
  `AB|CD` probability `1 - (2/3)e^{-(x+y)}`, respectively `1 - (2/3)e^{-x}`, and each of the other
  two `(1/3)e^{-(x+y)}`, respectively `(1/3)e^{-x}`.
* `theorem9`: for a binary species tree on at least five taxa, with one lineage per taxon, the
  distribution of unrooted gene tree topologies determines the rooted species tree topology and
  all its internal edge lengths.
* `theorem9_four`: on four taxa it determines exactly the unrooted metric species tree.
* `proposition3`: on four taxa, the unrooted metric species tree is determined, but the rooted one
  is not.
* `corollary10`: with `ℓ x > 0` lineages sampled from each taxon `x`, if `|X| ≥ 4` and some
  `ℓ x ≥ 2`, or `|X| = 3` and two of the `ℓ x` are `≥ 2`, the distribution of unrooted gene trees
  determines the rooted species tree, its internal edge lengths, and the pendant edge length of
  every taxon with `ℓ x ≥ 2`.
* `proposition11_theorem9`, `proposition11_theorem9_four`, `proposition11_corollary10`
  (Proposition 11): the same three results for species trees that need not be binary.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS
namespace ADR11

open Finset

section Kingman

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The roots of a forest `F`: its maximal clusters. -/
def roots (F : Finset (Finset L)) : Finset (Finset L) :=
  F.filter fun A => ∀ B ∈ F, A ⊆ B → B = A

/-- The generator of Kingman's coalescent on forests. From a forest `F` with `k` roots, each of
the `k.choose 2` pairs of distinct roots `A, B` merges at rate `1`; the merge adds the cluster
`A ∪ B` to `F`. -/
noncomputable def kingmanGenerator : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G =>
    if G = F then -((#(roots F)).choose 2 : ℝ)
    else if ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F then 1 else 0

/-- The transition probabilities of Kingman's coalescent on forests over a time `t`, in
coalescent units: the matrix exponential `exp (t • Q)` of the generator. -/
noncomputable def kingmanTransition (t : ℝ) : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  NormedSpace.exp (t • kingmanGenerator)

/-- The transition probabilities of Kingman's coalescent on forests over an infinite time: the
entrywise limits of `kingmanTransition t` as `t → ∞`. -/
noncomputable def kingmanAbsorption : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G => Filter.limUnder Filter.atTop fun t : ℝ => kingmanTransition t F G

end Kingman

section MultispeciesCoalescent

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

/-- The children of a cluster `A` in a family `H` of clusters: the maximal members of `H`
strictly contained in `A`. -/
def childClusters (H : Finset (Finset X)) (A : Finset X) : Finset (Finset X) :=
  H.filter fun B => B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A

/-- The forest of singleton clusters `{l}` of the lineages `l` sampled from the taxa in `A` (at an
internal cluster these singletons already belong to the forests of its children). -/
def sampledForest (s : L → X) (A : Finset X) : Finset (Finset L) :=
  (univ.filter fun l => s l ∈ A).image fun l => {l}

/-- The population on the edge above the cluster `A`: Kingman's coalescent runs for the time
`len A`, or, above the root `A = univ`, for an infinite time. -/
noncomputable def populationKernel (len : Finset X → ℝ) (A : Finset X) :
    Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  if A = univ then kingmanAbsorption else kingmanTransition (len A)

/-- The multispecies coalescent on the species tree with clusters `H` and edge lengths `len`,
with lineages sampled according to `s : L → X`: `forestDist H len s A G` is the probability that
the forest of gene lineages leaving the population above the cluster `A` (at its ancient end) is
`G`. The forests leaving the populations of the children of `A` are independent; their union,
together with the singletons of the lineages sampled at `A`, enters the population above `A`. -/
noncomputable def forestDist (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (G : Finset (Finset L)) : ℝ :=
  ∑ f : childClusters H A → Finset (Finset L),
    (∏ B : childClusters H A, forestDist H len s B (f B)) *
      populationKernel len A (univ.sup f ∪ sampledForest s A) G
termination_by #A
decreasing_by exact card_lt_card (mem_filter.1 B.2).2.1

/-- A rooted species tree on the taxa `X`: a hierarchy of clusters on `X`, with a strictly positive
length, in coalescent units, on the edge above each cluster other than the root `univ`. The
lengths of pendant edges (above singletons) matter only when several lineages are sampled from a
taxon. -/
structure SpeciesTree (X : Type*) [Fintype X] [DecidableEq X] where
  /-- The clusters: the sets of taxa below the nodes of the tree. -/
  clusters : Finset (Finset X)
  univ_mem : (univ : Finset X) ∈ clusters
  singleton_mem : ∀ x : X, {x} ∈ clusters
  nonempty_of_mem : ∀ A ∈ clusters, A.Nonempty
  laminar : ∀ A ∈ clusters, ∀ B ∈ clusters, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B
  /-- The length of the edge above each cluster (its value at `univ` and at non-clusters is
  irrelevant). -/
  length : Finset X → ℝ
  length_pos : ∀ A ∈ clusters, A ≠ univ → 0 < length A

/-- The unrooted tree of a rooted tree (or of a rooted forest) `G`: the sides of the splits
induced by its non-root clusters. -/
def unroot (G : Finset (Finset L)) : Finset (Finset L) :=
  G.erase univ ∪ (G.erase univ).image compl

namespace SpeciesTree

/-- A species tree is binary if every cluster with at least two taxa is the union of two disjoint
clusters (equivalently, every internal node has exactly two children). -/
def IsBinary (σ : SpeciesTree X) : Prop :=
  ∀ A ∈ σ.clusters, 2 ≤ #A → ∃ B ∈ σ.clusters, ∃ C ∈ σ.clusters, Disjoint B C ∧ B ∪ C = A

/-- The distribution of rooted gene trees (topologies, given by their clusters) under the
multispecies coalescent on `σ`, with lineages sampled according to `s : L → X`. -/
noncomputable def rootedDist (σ : SpeciesTree X) (s : L → X) (G : Finset (Finset L)) : ℝ :=
  forestDist σ.clusters σ.length s univ G

/-- The distribution of unrooted gene tree topologies under the multispecies coalescent on `σ`,
with lineages sampled according to `s`: the probability of an unrooted tree `T` is the sum of the
probabilities of its rooted versions. -/
noncomputable def unrootedDist (σ : SpeciesTree X) (s : L → X) (T : Finset (Finset L)) : ℝ :=
  ∑ G, if unroot G = T then σ.rootedDist s G else 0

/-- The length of the edge of the unrooted species tree that induces the split `A | Aᶜ`: when the
root is suppressed, the two edges below it merge into one. -/
noncomputable def unrootedLength (σ : SpeciesTree X) (A : Finset X) : ℝ :=
  ∑ C ∈ σ.clusters with C ≠ univ ∧ (C = A ∨ C = Aᶜ), σ.length C

/-- Two species trees have the same unrooted metric tree `σ⁻`: the same unrooted topology and the
same lengths of internal edges. -/
def SameUnrootedMetricTree (σ σ' : SpeciesTree X) : Prop :=
  unroot σ.clusters = unroot σ'.clusters ∧
    ∀ A ∈ unroot σ.clusters, 2 ≤ #A → 2 ≤ #Aᶜ → σ.unrootedLength A = σ'.unrootedLength A

/-- Two species trees have the same rooted metric tree `σ⁺`: the same rooted topology and the same
lengths of internal edges. -/
def SameRootedMetricTree (σ σ' : SpeciesTree X) : Prop :=
  σ.clusters = σ'.clusters ∧ ∀ A ∈ σ.clusters, 2 ≤ #A → A ≠ univ → σ.length A = σ'.length A

end SpeciesTree

end MultispeciesCoalescent

end ADR11
-- END SHARED DEFINITIONS

namespace ADR11.Challenge

open ADR11 Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The unrooted gene tree probabilities are nonnegative. -/
theorem unrootedDist_nonneg {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) (T : Finset (Finset L)) : 0 ≤ σ.unrootedDist s T := by
  sorry

/-- The unrooted gene tree probabilities sum to `1`. -/
theorem unrootedDist_sum {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) : ∑ T, σ.unrootedDist s T = 1 := by
  sorry

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
  sorry

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
  sorry

/-- **Theorem 9** (`|X| ≥ 5`): the unrooted topological gene tree distribution arising from the
multispecies coalescent for samples of one lineage per taxon determines the binary metric species
tree. -/
theorem theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := by
  sorry

/-- **Theorem 9** (`|X| = 4`): the unrooted gene tree distribution determines only the unrooted
metric species tree. -/
theorem theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  sorry

/-- **Proposition 3**: for `|X| = 4` taxa, `σ⁻` is identifiable from the unrooted gene tree
distribution, but `σ⁺` is not. -/
theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
        σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
        σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  sorry

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
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := by
  sorry

/-- **Proposition 11** (Theorem 9, `|X| ≥ 5`, for species trees that need not be binary). -/
theorem proposition11_theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  sorry

/-- **Proposition 11** (Theorem 9, `|X| = 4`, for species trees that need not be binary). -/
theorem proposition11_theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  sorry

/-- **Proposition 11** (Corollary 10 for species trees that need not be binary). -/
theorem proposition11_corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := by
  sorry

end ADR11.Challenge
