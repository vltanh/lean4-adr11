module

public import Mathlib

/-!
# The multispecies coalescent model: shared definitions

This module defines the objects that the main theorems talk about: rooted species trees with edge
lengths, Kingman's coalescent on forests of gene lineages, the multispecies coalescent model, and
the distributions of rooted and unrooted gene tree topologies that it induces. The block between
the markers `BEGIN SHARED DEFINITIONS` and `END SHARED DEFINITIONS` is copied verbatim into
`Challenge.lean` by `scripts/sync_challenge_defs.py`.

## Conventions

* Taxa form a finite type `X`; gene lineages form a finite type `L`, and a sampling map
  `s : L → X` says from which taxon each lineage is sampled. With one lineage per taxon, `L = X`
  and `s = id`.
* A *cluster* is a `Finset`. A rooted tree on a finite set is identified with its set of clusters
  (the sets of leaves below its nodes); a rooted *forest* of gene lineages is likewise a
  `Finset (Finset L)`, the set of clusters of its trees. Its *roots* are its maximal clusters.
* A rooted species tree on `X` is a hierarchy on `X` (a set of nonempty clusters containing `X`
  and every singleton, any two of which are nested or disjoint), together with a length, in
  coalescent units, on the edge above each non-root cluster. Lengths are strictly positive.
* An unrooted tree is identified with the set of sides of its splits: `unroot G` consists of
  every non-root cluster of `G` and its complement. Trivial splits are included.
* Kingman's coalescent on forests is the continuous-time Markov chain in which each pair of roots
  merges at rate `1`. Its transition probabilities over time `t` are the matrix exponential
  `exp (t • Q)` of its generator `Q`; over an infinite time (the population above the root of the
  species tree) they are the limits as `t → ∞`.
* The multispecies coalescent: the forest entering the population above a cluster `A` is the
  union of the forests leaving the populations of the children of `A` (independent of each
  other), together with the singletons of the lineages sampled at `A`; the forest leaving the
  population is obtained by running Kingman's coalescent for the length of the edge above `A`.
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

/-- The forest of singleton clusters `{l}` of the lineages `l` sampled from the taxa in `A`. -/
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
