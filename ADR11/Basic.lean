module

public import ADR11.Defs

/-!
# Notions used in the statements of the paper's results

* `restrictClusters S H`: the clusters of a rooted tree (or forest) `H` on `X`, restricted to the
  taxa `S` and viewed as clusters on the subtype `S`.
* `restrictSplits S T`: the induced unrooted tree `T(S)` of an unrooted tree `T`, in the
  representation of `ADR11.unroot` (the sides of its splits).
* `SpeciesTree.restrict σ S`: the induced species tree `σ⁺(S)` (the paper's Section 2): its
  clusters are the nonempty traces `A ∩ S` of the clusters of `σ`, and the length of the edge above
  a trace `C` is the sum of the lengths of the edges above the clusters `A` of `σ` with
  `A ∩ S = C` (the edges that merge when nodes of degree 2 are suppressed).
* `coalescenceProb i j t`: the paper's `g_ij(t)`, the probability that `i` lineages coalesce into
  `j` lineages within time `t`, defined from Kingman's coalescent itself.
* `SpeciesTree.rootedTripleProb σ a b c`: the probability that the rooted gene tree displays the
  rooted triple `ab|c`.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The clusters of `H` that meet `S`, restricted to `S`, as clusters on the subtype `S`. -/
def restrictClusters (S : Finset X) (H : Finset (Finset X)) : Finset (Finset S) :=
  (H.filter fun A => (A ∩ S).Nonempty).image fun A => A.subtype (· ∈ S)

/-- The induced unrooted tree `T(S)` of an unrooted tree `T` (given by the sides of its splits):
the splits of `T` whose two sides both meet `S`, restricted to `S`. -/
def restrictSplits (S : Finset X) (T : Finset (Finset X)) : Finset (Finset S) :=
  (T.filter fun A => (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty).image fun A => A.subtype (· ∈ S)

namespace SpeciesTree

theorem restrict_univ_mem (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (univ : Finset S) ∈ restrictClusters S σ.clusters := by
  sorry

theorem restrict_singleton_mem (σ : SpeciesTree X) (S : Finset X) (x : S) :
    {x} ∈ restrictClusters S σ.clusters := by
  sorry

theorem restrict_nonempty_of_mem (σ : SpeciesTree X) (S : Finset X) :
    ∀ C ∈ restrictClusters S σ.clusters, C.Nonempty := by
  sorry

theorem restrict_laminar (σ : SpeciesTree X) (S : Finset X) :
    ∀ C ∈ restrictClusters S σ.clusters, ∀ D ∈ restrictClusters S σ.clusters,
      C ⊆ D ∨ D ⊆ C ∨ Disjoint C D := by
  sorry

/-- The length of the edge above the cluster `C` of the induced tree `σ(S)`: the sum of the
lengths of the edges above the clusters of `σ` whose trace on `S` is `C`. -/
noncomputable def restrictLength (σ : SpeciesTree X) (S : Finset X) (C : Finset S) : ℝ :=
  ∑ A ∈ σ.clusters with A ≠ univ ∧ A.subtype (· ∈ S) = C, σ.length A

theorem restrictLength_pos (σ : SpeciesTree X) (S : Finset X) :
    ∀ C ∈ restrictClusters S σ.clusters, C ≠ univ → 0 < σ.restrictLength S C := by
  sorry

/-- The induced species tree `σ⁺(S)` on a nonempty set of taxa `S`. -/
noncomputable def restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    SpeciesTree S where
  clusters := restrictClusters S σ.clusters
  univ_mem := σ.restrict_univ_mem S hS
  singleton_mem := σ.restrict_singleton_mem S
  nonempty_of_mem := σ.restrict_nonempty_of_mem S
  laminar := σ.restrict_laminar S
  length := σ.restrictLength S
  length_pos := σ.restrictLength_pos S

/-- The probability that the rooted gene tree (one lineage per taxon) displays the rooted triple
`ab|c`, that is, has a cluster containing `a` and `b` but not `c`. -/
noncomputable def rootedTripleProb (σ : SpeciesTree X) (a b c : X) : ℝ :=
  ∑ G, if ∃ C ∈ G, a ∈ C ∧ b ∈ C ∧ c ∉ C then σ.rootedDist id G else 0

end SpeciesTree

/-- The forest of `n` singleton lineages `{0}, …, {n - 1}`. -/
def singletonForest (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.image fun l => {l}

/-- The paper's `g_ij(t)` (Section 3): the probability that `i` lineages coalesce into `j`
lineages within time `t` under Kingman's coalescent, that is, that the forest reached from `i`
singletons after time `t` has `j` roots. -/
noncomputable def coalescenceProb (i j : ℕ) (t : ℝ) : ℝ :=
  ∑ G : Finset (Finset (Fin i)), if #(roots G) = j then kingmanTransition t (singletonForest i) G
    else 0

end ADR11
