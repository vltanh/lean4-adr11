module

public import ADR11.FiveTaxa.Basic
public import ADR11.MSC.Basic

/-!
# Section 5: nonbinary species trees

* `section5_threeTaxa`: for the unresolved 3-taxon species tree the three rooted gene trees are
  equiprobable; for a resolved one exactly one has probability greater than `1/3`.
* `section5_triples`: a species tree has no cluster separating one of three taxa from the other
  two exactly when the three rooted triples on them are equiprobable.
* `section5_proposition1`, `section5_corollary2`: Proposition 1 and Corollary 2 for species trees
  that need not be binary.
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

/-- Section 5: polytomies are identified by rooted triples, so Proposition 1 holds for species trees
that need not be binary: the probabilities of rooted triples determine the species tree topology
and its internal branch lengths. -/
theorem section5_proposition1 (hX : 3 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c → σ.rootedTripleProb a b c = σ'.rootedTripleProb a b c) :
    σ.SameRootedMetricTree σ' := by
  sorry

/-- Section 5: Corollary 2 for species trees that need not be binary. -/
theorem section5_corollary2 (hX : 3 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.rootedDist id = σ'.rootedDist id) : σ.SameRootedMetricTree σ' := by
  sorry

/-- Section 5: the gene tree probabilities of a nonbinary species tree are the limits of those of a
binary resolution `H` of it as the lengths of the added edges tend to `0`. -/
theorem section5_limit (σ : SpeciesTree X) {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hsub : σ.clusters ⊆ H) (T : Finset (Finset X)) :
    Filter.Tendsto
      (fun ε : ℝ => unrootedDistOf H (fun A => if A ∈ σ.clusters then σ.length A else ε) id T)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (σ.unrootedDist id T)) := by
  sorry

end ADR11
