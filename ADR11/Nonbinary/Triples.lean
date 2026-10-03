module

public import ADR11.Nonbinary
public import ADR11.Introduction.Proposition1

/-!
# Section 5: polytomies and rooted triples

* `section5_triples`: no cluster of the species tree contains exactly two of three taxa if and only
  if the three rooted triples on them are equiprobable.
* `section5_proposition1`, `section5_corollary2`: Proposition 1 and Corollary 2 for species trees
  that need not be binary.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]
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

end ADR11
