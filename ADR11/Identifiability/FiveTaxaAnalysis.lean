module

public import ADR11.Identifiability.Unrooted
public import ADR11.Rootings.Statements
public import ADR11.Trees.Classify

/-!
# The five-taxon analysis (Propositions 7 and 8)

On five taxa, the unrooted gene tree distribution determines the rooted metric species tree. After
relabelling, a species tree is a rooting of one of the standard unrooted trees `U5 2`, `U5 1`,
`U5 0` (`ADR11.rootings5`), and two species trees with the same distribution have the same
unrooted metric tree (Corollary 6), hence are rootings of the same standard tree with the same
internal edge lengths. The closed forms of `ADR11.Rootings.Statements` then separate the rootings:
signs of differences such as `u₇ - u₈`, `u₃ - u₂` and `u₁₃ - u₄` locate the root, as in the proof
of Proposition 7 (the 6-element least probable class of the balanced tree contains `T₇`; for the
caterpillar `u₃ > u₂`), and the remaining length is read off a single probability, as in
equations (7)–(9).
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- On five taxa, the unrooted gene tree distribution determines the rooted metric species
tree. -/
theorem sameRootedMetricTree_of_unrootedDist_eq_five (hX : Fintype.card X = 5)
    (σ σ' : SpeciesTree X) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := by
  sorry

end ADR11
