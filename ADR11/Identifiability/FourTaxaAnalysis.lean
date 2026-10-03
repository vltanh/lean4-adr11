module

public import ADR11.Rootings.Statements
public import ADR11.Trees.Classify

/-!
# The four-taxon analysis

On four taxa, the unrooted gene tree distribution determines exactly the unrooted metric species
tree (Proposition 3, Theorem 9 for `|X| = 4`): after relabelling, a species tree is a rooting of
`U4 1` (one internal edge, of length `t`) or of the star `U4 0`; by the closed forms of
`ADR11.Rootings.Statements`, the gene tree with the split of the species tree has probability
`1 - (2/3) e^{-t}` and the two others `(1/3) e^{-t}`, or all three have probability `1/3`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- On four taxa, two species trees have the same unrooted gene tree distribution exactly when
they have the same unrooted metric tree. -/
theorem unrootedDist_eq_iff_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  sorry

end ADR11
