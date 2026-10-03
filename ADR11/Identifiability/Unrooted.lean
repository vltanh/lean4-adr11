module

public import ADR11.Identifiability.FourTaxaAnalysis
public import ADR11.Identifiability.Lemma5
public import ADR11.Identifiability.Quartets

/-!
# The unrooted metric species tree is identifiable (Corollary 6)

By Lemma 5 the unrooted gene tree distribution determines the distribution of every induced
quartet tree, hence by the four-taxon analysis every induced unrooted metric quartet tree, hence
the unrooted metric species tree, which is determined by its quartets [Steel 1992].
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Equal unrooted gene tree distributions give equal distributions on every induced subtree
(Lemma 5). -/
theorem unrootedDist_restrict_eq {σ σ' : SpeciesTree X}
    (h : σ.unrootedDist id = σ'.unrootedDist id) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).unrootedDist id = (σ'.restrict S hS).unrootedDist id := by
  funext T'
  rw [lemma5, lemma5, h]

/-- For any taxon set, the unrooted gene tree distribution determines the unrooted metric species
tree. -/
theorem sameUnrootedMetricTree_of_unrootedDist_eq (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' :=
  SpeciesTree.sameUnrootedMetricTree_of_restrict σ σ' fun Q hQ hQ4 =>
    (unrootedDist_eq_iff_four (by simpa using hQ4) _ _).1 (unrootedDist_restrict_eq h Q hQ)

end ADR11
