module

public import ADR11.Nonbinary.FourTaxa
public import ADR11.Identifiability.Lemma5
public import ADR11.Identifiability.Quartets

/-!
# The unrooted metric species tree is identifiable, binary or not (Corollary 6, Appendix C)

By Lemma 5 the unrooted gene tree distribution determines the distribution of every induced
quartet tree (`unrootedDist_restrict_eq`), hence by the four-taxon analysis, which covers resolved
and unresolved quartet trees (`unrootedDist_eq_iff_four`, Section 5), every induced unrooted metric
quartet tree, hence the unrooted metric species tree, which is determined by its quartets
[Steel 1992]. This is Corollary 6 for species trees that need not be binary (Appendix C,
l.940–941); the binary Corollary 6 (`corollary6`) uses Proposition 3 instead.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- For any taxon set, the unrooted gene tree distribution determines the unrooted metric species
tree. -/
theorem sameUnrootedMetricTree_of_unrootedDist_eq (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' :=
  SpeciesTree.sameUnrootedMetricTree_of_restrict σ σ' fun Q hQ hQ4 =>
    (unrootedDist_eq_iff_four (by simpa using hQ4) _ _).1 (unrootedDist_restrict_eq h Q hQ)

end ADR11
