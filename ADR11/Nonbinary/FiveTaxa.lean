module

public import ADR11.Nonbinary.FiveTaxa.StarOneSplit
public import ADR11.Nonbinary.FiveTaxa.TwoSplits
public import ADR11.Identifiability.Unrooted

/-!
# Propositions 7 and 8 for nonbinary species trees (Appendix C)

On five taxa the unrooted gene tree distribution determines the rooted metric species tree, binary
or not (`appC_sameRootedMetricTree`). As in Appendix C, the unrooted metric tree is determined
first, by the nonbinary Corollary 6 (`sameUnrootedMetricTree_of_unrootedDist_eq`: quartets after
Bandelt–Dress). After relabelling the taxa it is the star `U5 0`, the tree `U5 1` with the split
`ab|cde`, or the binary tree `U5 2` with the splits `ab|cde` and `abc|de`, and the species tree is
one of its rootings. Appendix C's argument for the rootings of each of these trees is in
`ADR11.Nonbinary.FiveTaxa.StarOneSplit` (`ac1_rootings_zero`, `ac1_rootings_one`) and
`ADR11.Nonbinary.FiveTaxa.TwoSplits` (`ac2_rootings_two`, which uses Proposition 8 for two binary
trees).
-/

@[expose] public section

namespace ADR11

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Appendix C: on five taxa, two species trees, binary or not, with the same unrooted gene tree
distribution have the same rooted metric tree. -/
theorem appC_sameRootedMetricTree (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  -- the unrooted metric tree is determined (Corollary 6, extended to nonbinary trees)
  have hU := sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h
  -- name the taxa so that the unrooted tree is one of `U5 0`, `U5 1`, `U5 2`
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U5 hX σ
  have he' : unroot (σ'.relabel e.symm).clusters = U5 k := by
    rw [SpeciesTree.relabel_clusters, unroot_relabelFamily, ← hU.1, ← unroot_relabelFamily]
    exact he
  have hd := (SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm).2 h
  rw [← SpeciesTree.sameRootedMetricTree_relabel_iff σ σ' e.symm]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · exact ac1_rootings_zero _ _ he he' hd
  · exact ac1_rootings_one _ _ he he' hd
  · exact ac2_rootings_two _ _ he he' hd

end ADR11
