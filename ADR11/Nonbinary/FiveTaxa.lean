module

public import ADR11.Nonbinary.FiveTaxa.StarOneSplit
public import ADR11.Nonbinary.FiveTaxa.TwoSplits
public import ADR11.Identifiability.Unrooted

/-!
# Propositions 7 and 8 for nonbinary species trees (Appendix C)

On five taxa the unrooted gene tree distribution determines the rooted metric species tree, binary
or not (`appC_sameRootedMetricTree`). The proof follows the order of Appendix C.

1. The rooted shape, unlabelled, is read off the classes of gene trees, without the unrooted
   species tree (l. 943–971): the size of the least probable class, the taxa in no cherry of the
   gene trees of the 3-element class (`P₂` versus `P₃`), the cherries shared by the gene trees of
   the two 2-element classes (`P₅` versus `P₇`), and the size of the class with the second smallest
   probability. This determines the shape up to the cases `P₄`/`P₈` and balanced/`P₆`
   (`sh_group_eq`, in `ADR11.Nonbinary.FiveTaxa.Shapes`).
2. The labelling (l. 973–986) uses the unrooted species tree, determined by the nonbinary
   Corollary 6 (`sameUnrootedMetricTree_of_unrootedDist_eq`: quartets after Bandelt–Dress). After
   relabelling the taxa it is the star `U5 0`, the tree `U5 1` with the split `ab|cde`, or the
   binary tree `U5 2` with the splits `ab|cde` and `abc|de`, and the species tree is one of its
   rootings. Within the shape group, the paper's rules give the labelled rooted tree:
   `ac1_rootings_zero`, `ac1_rootings_one` (`ADR11.Nonbinary.FiveTaxa.StarOneSplit`) and
   `ac2_rootings_two` (`ADR11.Nonbinary.FiveTaxa.TwoSplits`, with Proposition 8 for two binary
   trees).
3. The branch lengths (l. 988–993) are solved from the equations of Table 7 and Appendix B; `P₄` is
   told apart from `P₈`, and `P₆` from the balanced tree, by whether the solved `Z` is `1` or less.
-/

@[expose] public section

namespace ADR11

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Appendix C: on five taxa, two species trees, binary or not, with the same unrooted gene tree
distribution have the same rooted metric tree. -/
theorem appC_sameRootedMetricTree (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  -- (1) the unlabelled rooted shape, up to `P₄`/`P₈` and balanced/`P₆`, is read off the classes
  -- of gene trees (l. 943–971)
  have hg : sh_groupOf σ.clusters = sh_groupOf σ'.clusters := sh_group_eq hX σ σ' h
  -- (2) the labelling: the unrooted species tree is determined (Corollary 6, extended to nonbinary
  -- trees); name the taxa so that it is `U5 0`, `U5 1` or `U5 2`
  have hU := sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U5 hX σ
  have he' : unroot (σ'.relabel e.symm).clusters = U5 k := by
    rw [SpeciesTree.relabel_clusters, unroot_relabelFamily, ← hU.1, ← unroot_relabelFamily]
    exact he
  have hd := (SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm).2 h
  have hg' : sh_groupOf (σ.relabel e.symm).clusters = sh_groupOf (σ'.relabel e.symm).clusters := by
    rw [SpeciesTree.relabel_clusters, SpeciesTree.relabel_clusters, sh_groupOf_relabel,
      sh_groupOf_relabel]
    exact hg
  rw [← SpeciesTree.sameRootedMetricTree_relabel_iff σ σ' e.symm]
  -- within the shape group, the labelling rules for the rootings of `U5 k`, and then (3) the
  -- branch lengths
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · exact ac1_rootings_zero _ _ he he' hg' hd
  · exact ac1_rootings_one _ _ he he' hg' hd
  · exact ac2_rootings_two _ _ he he' hg' hd

end ADR11
