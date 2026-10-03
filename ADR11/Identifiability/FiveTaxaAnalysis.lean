module

public import ADR11.Identifiability.Unrooted
public import ADR11.Rootings.Statements
public import ADR11.Trees.Classify
public import ADR11.Identifiability.FiveTaxa.TwoSplits
public import ADR11.Identifiability.FiveTaxa.OneSplit
public import ADR11.Identifiability.FiveTaxa.Star

/-!
# The five-taxon analysis (Propositions 7 and 8)

On five taxa, the unrooted gene tree distribution determines the rooted metric species tree. After
relabelling, a species tree is a rooting of one of the standard unrooted trees `U5 2`, `U5 1`,
`U5 0` (`ADR11.rootings5`), and two species trees with the same distribution have the same
unrooted metric tree (Corollary 6), hence are rootings of the same standard tree with the same
internal edge lengths. The closed forms of `ADR11.Rootings.Statements` then separate the rootings:
signs of differences of gene tree probabilities locate the root, as in the proof of Proposition 7
(for the caterpillar `u₃ > u₂`; on `U5 2` the signs of `u₂ - u₃`, `u₄ - u₁₃`, `u₅ - u₈` and
`u₅ - u₇` are used), except that a root on an internal edge of the unrooted tree is told apart
from the root at an adjacent node (the limit where one of the two edges below the root has
length `0`) by comparing one probability with the lengths of the internal edges of the unrooted
tree. The remaining length is read off a single probability, as in equations (7)–(9). The case
analysis for each standard unrooted tree is in `ADR11.Identifiability.FiveTaxa.TwoSplits`
(`U5 2`), `ADR11.Identifiability.FiveTaxa.OneSplit` (`U5 1`) and
`ADR11.Identifiability.FiveTaxa.Star` (`U5 0`).
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
  obtain ⟨e, k, hk, hU⟩ := exists_equiv_unroot_eq_U5 hX σ
  rw [← SpeciesTree.sameRootedMetricTree_relabel_iff σ σ' e.symm]
  have hd : (σ.relabel e.symm).unrootedDist id = (σ'.relabel e.symm).unrootedDist id :=
    (SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm).2 h
  have hm := sameUnrootedMetricTree_of_unrootedDist_eq _ _ hd
  have hU' : unroot (σ'.relabel e.symm).clusters = U5 k := hm.1.symm.trans hU
  have hR := mem_rootings5 _ k hk hU
  have hR' := mem_rootings5 _ k hk hU'
  have hu : u (σ.relabel e.symm) = u (σ'.relabel e.symm) := funext fun i => congrFun hd (T5 i)
  have ht : ∀ A : Finset (Fin 5), A ∈ U5 k → 2 ≤ #A → 2 ≤ #Aᶜ →
      (σ.relabel e.symm).unrootedLength A = (σ'.relabel e.symm).unrootedLength A :=
    fun A hA => hm.2 A (by rw [hU]; exact hA)
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · exact five_sameRootedMetricTree_zero _ _ hR hR' hu
  · exact five_sameRootedMetricTree_one _ _ hR hR' hu
      (ht {0, 1} (by decide) (by decide) (by decide))
  · exact five_sameRootedMetricTree_two _ _ hR hR' hu
      (ht {0, 1} (by decide) (by decide) (by decide))
      (ht {3, 4} (by decide) (by decide) (by decide))

end ADR11
