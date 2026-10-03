module

public import ADR11.Trees.Hierarchy

/-!
# Unrooted trees are determined by their quartets

[M. Steel, *The complexity of reconstructing trees from qualitative characters and subtrees*,
J. Classification 9 (1992) 91–116], used in the proofs of Corollary 6 (binary trees) and of
Theorem 9 (Proposition 6 there: every internal edge is distinguished by a quartet); for trees
that need not be binary, [H.-J. Bandelt, A. Dress, *Reconstructing the shape of a tree from
observed dissimilarity data*, Adv. Appl. Math. 7 (1986) 309–343] and [C. Semple, M. Steel,
*Phylogenetics*, Oxford University Press, 2003, Theorem 6.3.5], used in the proof of
Proposition 11.

In the representation of `ADR11.unroot`, these are statements about the sets of splits of the
unrooted trees `σ⁻` of species trees:

* `mem_unroot_iff_quartets`: a bipartition `A | Aᶜ` with `|A|, |Aᶜ| ≥ 2` is a split of `σ⁻` if and
  only if every quartet `aa'|bb'` with `a, a' ∈ A` and `b, b' ∈ Aᶜ` is displayed by `σ⁻`.
* `exists_distinguishing_quartet`: every internal edge of `σ⁻` is the only edge of `σ⁻` separating
  some quartet `aa'|bb'` (Steel's Proposition 6, for trees that need not be binary).
* `SpeciesTree.sameUnrootedMetricTree_of_restrict`: two species trees whose induced unrooted
  metric trees agree on every set of four taxa have the same unrooted metric tree.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A split `A | Aᶜ` (with both sides of size at least 2) is a split of `σ⁻` if and only if every
quartet `aa'|bb'` (`a ≠ a'` in `A`, `b ≠ b'` in `Aᶜ`) is displayed by `σ⁻`, that is, separated by
some split of `σ⁻`. -/
theorem mem_unroot_iff_quartets (σ : SpeciesTree X) {A : Finset X} (hA : 2 ≤ #A)
    (hA' : 2 ≤ #Aᶜ) :
    A ∈ unroot σ.clusters ↔
      ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ Aᶜ, ∀ b' ∈ Aᶜ, a ≠ a' → b ≠ b' →
        ∃ C ∈ unroot σ.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C ∧ b' ∉ C := by
  sorry

/-- Steel's Proposition 6: every internal edge `A | Aᶜ` of `σ⁻` is the only split of `σ⁻`
separating some quartet `aa'|bb'`. -/
theorem exists_distinguishing_quartet (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA₁ : 2 ≤ #A) (hA₂ : 2 ≤ #Aᶜ) :
    ∃ a ∈ A, ∃ a' ∈ A, ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, a ≠ a' ∧ b ≠ b' ∧
      ∀ C ∈ unroot σ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A := by
  sorry

/-- Unrooted metric trees are determined by their quartets. -/
theorem SpeciesTree.sameUnrootedMetricTree_of_restrict (σ σ' : SpeciesTree X)
    (h : ∀ Q : Finset X, ∀ hQ : Q.Nonempty, #Q = 4 →
      (σ.restrict Q hQ).SameUnrootedMetricTree (σ'.restrict Q hQ)) :
    σ.SameUnrootedMetricTree σ' := by
  sorry

end ADR11
