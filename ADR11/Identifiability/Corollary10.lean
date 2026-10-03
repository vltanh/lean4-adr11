module

public import ADR11.Basic
public import ADR11.Nonbinary.Proposition11

/-!
# Corollary 10: several lineages per taxon

With `ℓ_x > 0` lineages sampled from each taxon `x`, the unrooted gene tree distribution
determines the rooted species tree, its internal edge lengths, and the pendant edge lengths of
the taxa sampled at least twice, provided `|X| ≥ 4` and some `ℓ_x ≥ 2`, or `|X| = 3` and two of the
`ℓ_x` are at least `2`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Corollary 10.** Consider the distribution of unrooted topological gene trees under the
multispecies coalescent with `ℓ_x > 0` lineages sampled from each taxon `x` (lineages
`(x, k)`, `k < ℓ_x`). Suppose that either `|X| ≥ 4` and some `ℓ_x ≥ 2`, or `|X| = 3` and at least
two of the `ℓ_x` are `≥ 2`. Then the gene tree distribution determines the species tree's rooted
topology, its internal edge lengths, and the length of the pendant edge of every taxon `x` with
`ℓ_x > 1`. -/
theorem corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X) (hσ : σ.IsBinary) (hσ' : σ'.IsBinary)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} :=
  proposition11_corollary10 ℓ hℓ hcond σ σ' h

end ADR11
