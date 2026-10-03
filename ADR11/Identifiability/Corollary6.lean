module

public import ADR11.Identifiability.Proposition3
public import ADR11.Identifiability.Unrooted

/-!
# Corollary 6: the unrooted metric species tree is identifiable

For any taxon set `X`, the unrooted gene tree distribution `ℙ_{σ⁺}` of a binary species tree
determines `σ⁻` (`corollary6`).

## Proof (the paper's)

For any quartet `Q ⊆ X`, by Lemma 5 `ℙ_{σ⁺}` determines `ℙ_{σ⁺(Q)}`
(`unrootedDist_restrict_eq`), so by Proposition 3, applied to the induced quartet trees, which
are binary (`SpeciesTree.restrict_isBinary`), it determines `σ⁻(Q)`. All induced quartet trees,
with their internal edge lengths, determine `σ⁻`: the topology by [Steel 1992], and the length
of each internal edge of `σ⁻` as the internal edge length of a quartet tree whose internal edge
it is (`SpeciesTree.sameUnrootedMetricTree_of_restrict`). With fewer than four taxa there is no
quartet and nothing to prove: `σ⁻` has no internal edge.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Corollary 6** (`cor:unroot`). For any `X`, `ℙ_{σ⁺}` determines `σ⁻`.

Proof (the paper's): by Lemma 5 the distribution determines that of every induced quartet tree
(`unrootedDist_restrict_eq`), hence by Proposition 3 every induced unrooted metric quartet tree,
hence `σ⁻` (`SpeciesTree.sameUnrootedMetricTree_of_restrict`, after [Steel 1992]). -/
theorem corollary6 (σ σ' : SpeciesTree X) (hσ : σ.IsBinary) (hσ' : σ'.IsBinary)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' :=
  SpeciesTree.sameUnrootedMetricTree_of_restrict σ σ' fun Q hQ hQ4 =>
    (proposition3 (by simpa using hQ4)).1 (σ.restrict Q hQ) (σ'.restrict Q hQ)
      (SpeciesTree.restrict_isBinary hσ Q hQ) (SpeciesTree.restrict_isBinary hσ' Q hQ)
      (unrootedDist_restrict_eq h Q hQ)

end ADR11
