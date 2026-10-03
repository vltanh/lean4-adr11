module

public import ADR11.SmallTrees

/-!
# Section 6 (Discussion)

The Discussion remarks that, for the species tree `((((a,b):x,c):y,d):z,e)` with `y` large,
determining that `e` is the outgroup "would require observing conflicting splits, such as that
`ABD|CE` is more probable than `ABE|CD`". For this species tree the inequality goes the other way
(the split `ABE|CD` of `T₃, T₁₀, T₁₅` is more probable than `ABD|CE` of `T₂, T₇, T₁₄`), as in the
proof of Proposition 7; `discussion_splits` records the correct direction.
-/

@[expose] public section

namespace ADR11

open Finset

/-- The probability that the unrooted gene tree has the split `A | Aᶜ`. -/
noncomputable def splitProb {X : Type*} [Fintype X] [DecidableEq X] (σ : SpeciesTree X)
    (A : Finset X) : ℝ :=
  ∑ T, if A ∈ T then σ.unrootedDist id T else 0

/-- For the caterpillar species tree `((((a,b),c),d),e)`, the split `ABE|CD` is strictly more
probable than the split `ABD|CE`, for all branch lengths. -/
theorem discussion_splits (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    splitProb σ {0, 1, 3} < splitProb σ {0, 1, 4} := by
  sorry

end ADR11
