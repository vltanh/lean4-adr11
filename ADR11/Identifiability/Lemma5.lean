module

public import ADR11.Basic

/-!
# Lemma 5: marginalization

The distribution of the gene trees induced on a subset `S` of the taxa is the distribution under
the induced species tree `σ⁺(S)`: for unrooted gene trees (Lemma 5) and, as the paper remarks, for
rooted gene trees.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Lemma 5.** If `S ⊆ X` and `T' ∈ 𝒯_S`, then
`ℙ_{σ⁺(S)}(T') = ∑_{T ∈ 𝒯_X, T(S) = T'} ℙ_{σ⁺}(T)`. -/
theorem lemma5 (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) (T' : Finset (Finset S)) :
    (σ.restrict S hS).unrootedDist id T' =
      ∑ T, if restrictSplits S T = T' then σ.unrootedDist id T else 0 := by
  sorry

/-- The analogue of Lemma 5 for rooted gene trees. -/
theorem lemma5_rooted (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty)
    (G' : Finset (Finset S)) :
    (σ.restrict S hS).rootedDist id G' =
      ∑ G, if restrictClusters S G = G' then σ.rootedDist id G else 0 := by
  sorry

end ADR11
