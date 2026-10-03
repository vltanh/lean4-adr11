module

public import ADR11.Computation.Toolkit

/-!
# Rooted gene tree probabilities in the 5-taxon caterpillar species tree

The two worked examples of Section 3 of the paper, for the caterpillar species tree
`((((a,b):x,c):y,d):z,e)` (`caterpillar5`), with `X = e^{-x}`, `Y = e^{-y}`, `Z = e^{-z}`:

* `rootedDist_cat5_example1`: `ℙ(((((B,E),A),C),D)) = X Y³ Z⁶ / 180`;
* `rootedDist_cat5_example2`: `ℙ((((B,E),A),(C,D))) = X Y³ Z³ / 54 - X Y³ Z⁶ / 540`.

`cat5Shape` is the tree shape of `caterpillar5` for the engine of `ADR11.Computation.Toolkit`.
-/

@[expose] public section

namespace ADR11.Computation

open Finset Real

/-- The tree shape of the caterpillar `((((a,b),c),d),e)` on `Fin 5`. -/
def cat5Shape : PTree :=
  .node 31 [.node 15 [.node 7 [.node 3 [.leaf 0, .leaf 1], .leaf 2], .leaf 3], .leaf 4]

theorem cat5Shape_wfB : cat5Shape.wfB 5 caterpillar5 = true := by decide +kernel

theorem decC_cat5 : decC 5 3 = {0, 1} ∧ decC 5 7 = {0, 1, 2} ∧ decC 5 15 = {0, 1, 2, 3} := by
  decide +kernel

/-- Section 3, first example: `ℙ(((((B,E),A),C),D)) = X Y³ Z⁶ / 180`. -/
theorem rootedDist_cat5_example1 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    σ.rootedDist id (hierarchyOf {{1, 4}, {0, 1, 4}, {0, 1, 2, 4}}) =
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 *
        exp (-σ.length {0, 1, 2, 3}) ^ 6 / 180 := by
  rw [rootedDist_eq_evalPoly σ hσ cat5Shape cat5Shape_wfB rfl
    (g := [1, 2, 4, 8, 16, 18, 19, 23, 31]) (by decide +kernel)
    (P := [(1 / 180, [(3, 1), (7, 3), (15, 6)])]) (by decide +kernel)]
  obtain ⟨h3, h7, h15⟩ := decC_cat5
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h3, h7, h15]
  push_cast
  ring

/-- Section 3, second example: `ℙ((((B,E),A),(C,D))) = X Y³ Z³ / 54 - X Y³ Z⁶ / 540`. -/
theorem rootedDist_cat5_example2 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    σ.rootedDist id (hierarchyOf {{1, 4}, {0, 1, 4}, {2, 3}}) =
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 *
          exp (-σ.length {0, 1, 2, 3}) ^ 3 / 54 -
        exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 *
          exp (-σ.length {0, 1, 2, 3}) ^ 6 / 540 := by
  rw [rootedDist_eq_evalPoly σ hσ cat5Shape cat5Shape_wfB rfl
    (g := [1, 2, 4, 8, 16, 18, 19, 12, 31]) (by decide +kernel)
    (P := [(1 / 54, [(3, 1), (7, 3), (15, 3)]), (-1 / 540, [(3, 1), (7, 3), (15, 6)])])
    (by decide +kernel)]
  obtain ⟨h3, h7, h15⟩ := decC_cat5
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h3, h7, h15]
  push_cast
  ring

end ADR11.Computation
