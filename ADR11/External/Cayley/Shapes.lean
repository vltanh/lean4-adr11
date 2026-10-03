module

public import ADR11.MSC.Relabel
public import ADR11.SmallTrees

/-!
# Rooted tree shapes on three, four and five taxa

[A. Cayley, *On the theory of the analytical forms called trees*, Philos. Mag. 13 (1857)
172–176], cited in Section 5 of the paper: there are two unlabelled rooted shapes on three taxa,
five on four taxa and twelve on five taxa, binary or not. In the representation by hierarchies,
every hierarchy on `Fin n` is a relabelling of exactly one of the listed representatives.

* `shapes3`: `(a,b,c)` and `((a,b),c)`.
* `shapes4`: `(a,b,c,d)`, `((a,b),c,d)`, `((a,b,c),d)`, `((a,b),(c,d))`, `(((a,b),c),d)`.
* `shapes5`: the balanced tree, the caterpillar, the pseudocaterpillar and `P₁, …, P₉` of Table 6.
-/

@[expose] public section

namespace ADR11

open Finset

/-- The two rooted shapes on three taxa. -/
def shapes3 : ℕ → Finset (Finset (Fin 3))
  | 1 => hierarchyOf ∅
  | _ => hierarchyOf {{0, 1}}

/-- The five rooted shapes on four taxa. -/
def shapes4 : ℕ → Finset (Finset (Fin 4))
  | 1 => hierarchyOf ∅
  | 2 => hierarchyOf {{0, 1}}
  | 3 => hierarchyOf {{0, 1, 2}}
  | 4 => balanced4
  | _ => caterpillar4

/-- The twelve rooted shapes on five taxa: the three binary shapes of Fig. 2 and the nine
nonbinary representatives of Table 6. -/
def shapes5 : ℕ → Finset (Finset (Fin 5))
  | 1 => balanced5
  | 2 => caterpillar5
  | 3 => pseudocaterpillar5
  | k => polytomy5 (k - 3)

/-- Every hierarchy on `Fin n` (`n = 3, 4, 5`) is a relabelling of exactly one of the listed
shapes: two on three taxa, five on four taxa, twelve on five taxa. -/
theorem cayley_shapes :
    (∀ H : Finset (Finset (Fin 3)), IsHierarchy H →
      ∃! k, k ∈ Icc 1 2 ∧ ∃ π : Fin 3 ≃ Fin 3, H = relabelFamily π (shapes3 k)) ∧
    (∀ H : Finset (Finset (Fin 4)), IsHierarchy H →
      ∃! k, k ∈ Icc 1 5 ∧ ∃ π : Fin 4 ≃ Fin 4, H = relabelFamily π (shapes4 k)) ∧
    (∀ H : Finset (Finset (Fin 5)), IsHierarchy H →
      ∃! k, k ∈ Icc 1 12 ∧ ∃ π : Fin 5 ≃ Fin 5, H = relabelFamily π (shapes5 k)) := by
  sorry

end ADR11
