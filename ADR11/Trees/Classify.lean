module

public import ADR11.MSC.Relabel
public import ADR11.SmallTrees

/-!
# Unrooted trees on four and five taxa, and their rootings

Every species tree on four or five taxa is, after relabelling, a rooting of one of a few standard
unrooted trees, and the rootings of each standard unrooted tree are listed explicitly.

* Four taxa: `U4 1 = AB|CD` and the star `U4 0`; `rootings4 k` lists the hierarchies on `Fin 4`
  with unrooted tree `U4 k` (7 for `AB|CD`: four caterpillars, the balanced tree, and the two
  trees with one cherry and a trifurcating root; 5 for the star).
* Five taxa: `U5 2 = {AB|CDE, ABC|DE}`, `U5 1 = AB|CDE`, the star `U5 0`; `rootings5 k` lists the
  hierarchies on `Fin 5` with unrooted tree `U5 k` (10, 8 and 6 of them), and
  `binaryRootings5` the 7 binary ones with unrooted tree `U5 2`.

## Main results

* `exists_equiv_unroot_eq_U4`, `exists_equiv_unroot_eq_U5`: normal forms up to relabelling.
* `exists_equiv_unroot_eq_U5_two_of_isBinary`: a binary 5-taxon tree has unrooted shape `U5 2`.
* `mem_rootings4`, `mem_rootings5`, `mem_binaryRootings5`: the lists are complete.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The unrooted trees on `Fin 4`: `U4 1` has the split `AB|CD`, `U4 0` is the star. -/
def U4 : ℕ → Finset (Finset (Fin 4))
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

/-- The unrooted trees on `Fin 5`: `U5 2` has the splits `AB|CDE` and `ABC|DE`, `U5 1` the split
`AB|CDE`, and `U5 0` is the star. -/
def U5 : ℕ → Finset (Finset (Fin 5))
  | 2 => treeOfClusters {{0, 1}, {3, 4}}
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

/-- The hierarchies on `Fin 4` with unrooted tree `U4 k`. -/
def rootings4 : ℕ → Finset (Finset (Finset (Fin 4)))
  | 1 => {hierarchyOf {{0, 1}, {0, 1, 2}}, hierarchyOf {{0, 1}, {0, 1, 3}},
          hierarchyOf {{2, 3}, {0, 2, 3}}, hierarchyOf {{2, 3}, {1, 2, 3}},
          hierarchyOf {{0, 1}, {2, 3}}, hierarchyOf {{0, 1}}, hierarchyOf {{2, 3}}}
  | _ => {hierarchyOf ∅, hierarchyOf {{0, 1, 2}}, hierarchyOf {{0, 1, 3}},
          hierarchyOf {{0, 2, 3}}, hierarchyOf {{1, 2, 3}}}

/-- The hierarchies on `Fin 5` with unrooted tree `U5 k`. -/
def rootings5 : ℕ → Finset (Finset (Finset (Fin 5)))
  | 2 => {hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}, hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}},
          hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}, hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}},
          hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}},
          hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}},
          hierarchyOf {{0, 1}, {3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2}},
          hierarchyOf {{3, 4}, {2, 3, 4}}}
  | 1 => {hierarchyOf {{0, 1}}, hierarchyOf {{2, 3, 4}}, hierarchyOf {{0, 1}, {2, 3, 4}},
          hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}, hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}},
          hierarchyOf {{0, 1}, {0, 1, 3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2, 4}},
          hierarchyOf {{0, 1}, {0, 1, 2, 3}}}
  | _ => {hierarchyOf ∅, hierarchyOf {{1, 2, 3, 4}}, hierarchyOf {{0, 2, 3, 4}},
          hierarchyOf {{0, 1, 3, 4}}, hierarchyOf {{0, 1, 2, 4}}, hierarchyOf {{0, 1, 2, 3}}}

/-- The seven binary rootings of `U5 2` (roots on the pendant edges of `e`, `d`, `a`, `b`, `c`,
and on the internal edges `ABC|DE` and `AB|CDE`). -/
def binaryRootings5 : Finset (Finset (Finset (Fin 5))) :=
  {hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}, hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}},
   hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}, hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}},
   hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}},
   hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}}}

/-- Normal form on four taxa. -/
theorem exists_equiv_unroot_eq_U4 (hX : Fintype.card X = 4) (σ : SpeciesTree X) :
    ∃ e : Fin 4 ≃ X, ∃ k ∈ ({0, 1} : Finset ℕ), unroot (σ.relabel e.symm).clusters = U4 k := by
  sorry

/-- Normal form on five taxa. -/
theorem exists_equiv_unroot_eq_U5 (hX : Fintype.card X = 5) (σ : SpeciesTree X) :
    ∃ e : Fin 5 ≃ X, ∃ k ∈ ({0, 1, 2} : Finset ℕ),
      unroot (σ.relabel e.symm).clusters = U5 k := by
  sorry

/-- A binary 5-taxon species tree has unrooted shape `U5 2`. -/
theorem exists_equiv_unroot_eq_U5_two_of_isBinary (hX : Fintype.card X = 5) (σ : SpeciesTree X)
    (hσ : σ.IsBinary) :
    ∃ e : Fin 5 ≃ X, unroot (σ.relabel e.symm).clusters = U5 2 := by
  sorry

theorem mem_rootings4 (τ : SpeciesTree (Fin 4)) (k : ℕ) (hk : k ∈ ({0, 1} : Finset ℕ))
    (h : unroot τ.clusters = U4 k) : τ.clusters ∈ rootings4 k := by
  sorry

theorem mem_rootings5 (τ : SpeciesTree (Fin 5)) (k : ℕ) (hk : k ∈ ({0, 1, 2} : Finset ℕ))
    (h : unroot τ.clusters = U5 k) : τ.clusters ∈ rootings5 k := by
  sorry

theorem mem_binaryRootings5 (τ : SpeciesTree (Fin 5)) (hτ : τ.IsBinary)
    (h : unroot τ.clusters = U5 2) : τ.clusters ∈ binaryRootings5 := by
  sorry

end ADR11
