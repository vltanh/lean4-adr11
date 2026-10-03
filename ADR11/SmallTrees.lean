module

public import ADR11.Basic

/-!
# Small species trees and gene trees used in the paper

Taxa are labelled `a, b, c, d, e = 0, 1, 2, 3, 4` (types `Fin 3`, `Fin 4`, `Fin 5`), and gene
lineages carry the same labels (`A, B, C, D, E` in the paper).

* `treeOfClusters C`: the unrooted tree whose nontrivial splits are `A | Aᶜ` for `A ∈ C`,
  in the representation of `ADR11.unroot`.
* `T5 i` (`1 ≤ i ≤ 15`): the paper's unrooted 5-taxon gene tree `T_i` (Table 5), given by one side
  of each of its two nontrivial splits.
* Cluster sets of the rooted species tree shapes: on 3 taxa `((a,b),c)`; on 4 taxa the balanced
  tree `((a,b),(c,d))` and the caterpillar `(((a,b),c),d)` (Fig. 2a, b); on 5 taxa the balanced
  tree `(((a,b),c),(d,e))`, the caterpillar `((((a,b),c),d),e)` and the pseudocaterpillar
  `(((a,b),(d,e)),c)` (Fig. 2c–e), and the nine nonbinary representatives `P₁, …, P₉` of Table 6.
* Species trees with these shapes and given internal edge lengths; pendant edges get length `1`,
  which does not affect the distributions with one lineage per taxon.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The unrooted tree with the nontrivial splits `A | Aᶜ`, `A ∈ C` (and all trivial splits). -/
def treeOfClusters (C : Finset (Finset X)) : Finset (Finset X) :=
  unroot (insert univ (C ∪ univ.image fun x => {x}))

/-- The hierarchy with the given nontrivial clusters `C`, together with `univ` and the
singletons. -/
def hierarchyOf (C : Finset (Finset X)) : Finset (Finset X) :=
  insert univ (C ∪ univ.image fun x => {x})

/-! ### Three taxa -/

/-- The rooted species tree `((a,b),c)` on three taxa. -/
def clusters3 : Finset (Finset (Fin 3)) := hierarchyOf {{0, 1}}

/-- The rooted gene tree on three lineages with cherry `A` (a 2-element set). -/
def rootedTree3 (A : Finset (Fin 3)) : Finset (Finset (Fin 3)) := hierarchyOf {A}

/-! ### Four taxa -/

/-- The balanced species tree `((a,b),(c,d))` (Fig. 2a). -/
def balanced4 : Finset (Finset (Fin 4)) := hierarchyOf {{0, 1}, {2, 3}}

/-- The rooted caterpillar species tree `(((a,b),c),d)` (Fig. 2b). -/
def caterpillar4 : Finset (Finset (Fin 4)) := hierarchyOf {{0, 1}, {0, 1, 2}}

/-! ### Five taxa -/

/-- The balanced species tree `(((a,b),c),(d,e))` (Fig. 2c). -/
def balanced5 : Finset (Finset (Fin 5)) := hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}}

/-- The rooted caterpillar species tree `((((a,b),c),d),e)` (Fig. 2d). -/
def caterpillar5 : Finset (Finset (Fin 5)) := hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}

/-- The pseudocaterpillar species tree `(((a,b),(d,e)),c)` (Fig. 2e). -/
def pseudocaterpillar5 : Finset (Finset (Fin 5)) := hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}

/-- The nine nonbinary rooted 5-taxon shapes of Table 6, with the labellings given there:
`P₁ = (a,b,c,d,e)`, `P₂ = (a,b,c,(d,e))`, `P₃ = ((a,b,c,d),e)`, `P₄ = ((a,b,c),d,e)`,
`P₅ = ((a,b),(d,e),c)`, `P₆ = (((a,b),c),d,e)`, `P₇ = (((a,b),d,e),c)`, `P₈ = ((a,b,c),(d,e))`,
`P₉ = (((a,b,c),d),e)`. -/
def polytomy5 : ℕ → Finset (Finset (Fin 5))
  | 1 => hierarchyOf ∅
  | 2 => hierarchyOf {{3, 4}}
  | 3 => hierarchyOf {{0, 1, 2, 3}}
  | 4 => hierarchyOf {{0, 1, 2}}
  | 5 => hierarchyOf {{0, 1}, {3, 4}}
  | 6 => hierarchyOf {{0, 1}, {0, 1, 2}}
  | 7 => hierarchyOf {{0, 1}, {0, 1, 3, 4}}
  | 8 => hierarchyOf {{0, 1, 2}, {3, 4}}
  | 9 => hierarchyOf {{0, 1, 2}, {0, 1, 2, 3}}
  | _ => ∅

/-- The paper's unrooted 5-taxon gene trees `T₁, …, T₁₅` (Table 5), each given by one side of
each of its two nontrivial splits. For instance `T₁` has the splits `AB|CDE` and `ABC|DE`. -/
def T5 : ℕ → Finset (Finset (Fin 5))
  | 1 => treeOfClusters {{0, 1}, {0, 1, 2}}
  | 2 => treeOfClusters {{0, 1}, {0, 1, 3}}
  | 3 => treeOfClusters {{0, 1}, {0, 1, 4}}
  | 4 => treeOfClusters {{0, 2}, {0, 1, 2}}
  | 5 => treeOfClusters {{0, 2}, {0, 2, 3}}
  | 6 => treeOfClusters {{0, 2}, {0, 2, 4}}
  | 7 => treeOfClusters {{0, 3}, {0, 1, 3}}
  | 8 => treeOfClusters {{0, 3}, {0, 2, 3}}
  | 9 => treeOfClusters {{0, 3}, {0, 3, 4}}
  | 10 => treeOfClusters {{0, 4}, {0, 1, 4}}
  | 11 => treeOfClusters {{0, 4}, {0, 2, 4}}
  | 12 => treeOfClusters {{0, 4}, {0, 3, 4}}
  | 13 => treeOfClusters {{1, 2}, {0, 1, 2}}
  | 14 => treeOfClusters {{1, 3}, {0, 1, 3}}
  | 15 => treeOfClusters {{1, 4}, {0, 1, 4}}
  | _ => ∅

/-- `u σ i = ℙ_σ(T_i)`, the probability of the unrooted gene tree `T_i` under the multispecies
coalescent on a 5-taxon species tree `σ`, with one lineage per taxon. -/
noncomputable def u (σ : SpeciesTree (Fin 5)) (i : ℕ) : ℝ :=
  σ.unrootedDist id (T5 i)

/-- The vector `(u₁, …, u₁₅)`, indexed by `Fin 15` (`i ↦ u_{i+1}`). -/
noncomputable def uVec (σ : SpeciesTree (Fin 5)) : Fin 15 → ℝ :=
  fun i => u σ (i.val + 1)

/-! ### Species trees with given internal edge lengths -/

/-- A species tree with the clusters `H` and the internal edge lengths `len` (pendant edges get
length `1`). -/
noncomputable def SpeciesTree.ofLengths (H : Finset (Finset X)) (len : Finset X → ℝ)
    (h₁ : univ ∈ H) (h₂ : ∀ x : X, {x} ∈ H) (h₃ : ∀ A ∈ H, A.Nonempty)
    (h₄ : ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (h₅ : ∀ A ∈ H, A ≠ univ → 2 ≤ #A → 0 < len A) : SpeciesTree X where
  clusters := H
  univ_mem := h₁
  singleton_mem := h₂
  nonempty_of_mem := h₃
  laminar := h₄
  length A := if #A ≤ 1 then 1 else len A
  length_pos A hA hne := by
    split_ifs with h
    · exact one_pos
    · exact h₅ A hA hne (by omega)

end ADR11
