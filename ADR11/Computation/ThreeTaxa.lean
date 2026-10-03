module

public import ADR11.Computation.Toolkit

/-!
# Gene tree distributions of 3-taxon species trees

With one lineage per taxon on `Fin 3`, the rooted gene trees are `rootedTree3 {0, 1}`,
`rootedTree3 {0, 2}` and `rootedTree3 {1, 2}`.

* `rootedDist_three_01`, `rootedDist_three_02`, `rootedDist_three_12`: the rooted gene tree
  distributions of the binary species trees `((a,b):t,c)`, `((a,c):t,b)`, `((b,c):t,a)`, as
  functions of the gene tree.
* `rootedDist_three_star`: the unresolved species tree `(a,b,c)` gives probability `1/3` to each.
* `clusters_eq_of_isBinary_three`: the binary hierarchies on `Fin 3`.
-/

@[expose] public section

namespace ADR11.Computation

open Finset Real

/-- The codes of the rooted gene tree `rootedTree3 A` on `Fin 3`, `a` being the code of `A`. -/
def tripleCode (a : ℕ) : List ℕ := [1, 2, 4, a, 7]

theorem decF_tripleCode_3 : decF 3 (tripleCode 3) = rootedTree3 {0, 1} := by decide +kernel

theorem decF_tripleCode_5 : decF 3 (tripleCode 5) = rootedTree3 {0, 2} := by decide +kernel

theorem decF_tripleCode_6 : decF 3 (tripleCode 6) = rootedTree3 {1, 2} := by decide +kernel

theorem rootedTree3_ne_01_02 : rootedTree3 {0, 1} ≠ rootedTree3 {0, 2} := by decide +kernel

theorem rootedTree3_ne_01_12 : rootedTree3 {0, 1} ≠ rootedTree3 {1, 2} := by decide +kernel

theorem rootedTree3_ne_02_12 : rootedTree3 {0, 2} ≠ rootedTree3 {1, 2} := by decide +kernel

/-- A rooted gene tree distribution on `Fin 3` computed by the engine, as a function of the gene
tree. -/
theorem rootedDist_eq_triples (σ : SpeciesTree (Fin 3)) {H : Finset (Finset (Fin 3))}
    (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB 3 H = true) (htop : T.code = 7)
    {P₁ P₂ P₃ : List (ℚ × List (ℕ × ℕ))}
    (hc : certAllB 3 (T.rootedL 3 3 id)
      [(tripleCode 3, P₁), (tripleCode 5, P₂), (tripleCode 6, P₃)] = true)
    (G : Finset (Finset (Fin 3))) :
    σ.rootedDist id G =
      if G = rootedTree3 {0, 1} then evalPoly σ.length P₁
      else if G = rootedTree3 {0, 2} then evalPoly σ.length P₂
      else if G = rootedTree3 {1, 2} then evalPoly σ.length P₃ else 0 :=
  rootedDist_eq_ite₃ σ hσ T hwf htop hc decF_tripleCode_3 decF_tripleCode_5 decF_tripleCode_6
    rootedTree3_ne_01_02 rootedTree3_ne_01_12 rootedTree3_ne_02_12 G

/-- The rooted gene tree distribution of `((a,b):t,c)` [Nei 1987]. -/
theorem rootedDist_three_01 (σ : SpeciesTree (Fin 3)) (hσ : σ.clusters = hierarchyOf {{0, 1}})
    (G : Finset (Finset (Fin 3))) :
    σ.rootedDist id G =
      if G = rootedTree3 {0, 1} then 1 - 2 / 3 * exp (-σ.length {0, 1})
      else if G = rootedTree3 {0, 2} then 1 / 3 * exp (-σ.length {0, 1})
      else if G = rootedTree3 {1, 2} then 1 / 3 * exp (-σ.length {0, 1}) else 0 := by
  rw [rootedDist_eq_triples σ hσ (.node 7 [.node 3 [.leaf 0, .leaf 1], .leaf 2])
    (by decide +kernel) rfl (P₁ := [(1, []), (-2 / 3, [(3, 1)])]) (P₂ := [(1 / 3, [(3, 1)])])
    (P₃ := [(1 / 3, [(3, 1)])]) (by decide +kernel)]
  have h : decC 3 3 = {0, 1} := by decide +kernel
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h]
  push_cast
  split_ifs <;> ring

/-- The rooted gene tree distribution of `((a,c):t,b)`. -/
theorem rootedDist_three_02 (σ : SpeciesTree (Fin 3)) (hσ : σ.clusters = hierarchyOf {{0, 2}})
    (G : Finset (Finset (Fin 3))) :
    σ.rootedDist id G =
      if G = rootedTree3 {0, 1} then 1 / 3 * exp (-σ.length {0, 2})
      else if G = rootedTree3 {0, 2} then 1 - 2 / 3 * exp (-σ.length {0, 2})
      else if G = rootedTree3 {1, 2} then 1 / 3 * exp (-σ.length {0, 2}) else 0 := by
  rw [rootedDist_eq_triples σ hσ (.node 7 [.node 5 [.leaf 0, .leaf 2], .leaf 1])
    (by decide +kernel) rfl (P₁ := [(1 / 3, [(5, 1)])]) (P₂ := [(1, []), (-2 / 3, [(5, 1)])])
    (P₃ := [(1 / 3, [(5, 1)])]) (by decide +kernel)]
  have h : decC 3 5 = {0, 2} := by decide +kernel
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h]
  push_cast
  split_ifs <;> ring

/-- The rooted gene tree distribution of `((b,c):t,a)`. -/
theorem rootedDist_three_12 (σ : SpeciesTree (Fin 3)) (hσ : σ.clusters = hierarchyOf {{1, 2}})
    (G : Finset (Finset (Fin 3))) :
    σ.rootedDist id G =
      if G = rootedTree3 {0, 1} then 1 / 3 * exp (-σ.length {1, 2})
      else if G = rootedTree3 {0, 2} then 1 / 3 * exp (-σ.length {1, 2})
      else if G = rootedTree3 {1, 2} then 1 - 2 / 3 * exp (-σ.length {1, 2}) else 0 := by
  rw [rootedDist_eq_triples σ hσ (.node 7 [.node 6 [.leaf 1, .leaf 2], .leaf 0])
    (by decide +kernel) rfl (P₁ := [(1 / 3, [(6, 1)])]) (P₂ := [(1 / 3, [(6, 1)])])
    (P₃ := [(1, []), (-2 / 3, [(6, 1)])]) (by decide +kernel)]
  have h : decC 3 6 = {1, 2} := by decide +kernel
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h]
  push_cast
  split_ifs <;> ring

/-- The rooted gene tree distribution of the unresolved species tree `(a,b,c)`. -/
theorem rootedDist_three_star (σ : SpeciesTree (Fin 3)) (hσ : σ.clusters = hierarchyOf ∅)
    (G : Finset (Finset (Fin 3))) :
    σ.rootedDist id G =
      if G = rootedTree3 {0, 1} then 1 / 3 else if G = rootedTree3 {0, 2} then 1 / 3
      else if G = rootedTree3 {1, 2} then 1 / 3 else 0 := by
  rw [rootedDist_eq_triples σ hσ (.node 7 [.leaf 0, .leaf 1, .leaf 2])
    (by decide +kernel) rfl (P₁ := [(1 / 3, [])]) (P₂ := [(1 / 3, [])])
    (P₃ := [(1 / 3, [])]) (by decide +kernel)]
  simp only [evalPoly_cons, evalPoly_nil, monoVal_nil]
  push_cast
  split_ifs <;> ring

/-- The binary hierarchies on `Fin 3`: a binary species tree on three taxa has exactly one
cluster with two taxa. -/
theorem clusters_eq_of_isBinary_three (σ : SpeciesTree (Fin 3)) (hσ : σ.IsBinary) :
    σ.clusters = hierarchyOf {{0, 1}} ∨ σ.clusters = hierarchyOf {{0, 2}} ∨
      σ.clusters = hierarchyOf {{1, 2}} := by
  obtain ⟨B, hB, C, hC, hBC, hU⟩ := hσ univ σ.univ_mem (by decide +kernel)
  have key₁ : ∀ B C : Finset (Fin 3), B.Nonempty → C.Nonempty → Disjoint B C → B ∪ C = univ →
      #B = 2 ∨ #C = 2 := by decide +kernel
  obtain ⟨D, hD, hD2⟩ : ∃ D ∈ σ.clusters, #D = 2 := by
    rcases key₁ B C (σ.nonempty_of_mem B hB) (σ.nonempty_of_mem C hC) hBC hU with h | h
    exacts [⟨B, hB, h⟩, ⟨C, hC, h⟩]
  have key₂ : ∀ D A : Finset (Fin 3), #D = 2 → A.Nonempty → (A ⊆ D ∨ D ⊆ A ∨ Disjoint A D) →
      A ∈ hierarchyOf {D} := by decide +kernel
  have hH : σ.clusters = hierarchyOf {D} := by
    ext A
    constructor
    · intro hA
      exact key₂ D A hD2 (σ.nonempty_of_mem A hA) (σ.laminar A hA D hD)
    · intro hA
      simp only [hierarchyOf, mem_insert, mem_union, mem_singleton, mem_image, mem_univ,
        true_and] at hA
      rcases hA with rfl | rfl | ⟨x, rfl⟩
      · exact σ.univ_mem
      · exact hD
      · exact σ.singleton_mem x
  have key₃ : ∀ D : Finset (Fin 3), #D = 2 → D = {0, 1} ∨ D = {0, 2} ∨ D = {1, 2} := by
    decide +kernel
  rcases key₃ D hD2 with rfl | rfl | rfl
  exacts [Or.inl hH, Or.inr (Or.inl hH), Or.inr (Or.inr hH)]

end ADR11.Computation
