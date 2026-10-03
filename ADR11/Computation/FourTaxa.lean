module

public import ADR11.Computation.Toolkit

/-!
# Unrooted gene tree distributions of 4-taxon species trees

With one lineage per taxon on `Fin 4`, the unrooted gene trees are the three quartets
`treeOfClusters {{0, 1}}` (`T_{AB|CD}`), `treeOfClusters {{0, 2}}` (`T_{AC|BD}`) and
`treeOfClusters {{0, 3}}` (`T_{AD|BC}`); every other `T` has probability `0`. This file gives the
complete unrooted gene tree distribution, as a function of `T`, of the species trees on `Fin 4`
used in the paper:

* `unrootedDist_bal4`: the balanced tree `((a,b):x,(c,d):y)` (`balanced4`);
* `unrootedDist_cat4_0123`, `_0132`, `_2301`, `_2310`: the caterpillars `(((a,b):x,c):y,d)`
  (`caterpillar4`), `(((a,b):x,d):y,c)`, `(((c,d):x,a):y,b)`, `(((c,d):x,b):y,a)`;
* `unrootedDist_star4`: the unresolved tree `(a,b,c,d)` (`hierarchyOf ∅`);
* `unrootedDist_cherry4`: `((a,b):x,c,d)` (`hierarchyOf {{0, 1}}`);
* `unrootedDist_triple4`: `((a,b,c):y,d)` (`hierarchyOf {{0, 1, 2}}`).

`unrootedDist_eq_quartets` is the general statement behind them: run the engine on a tree shape
and read the three quartet probabilities.
-/

@[expose] public section

namespace ADR11.Computation

open Finset Real

/-- The codes of the unrooted quartet tree with the split `A | Aᶜ`, where `0 ∈ A` and `a` is the
code of `A`. -/
def quartetCode (a : ℕ) : List ℕ := unrootL 4 [1, 2, 4, 8, a, 15]

theorem decF_quartetCode_3 : decF 4 (quartetCode 3) = treeOfClusters {{0, 1}} := by
  decide +kernel

theorem decF_quartetCode_5 : decF 4 (quartetCode 5) = treeOfClusters {{0, 2}} := by
  decide +kernel

theorem decF_quartetCode_9 : decF 4 (quartetCode 9) = treeOfClusters {{0, 3}} := by
  decide +kernel

theorem quartet_ne_01_02 :
    (treeOfClusters {{0, 1}} : Finset (Finset (Fin 4))) ≠ treeOfClusters {{0, 2}} := by
  decide +kernel

theorem quartet_ne_01_03 :
    (treeOfClusters {{0, 1}} : Finset (Finset (Fin 4))) ≠ treeOfClusters {{0, 3}} := by
  decide +kernel

theorem quartet_ne_02_03 :
    (treeOfClusters {{0, 2}} : Finset (Finset (Fin 4))) ≠ treeOfClusters {{0, 3}} := by
  decide +kernel

/-- An unrooted gene tree distribution on `Fin 4` computed by the engine, as a function of the
gene tree. -/
theorem unrootedDist_eq_quartets (σ : SpeciesTree (Fin 4)) {H : Finset (Finset (Fin 4))}
    (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB 4 H = true) (htop : T.code = 15)
    {P₁ P₂ P₃ : List (ℚ × List (ℕ × ℕ))}
    (hc : certAllB 4 (T.unrootedL 4 4 id)
      [(quartetCode 3, P₁), (quartetCode 5, P₂), (quartetCode 9, P₃)] = true)
    (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then evalPoly σ.length P₁
      else if U = treeOfClusters {{0, 2}} then evalPoly σ.length P₂
      else if U = treeOfClusters {{0, 3}} then evalPoly σ.length P₃ else 0 :=
  unrootedDist_eq_ite₃ σ hσ T hwf htop hc decF_quartetCode_3 decF_quartetCode_5
    decF_quartetCode_9 quartet_ne_01_02 quartet_ne_01_03 quartet_ne_02_03 U

/-- The balanced species tree `((a,b):x,(c,d):y)`. -/
theorem unrootedDist_bal4 (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters = balanced4)
    (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then
        1 - 2 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3}))
      else if U = treeOfClusters {{0, 2}} then
        1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3}))
      else if U = treeOfClusters {{0, 3}} then
        1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3}))
      else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.node 3 [.leaf 0, .leaf 1], .node 12 [.leaf 2, .leaf 3]])
    (by decide +kernel) rfl (P₁ := [(1, []), (-2 / 3, [(3, 1), (12, 1)])])
    (P₂ := [(1 / 3, [(3, 1), (12, 1)])]) (P₃ := [(1 / 3, [(3, 1), (12, 1)])]) (by decide +kernel)]
  have h3 : decC 4 3 = {0, 1} := by decide +kernel
  have h12 : decC 4 12 = {2, 3} := by decide +kernel
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h3, h12, neg_add,
    Real.exp_add]
  push_cast
  split_ifs <;> ring

/-- The caterpillar species tree `(((a,b):x,c):y,d)`. -/
theorem unrootedDist_cat4_0123 (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters = caterpillar4)
    (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then 1 - 2 / 3 * exp (-σ.length {0, 1})
      else if U = treeOfClusters {{0, 2}} then 1 / 3 * exp (-σ.length {0, 1})
      else if U = treeOfClusters {{0, 3}} then 1 / 3 * exp (-σ.length {0, 1})
      else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.node 7 [.node 3 [.leaf 0, .leaf 1], .leaf 2], .leaf 3])
    (by decide +kernel) rfl (P₁ := [(1, []), (-2 / 3, [(3, 1)])]) (P₂ := [(1 / 3, [(3, 1)])])
    (P₃ := [(1 / 3, [(3, 1)])]) (by decide +kernel)]
  have h3 : decC 4 3 = {0, 1} := by decide +kernel
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h3]
  push_cast
  split_ifs <;> ring

/-- The caterpillar species tree `(((a,b):x,d):y,c)`. -/
theorem unrootedDist_cat4_0132 (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = hierarchyOf {{0, 1}, {0, 1, 3}}) (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then 1 - 2 / 3 * exp (-σ.length {0, 1})
      else if U = treeOfClusters {{0, 2}} then 1 / 3 * exp (-σ.length {0, 1})
      else if U = treeOfClusters {{0, 3}} then 1 / 3 * exp (-σ.length {0, 1})
      else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.node 11 [.node 3 [.leaf 0, .leaf 1], .leaf 3], .leaf 2])
    (by decide +kernel) rfl (P₁ := [(1, []), (-2 / 3, [(3, 1)])]) (P₂ := [(1 / 3, [(3, 1)])])
    (P₃ := [(1 / 3, [(3, 1)])]) (by decide +kernel)]
  have h3 : decC 4 3 = {0, 1} := by decide +kernel
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h3]
  push_cast
  split_ifs <;> ring

/-- The caterpillar species tree `(((c,d):x,a):y,b)`. -/
theorem unrootedDist_cat4_2301 (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = hierarchyOf {{2, 3}, {0, 2, 3}}) (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then 1 - 2 / 3 * exp (-σ.length {2, 3})
      else if U = treeOfClusters {{0, 2}} then 1 / 3 * exp (-σ.length {2, 3})
      else if U = treeOfClusters {{0, 3}} then 1 / 3 * exp (-σ.length {2, 3})
      else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.node 13 [.node 12 [.leaf 2, .leaf 3], .leaf 0], .leaf 1])
    (by decide +kernel) rfl (P₁ := [(1, []), (-2 / 3, [(12, 1)])]) (P₂ := [(1 / 3, [(12, 1)])])
    (P₃ := [(1 / 3, [(12, 1)])]) (by decide +kernel)]
  have h12 : decC 4 12 = {2, 3} := by decide +kernel
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h12]
  push_cast
  split_ifs <;> ring

/-- The caterpillar species tree `(((c,d):x,b):y,a)`. -/
theorem unrootedDist_cat4_2310 (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = hierarchyOf {{2, 3}, {1, 2, 3}}) (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then 1 - 2 / 3 * exp (-σ.length {2, 3})
      else if U = treeOfClusters {{0, 2}} then 1 / 3 * exp (-σ.length {2, 3})
      else if U = treeOfClusters {{0, 3}} then 1 / 3 * exp (-σ.length {2, 3})
      else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.node 14 [.node 12 [.leaf 2, .leaf 3], .leaf 1], .leaf 0])
    (by decide +kernel) rfl (P₁ := [(1, []), (-2 / 3, [(12, 1)])]) (P₂ := [(1 / 3, [(12, 1)])])
    (P₃ := [(1 / 3, [(12, 1)])]) (by decide +kernel)]
  have h12 : decC 4 12 = {2, 3} := by decide +kernel
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h12]
  push_cast
  split_ifs <;> ring

/-- The unresolved species tree `(a,b,c,d)`. -/
theorem unrootedDist_star4 (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters = hierarchyOf ∅)
    (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then 1 / 3 else if U = treeOfClusters {{0, 2}} then 1 / 3
      else if U = treeOfClusters {{0, 3}} then 1 / 3 else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.leaf 0, .leaf 1, .leaf 2, .leaf 3])
    (by decide +kernel) rfl (P₁ := [(1 / 3, [])]) (P₂ := [(1 / 3, [])]) (P₃ := [(1 / 3, [])])
    (by decide +kernel)]
  simp only [evalPoly_cons, evalPoly_nil, monoVal_nil]
  push_cast
  split_ifs <;> ring

/-- The species tree `((a,b):x,c,d)`. -/
theorem unrootedDist_cherry4 (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters = hierarchyOf {{0, 1}})
    (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then 1 - 2 / 3 * exp (-σ.length {0, 1})
      else if U = treeOfClusters {{0, 2}} then 1 / 3 * exp (-σ.length {0, 1})
      else if U = treeOfClusters {{0, 3}} then 1 / 3 * exp (-σ.length {0, 1})
      else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.node 3 [.leaf 0, .leaf 1], .leaf 2, .leaf 3])
    (by decide +kernel) rfl (P₁ := [(1, []), (-2 / 3, [(3, 1)])]) (P₂ := [(1 / 3, [(3, 1)])])
    (P₃ := [(1 / 3, [(3, 1)])]) (by decide +kernel)]
  have h3 : decC 4 3 = {0, 1} := by decide +kernel
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h3]
  push_cast
  split_ifs <;> ring

/-- The species tree `((a,b,c):y,d)`: all three quartets are equiprobable. -/
theorem unrootedDist_triple4 (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters = hierarchyOf {{0, 1, 2}})
    (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then 1 / 3 else if U = treeOfClusters {{0, 2}} then 1 / 3
      else if U = treeOfClusters {{0, 3}} then 1 / 3 else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.node 7 [.leaf 0, .leaf 1, .leaf 2], .leaf 3])
    (by decide +kernel) rfl (P₁ := [(1 / 3, [])]) (P₂ := [(1 / 3, [])]) (P₃ := [(1 / 3, [])])
    (by decide +kernel)]
  simp only [evalPoly_cons, evalPoly_nil, monoVal_nil]
  push_cast
  split_ifs <;> ring

/-! ### Arbitrary labellings

For distinct `a b c d : Fin 4`, the complete unrooted gene tree distributions of the caterpillar
`(((a,b):x,c):y,d)`, the balanced tree `((a,b):x,(c,d):y)`, `((a,b):x,c,d)` and `((a,b,c):y,d)`,
in terms of the quartets `treeOfClusters {{a, b}}`, `treeOfClusters {{a, c}}`,
`treeOfClusters {{a, d}}`. Each is proved for all labellings at once by a kernel computation. -/

/-- The code of the cluster `{a, b}`. -/
def pairCode (a b : Fin 4) : ℕ := 2 ^ (a : ℕ) + 2 ^ (b : ℕ)

/-- The codes of the quartet `treeOfClusters {{a, b}}`. -/
def qCode (a b : Fin 4) : List ℕ := unrootL 4 [1, 2, 4, 8, pairCode a b, 15]

theorem decF_qCode : ∀ a b : Fin 4, a ≠ b → decF 4 (qCode a b) = treeOfClusters {{a, b}} := by
  decide +kernel

theorem decC_pairCode : ∀ a b : Fin 4, a ≠ b → decC 4 (pairCode a b) = {a, b} := by
  decide +kernel

theorem quartets_ne : ∀ a b c d : Fin 4, [a, b, c, d].Nodup →
    (treeOfClusters {{a, b}} : Finset (Finset (Fin 4))) ≠ treeOfClusters {{a, c}} ∧
      (treeOfClusters {{a, b}} : Finset (Finset (Fin 4))) ≠ treeOfClusters {{a, d}} ∧
      (treeOfClusters {{a, c}} : Finset (Finset (Fin 4))) ≠ treeOfClusters {{a, d}} := by
  decide +kernel

theorem ne_of_nodup₄ {a b c d : Fin 4} (h : [a, b, c, d].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h
  exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1.1, h.2.1.2, h.2.2⟩

/-- The tree shape of the caterpillar `(((a,b),c),d)`. -/
def cat4Shape (a b c d : Fin 4) : PTree :=
  .node 15 [.node (pairCode a b + 2 ^ (c : ℕ)) [.node (pairCode a b) [.leaf a, .leaf b], .leaf c],
    .leaf d]

/-- The tree shape of the balanced tree `((a,b),(c,d))`. -/
def bal4Shape (a b c d : Fin 4) : PTree :=
  .node 15 [.node (pairCode a b) [.leaf a, .leaf b], .node (pairCode c d) [.leaf c, .leaf d]]

/-- The tree shape of `((a,b),c,d)`. -/
def cherry4Shape (a b c d : Fin 4) : PTree :=
  .node 15 [.node (pairCode a b) [.leaf a, .leaf b], .leaf c, .leaf d]

/-- The tree shape of `((a,b,c),d)`. -/
def triple4Shape (a b c d : Fin 4) : PTree :=
  .node 15 [.node (pairCode a b + 2 ^ (c : ℕ)) [.leaf a, .leaf b, .leaf c], .leaf d]

theorem cat4Shape_wfB : ∀ a b c d : Fin 4, [a, b, c, d].Nodup →
    (cat4Shape a b c d).wfB 4 (hierarchyOf {{a, b}, {a, b, c}}) = true := by decide +kernel

theorem cat4_cert : ∀ a b c d : Fin 4, [a, b, c, d].Nodup →
    certAllB 4 ((cat4Shape a b c d).unrootedL 4 4 id)
      [(qCode a b, [(1, []), (-2/3, [(pairCode a b, 1)])]), (qCode a c, [(1/3, [(pairCode a b, 1)])]),
        (qCode a d, [(1/3, [(pairCode a b, 1)])])] = true := by decide +kernel

theorem bal4Shape_wfB : ∀ a b c d : Fin 4, [a, b, c, d].Nodup →
    (bal4Shape a b c d).wfB 4 (hierarchyOf {{a, b}, {c, d}}) = true := by decide +kernel

theorem bal4_cert : ∀ a b c d : Fin 4, [a, b, c, d].Nodup →
    certAllB 4 ((bal4Shape a b c d).unrootedL 4 4 id)
      [(qCode a b, [(1, []), (-2/3, [(pairCode a b, 1), (pairCode c d, 1)])]),
        (qCode a c, [(1/3, [(pairCode a b, 1), (pairCode c d, 1)])]),
        (qCode a d, [(1/3, [(pairCode a b, 1), (pairCode c d, 1)])])] = true := by decide +kernel

theorem cherry4Shape_wfB : ∀ a b c d : Fin 4, [a, b, c, d].Nodup →
    (cherry4Shape a b c d).wfB 4 (hierarchyOf {{a, b}}) = true := by decide +kernel

theorem cherry4_cert : ∀ a b c d : Fin 4, [a, b, c, d].Nodup →
    certAllB 4 ((cherry4Shape a b c d).unrootedL 4 4 id)
      [(qCode a b, [(1, []), (-2/3, [(pairCode a b, 1)])]), (qCode a c, [(1/3, [(pairCode a b, 1)])]),
        (qCode a d, [(1/3, [(pairCode a b, 1)])])] = true := by decide +kernel

theorem triple4Shape_wfB : ∀ a b c d : Fin 4, [a, b, c, d].Nodup →
    (triple4Shape a b c d).wfB 4 (hierarchyOf {{a, b, c}}) = true := by decide +kernel

theorem triple4_cert : ∀ a b c d : Fin 4, [a, b, c, d].Nodup →
    certAllB 4 ((triple4Shape a b c d).unrootedL 4 4 id)
      [(qCode a b, [(1/3, [])]), (qCode a c, [(1/3, [])]), (qCode a d, [(1/3, [])])] = true := by
  decide +kernel

/-- The caterpillar `(((a,b):x,c):y,d)`, for any distinct `a b c d`. -/
theorem unrootedDist_cat4 (a b c d : Fin 4) (h : [a, b, c, d].Nodup) (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = hierarchyOf {{a, b}, {a, b, c}}) (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{a, b}} then 1 - 2 / 3 * exp (-σ.length {a, b})
      else if U = treeOfClusters {{a, c}} then 1 / 3 * exp (-σ.length {a, b})
      else if U = treeOfClusters {{a, d}} then 1 / 3 * exp (-σ.length {a, b})
      else 0 := by
  obtain ⟨hab, hac, had, -, -, -⟩ := ne_of_nodup₄ h
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := quartets_ne a b c d h
  rw [unrootedDist_eq_ite₃ σ hσ (cat4Shape a b c d) (cat4Shape_wfB a b c d h) rfl
    (cat4_cert a b c d h) (decF_qCode a b hab) (decF_qCode a c hac) (decF_qCode a d had) h₁₂ h₁₃
    h₂₃ U]
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, decC_pairCode a b hab]
  push_cast
  split_ifs <;> ring

/-- The balanced tree `((a,b):x,(c,d):y)`, for any distinct `a b c d`. -/
theorem unrootedDist_bal4' (a b c d : Fin 4) (h : [a, b, c, d].Nodup) (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = hierarchyOf {{a, b}, {c, d}}) (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{a, b}} then 1 - 2 / 3 * exp (-(σ.length {a, b} + σ.length {c, d}))
      else if U = treeOfClusters {{a, c}} then 1 / 3 * exp (-(σ.length {a, b} + σ.length {c, d}))
      else if U = treeOfClusters {{a, d}} then 1 / 3 * exp (-(σ.length {a, b} + σ.length {c, d}))
      else 0 := by
  obtain ⟨hab, hac, had, -, -, hcd⟩ := ne_of_nodup₄ h
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := quartets_ne a b c d h
  rw [unrootedDist_eq_ite₃ σ hσ (bal4Shape a b c d) (bal4Shape_wfB a b c d h) rfl
    (bal4_cert a b c d h) (decF_qCode a b hab) (decF_qCode a c hac) (decF_qCode a d had) h₁₂ h₁₃
    h₂₃ U]
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, decC_pairCode a b hab,
    decC_pairCode c d hcd, neg_add, Real.exp_add]
  push_cast
  split_ifs <;> ring

/-- The species tree `((a,b):x,c,d)`, for any distinct `a b c d`. -/
theorem unrootedDist_cherry4' (a b c d : Fin 4) (h : [a, b, c, d].Nodup) (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = hierarchyOf {{a, b}}) (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{a, b}} then 1 - 2 / 3 * exp (-σ.length {a, b})
      else if U = treeOfClusters {{a, c}} then 1 / 3 * exp (-σ.length {a, b})
      else if U = treeOfClusters {{a, d}} then 1 / 3 * exp (-σ.length {a, b})
      else 0 := by
  obtain ⟨hab, hac, had, -, -, -⟩ := ne_of_nodup₄ h
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := quartets_ne a b c d h
  rw [unrootedDist_eq_ite₃ σ hσ (cherry4Shape a b c d) (cherry4Shape_wfB a b c d h) rfl
    (cherry4_cert a b c d h) (decF_qCode a b hab) (decF_qCode a c hac) (decF_qCode a d had) h₁₂
    h₁₃ h₂₃ U]
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, decC_pairCode a b hab]
  push_cast
  split_ifs <;> ring

/-- The species tree `((a,b,c):y,d)`, for any distinct `a b c d`: the three quartets are
equiprobable. -/
theorem unrootedDist_triple4' (a b c d : Fin 4) (h : [a, b, c, d].Nodup) (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = hierarchyOf {{a, b, c}}) (U : Finset (Finset (Fin 4))) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{a, b}} then 1 / 3 else if U = treeOfClusters {{a, c}} then 1 / 3
      else if U = treeOfClusters {{a, d}} then 1 / 3 else 0 := by
  obtain ⟨hab, hac, had, -, -, -⟩ := ne_of_nodup₄ h
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := quartets_ne a b c d h
  rw [unrootedDist_eq_ite₃ σ hσ (triple4Shape a b c d) (triple4Shape_wfB a b c d h) rfl
    (triple4_cert a b c d h) (decF_qCode a b hab) (decF_qCode a c hac) (decF_qCode a d had) h₁₂
    h₁₃ h₂₃ U]
  simp only [evalPoly_cons, evalPoly_nil, monoVal_nil]
  push_cast
  split_ifs <;> ring

end ADR11.Computation
