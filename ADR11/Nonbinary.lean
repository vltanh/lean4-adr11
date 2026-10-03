module

public import ADR11.MSC.Contract
public import ADR11.Introduction
public import ADR11.FourTaxa

/-!
# Section 5: nonbinary species trees

The paper obtains the probabilities of binary gene trees under a nonbinary species tree as the
limits of the formulas for binary species trees, as one or more branch lengths go to `0`
(l.697–699).

* `section5_limit`: the distributions of a nonbinary species tree are limits of those of a binary
  resolution as the added branch lengths tend to `0`. Hence (`lim_rootedDist_eq`,
  `lim_unrootedDist_eq`) a formula for the gene tree probabilities of the binary resolution,
  continuous in the added lengths, gives those of the nonbinary tree with the added lengths set
  to `0`.
* `section5_threeTaxa`: for the unresolved 3-taxon species tree the three rooted gene trees are
  equiprobable: letting `t → 0` in equation (1) for `((a,b):t,c)` gives `1/3` each
  (`lim_threeTaxa_unresolved`). For a resolved one exactly one has probability greater than `1/3`
  (equation (1)).
* `section5_triples`, `section5_proposition1`, `section5_corollary2` are in
  `ADR11.Nonbinary.Triples`.
* `section5_fourTaxa`: `(a,b,c,d)` and `((a,b,c):y,d)` give the same unrooted distribution, and so
  do `(((a,b):x,c):y,d)` and `((a,b):x,c,d)`, with `ℙ(T_{AB|CD}) = 1 - (2/3) e^{-x}`. The three
  nonbinary trees are limits of the caterpillar `(((a,b):x,c):y,d)` of Section 4.1, as `y → 0`,
  `x → 0`, or both (`lim_fourTaxa_quartets`).
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Limits of the formulas for binary species trees -/

/-- Section 5: the gene tree probabilities of a nonbinary species tree are the limits of those of a
binary resolution `H` of it as the lengths of the added edges tend to `0`. -/
theorem section5_limit (σ : SpeciesTree X) {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hsub : σ.clusters ⊆ H) (T : Finset (Finset X)) :
    Filter.Tendsto
      (fun ε : ℝ => unrootedDistOf H (fun A => if A ∈ σ.clusters then σ.length A else ε) id T)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (σ.unrootedDist id T)) :=
  -- the distribution is continuous in `ε`, and at `ε = 0` the added edges contract
  (σ.tendsto_unrootedDistOf hH hsub id T).mono_left nhdsWithin_le_nhds

/-- For `ε > 0`, the species tree with the clusters of a hierarchy `H`, the lengths of `σ` on the
clusters of `σ` and the length `ε` on the other clusters. -/
theorem lim_exists_resolution (σ : SpeciesTree X) {H : Finset (Finset X)} (hH : IsHierarchy H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : SpeciesTree X, τ.clusters = H ∧
      τ.length = fun A => if A ∈ σ.clusters then σ.length A else ε :=
  ⟨{ clusters := H
     univ_mem := hH.1
     singleton_mem := hH.2.1
     nonempty_of_mem := hH.2.2.1
     laminar := hH.2.2.2
     length := fun A => if A ∈ σ.clusters then σ.length A else ε
     length_pos := fun A _ hA => by
       split_ifs with h
       exacts [σ.length_pos A h hA, hε] }, rfl, rfl⟩

/-- The lengths of `σ` on its edges and `ε` on the added edges depend continuously on `ε`. -/
theorem lim_continuous_length (σ : SpeciesTree X) (A : Finset X) :
    Continuous fun ε : ℝ => if A ∈ σ.clusters then σ.length A else ε :=
  continuous_if_const _ (fun _ => continuous_const) fun _ => continuous_id

/-- **The formulas for a binary resolution, with the added lengths set to `0`**, for rooted gene
trees. Let `H` refine the hierarchy of `σ` (for example a binary resolution of `σ`). If every
species tree with the clusters `H` gives the rooted gene tree `G` the probability `φ` of its
lengths, and `φ` is continuous at `ε = 0` along the lengths of `σ` with `ε` on the added edges,
then `σ` gives `G` the probability `φ` with the lengths of `σ` and `0` on the added edges: the
probability under `σ` is the limit as `ε → 0` (`lim_tendsto_rootedDist`), and the limit of the
formula is its value at `ε = 0`. -/
theorem lim_rootedDist_eq (σ : SpeciesTree X) {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hsub : σ.clusters ⊆ H) (G : Finset (Finset X)) (φ : (Finset X → ℝ) → ℝ)
    (hφ : ∀ τ : SpeciesTree X, τ.clusters = H → τ.rootedDist id G = φ τ.length)
    (hcont : ContinuousAt (fun ε : ℝ => φ fun A => if A ∈ σ.clusters then σ.length A else ε) 0) :
    σ.rootedDist id G = φ fun A => if A ∈ σ.clusters then σ.length A else 0 := by
  refine tendsto_nhds_unique_of_eventuallyEq
    ((lim_tendsto_rootedDist σ hH hsub id G).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  -- for `ε > 0` the formula applies to the species tree with the length `ε` on the added edges
  obtain ⟨τ, hτ, hlen⟩ := lim_exists_resolution σ hH hε
  dsimp only
  rw [← hlen, ← hφ τ hτ, ← hτ]
  rfl

/-- **The formulas for a binary resolution, with the added lengths set to `0`**, for unrooted gene
trees: as `lim_rootedDist_eq`, with `section5_limit`. -/
theorem lim_unrootedDist_eq (σ : SpeciesTree X) {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hsub : σ.clusters ⊆ H) (T : Finset (Finset X)) (φ : (Finset X → ℝ) → ℝ)
    (hφ : ∀ τ : SpeciesTree X, τ.clusters = H → τ.unrootedDist id T = φ τ.length)
    (hcont : ContinuousAt (fun ε : ℝ => φ fun A => if A ∈ σ.clusters then σ.length A else ε) 0) :
    σ.unrootedDist id T = φ fun A => if A ∈ σ.clusters then σ.length A else 0 := by
  refine tendsto_nhds_unique_of_eventuallyEq (section5_limit σ hH hsub T)
    (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  -- for `ε > 0` the formula applies to the species tree with the length `ε` on the added edges
  obtain ⟨τ, hτ, hlen⟩ := lim_exists_resolution σ hH hε
  dsimp only
  rw [← hlen, ← hφ τ hτ, ← hτ]
  rfl

/-! ### Three taxa -/

/-- **Three taxa, unresolved** (l.701–702). For the 3-taxon species tree `((a,b):t,c)`, letting
`t → 0`, the rooted gene tree probabilities of equation (1), `1 - (2/3) e^{-t}`, `(1/3) e^{-t}`,
`(1/3) e^{-t}`, are each `1/3` in the limit; so the unresolved tree `(a,b,c)` gives probability
`1/3` to each rooted gene tree. -/
theorem lim_threeTaxa_unresolved (σ : SpeciesTree (Fin 3)) (hσ : σ.clusters = hierarchyOf ∅) :
    σ.rootedDist id (rootedTree3 {0, 1}) = 1 / 3 ∧ σ.rootedDist id (rootedTree3 {0, 2}) = 1 / 3 ∧
      σ.rootedDist id (rootedTree3 {1, 2}) = 1 / 3 := by
  -- `((a,b):t,c)` is a binary resolution of `(a,b,c)`, with the added edge above `{a, b}`
  have hH : IsHierarchy clusters3 := ⟨by decide, by decide, by decide, by decide⟩
  have hsub : σ.clusters ⊆ clusters3 := by rw [hσ]; decide
  have h01 : ({0, 1} : Finset (Fin 3)) ∉ σ.clusters := by rw [hσ]; decide
  -- `e^{-t}` is continuous in `t`, and `1` at `t = 0`
  have hc : Continuous fun ε : ℝ =>
      exp (-if ({0, 1} : Finset (Fin 3)) ∈ σ.clusters then σ.length {0, 1} else ε) :=
    (lim_continuous_length σ {0, 1}).neg.rexp
  have h0 : exp (-if ({0, 1} : Finset (Fin 3)) ∈ σ.clusters then σ.length {0, 1} else 0) = 1 := by
    rw [ite_eq_right h01, neg_zero, exp_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [lim_rootedDist_eq σ hH hsub _ (fun ℓ => 1 - 2 / 3 * exp (-ℓ {0, 1}))
      (fun τ hτ => (equation1 τ hτ).1)
      (continuous_const.sub (continuous_const.mul hc)).continuousAt]
    dsimp only
    rw [h0]
    norm_num
  · rw [lim_rootedDist_eq σ hH hsub _ (fun ℓ => 1 / 3 * exp (-ℓ {0, 1}))
      (fun τ hτ => (equation1 τ hτ).2.1) (continuous_const.mul hc).continuousAt]
    dsimp only
    rw [h0, mul_one]
  · rw [lim_rootedDist_eq σ hH hsub _ (fun ℓ => 1 / 3 * exp (-ℓ {0, 1}))
      (fun τ hτ => (equation1 τ hτ).2.2.1) (continuous_const.mul hc).continuousAt]
    dsimp only
    rw [h0, mul_one]

/-- Section 5, three taxa: for the unresolved species tree `(a,b,c)` the three rooted gene trees
have probability `1/3`; for the resolved species tree `((a,b):t,c)` exactly one rooted gene tree
has probability greater than `1/3`.

The unresolved tree is the limit `t → 0` of `((a,b):t,c)` (`lim_threeTaxa_unresolved`); the
resolved tree is equation (1). -/
theorem section5_threeTaxa (σ σ' : SpeciesTree (Fin 3)) (hσ : σ.clusters = hierarchyOf ∅)
    (hσ' : σ'.clusters = clusters3) :
    (σ.rootedDist id (rootedTree3 {0, 1}) = 1 / 3 ∧ σ.rootedDist id (rootedTree3 {0, 2}) = 1 / 3 ∧
        σ.rootedDist id (rootedTree3 {1, 2}) = 1 / 3) ∧
      (1 / 3 < σ'.rootedDist id (rootedTree3 {0, 1}) ∧
        σ'.rootedDist id (rootedTree3 {0, 2}) < 1 / 3 ∧
        σ'.rootedDist id (rootedTree3 {1, 2}) < 1 / 3) := by
  refine ⟨lim_threeTaxa_unresolved σ hσ, ?_⟩
  obtain ⟨e₁, e₂, e₃, -, -⟩ := equation1 σ' hσ'
  have hX : exp (-σ'.length {0, 1}) < 1 := by
    rw [Real.exp_lt_one_iff, neg_lt_zero]
    exact σ'.length_pos {0, 1} (by rw [hσ']; decide) (by decide)
  rw [e₁, e₂, e₃]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-! ### Four taxa -/

/-- **Four taxa as limits of the caterpillar** (l.709–711). The species trees `((a,b):x,c,d)`,
`((a,b,c):y,d)` and `(a,b,c,d)` are the limits of the caterpillar `(((a,b):x,c):y,d)` as `y → 0`,
`x → 0`, or both. So their quartet probabilities are those of Section 4.1 for the caterpillar,
`1 - (2/3) e^{-x}`, `(1/3) e^{-x}`, `(1/3) e^{-x}`, which do not depend on `y`, with `x = 0` when
the edge above `{a, b}` is contracted. -/
theorem lim_fourTaxa_quartets (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters ⊆ caterpillar4) :
    σ.unrootedDist id (treeOfClusters {{0, 1}}) =
        1 - 2 / 3 * exp (-if ({0, 1} : Finset (Fin 4)) ∈ σ.clusters then σ.length {0, 1} else 0) ∧
      σ.unrootedDist id (treeOfClusters {{0, 2}}) =
        1 / 3 * exp (-if ({0, 1} : Finset (Fin 4)) ∈ σ.clusters then σ.length {0, 1} else 0) ∧
      σ.unrootedDist id (treeOfClusters {{0, 3}}) =
        1 / 3 * exp (-if ({0, 1} : Finset (Fin 4)) ∈ σ.clusters then σ.length {0, 1} else 0) := by
  have hH : IsHierarchy caterpillar4 := ⟨by decide, by decide, by decide, by decide⟩
  -- `e^{-x}` is continuous in the length `x`
  have hc : Continuous fun ε : ℝ =>
      exp (-if ({0, 1} : Finset (Fin 4)) ∈ σ.clusters then σ.length {0, 1} else ε) :=
    (lim_continuous_length σ {0, 1}).neg.rexp
  exact ⟨lim_unrootedDist_eq σ hH hσ _ (fun ℓ => 1 - 2 / 3 * exp (-ℓ {0, 1}))
      (fun τ hτ => (fourTaxa_caterpillar τ hτ).1)
      (continuous_const.sub (continuous_const.mul hc)).continuousAt,
    lim_unrootedDist_eq σ hH hσ _ (fun ℓ => 1 / 3 * exp (-ℓ {0, 1}))
      (fun τ hτ => (fourTaxa_caterpillar τ hτ).2.1) (continuous_const.mul hc).continuousAt,
    lim_unrootedDist_eq σ hH hσ _ (fun ℓ => 1 / 3 * exp (-ℓ {0, 1}))
      (fun τ hτ => (fourTaxa_caterpillar τ hτ).2.2) (continuous_const.mul hc).continuousAt⟩

/-- Only the binary gene trees have positive probability (l.699–700): when the three binary unrooted
gene trees on four taxa have total probability `1`, every other gene tree has probability `0`, as
the probabilities are nonnegative and sum to `1`. -/
private theorem lim_four_eq_zero (σ : SpeciesTree (Fin 4))
    (h : σ.unrootedDist id (treeOfClusters {{0, 1}}) +
      σ.unrootedDist id (treeOfClusters {{0, 2}}) +
      σ.unrootedDist id (treeOfClusters {{0, 3}}) = 1) {U : Finset (Finset (Fin 4))}
    (h₁ : U ≠ treeOfClusters {{0, 1}}) (h₂ : U ≠ treeOfClusters {{0, 2}})
    (h₃ : U ≠ treeOfClusters {{0, 3}}) : σ.unrootedDist id U = 0 := by
  have hnn : ∀ T, 0 ≤ σ.unrootedDist id T := fun T =>
    unrootedDistOf_nonneg σ.isHierarchy (fun A hA hAu => (σ.length_pos A hA hAu).le) id T
  have hsum : ∑ T, σ.unrootedDist id T = 1 := unrootedDistOf_sum σ.isHierarchy σ.length id
  have q₁₂ : (treeOfClusters {{0, 1}} : Finset (Finset (Fin 4))) ≠ treeOfClusters {{0, 2}} := by
    decide
  have q₁₃ : (treeOfClusters {{0, 1}} : Finset (Finset (Fin 4))) ≠ treeOfClusters {{0, 3}} := by
    decide
  have q₂₃ : (treeOfClusters {{0, 2}} : Finset (Finset (Fin 4))) ≠ treeOfClusters {{0, 3}} := by
    decide
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ ({U, treeOfClusters {{0, 1}},
      treeOfClusters {{0, 2}}, treeOfClusters {{0, 3}}} : Finset (Finset (Finset (Fin 4)))))
    fun T _ _ => hnn T
  rw [hsum, sum_insert (by simp only [mem_insert, mem_singleton, not_or]; exact ⟨h₁, h₂, h₃⟩),
    sum_insert (by simp only [mem_insert, mem_singleton, not_or]; exact ⟨q₁₂, q₁₃⟩),
    sum_insert (by simp only [mem_singleton]; exact q₂₃), sum_singleton] at hle
  linarith [hnn U]

/-- Section 5, four taxa: `(a,b,c,d)` and `((a,b,c):y,d)` give the same unrooted gene tree
distribution, and so do `(((a,b):x,c):y,d)` and `((a,b):x,c,d)` (with the same `x`), with
`ℙ(T_{AB|CD}) = 1 - (2/3) e^{-x}`.

The nonbinary trees are limits of the caterpillar `(((a,b):x,c):y,d)` (`lim_fourTaxa_quartets`):
`(a,b,c,d)` and `((a,b,c):y,d)` give each binary unrooted gene tree probability `1/3`, and
`((a,b):x,c,d)` gives the probabilities of the caterpillar. The three binary gene trees have total
probability `1`, so the other gene trees have probability `0`. -/
theorem section5_fourTaxa (σ₁ σ₂ σ₃ σ₄ : SpeciesTree (Fin 4))
    (h₁ : σ₁.clusters = hierarchyOf ∅) (h₂ : σ₂.clusters = hierarchyOf {{0, 1, 2}})
    (h₃ : σ₃.clusters = caterpillar4) (h₄ : σ₄.clusters = hierarchyOf {{0, 1}})
    (hx : σ₄.length {0, 1} = σ₃.length {0, 1}) :
    σ₁.unrootedDist id = σ₂.unrootedDist id ∧ σ₃.unrootedDist id = σ₄.unrootedDist id ∧
      σ₄.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * exp (-σ₄.length {0, 1}) := by
  -- `(a,b,c,d)` and `((a,b,c):y,d)`: the limits `x → 0` (and `y → 0`), with probabilities `1/3`
  have n₁ : ({0, 1} : Finset (Fin 4)) ∉ σ₁.clusters := by rw [h₁]; decide
  have n₂ : ({0, 1} : Finset (Fin 4)) ∉ σ₂.clusters := by rw [h₂]; decide
  obtain ⟨a₁, b₁, c₁⟩ := lim_fourTaxa_quartets σ₁ (by rw [h₁]; decide)
  obtain ⟨a₂, b₂, c₂⟩ := lim_fourTaxa_quartets σ₂ (by rw [h₂]; decide)
  simp only [n₁, n₂, ↓reduceIte, neg_zero, exp_zero] at a₁ b₁ c₁ a₂ b₂ c₂
  -- `((a,b):x,c,d)`: the limit `y → 0`, with the probabilities of the caterpillar
  have m₄ : ({0, 1} : Finset (Fin 4)) ∈ σ₄.clusters := by rw [h₄]; decide
  obtain ⟨a₄, b₄, c₄⟩ := lim_fourTaxa_quartets σ₄ (by rw [h₄]; decide)
  simp only [m₄, ↓reduceIte] at a₄ b₄ c₄
  obtain ⟨a₃, b₃, c₃⟩ := fourTaxa_caterpillar σ₃ h₃
  refine ⟨funext fun U => ?_, funext fun U => ?_, a₄⟩
  · by_cases e₁ : U = treeOfClusters {{0, 1}}
    · rw [e₁, a₁, a₂]
    by_cases e₂ : U = treeOfClusters {{0, 2}}
    · rw [e₂, b₁, b₂]
    by_cases e₃ : U = treeOfClusters {{0, 3}}
    · rw [e₃, c₁, c₂]
    rw [lim_four_eq_zero σ₁ (by rw [a₁, b₁, c₁]; norm_num) e₁ e₂ e₃,
      lim_four_eq_zero σ₂ (by rw [a₂, b₂, c₂]; norm_num) e₁ e₂ e₃]
  · by_cases e₁ : U = treeOfClusters {{0, 1}}
    · rw [e₁, a₃, a₄, hx]
    by_cases e₂ : U = treeOfClusters {{0, 2}}
    · rw [e₂, b₃, b₄, hx]
    by_cases e₃ : U = treeOfClusters {{0, 3}}
    · rw [e₃, c₃, c₄, hx]
    rw [lim_four_eq_zero σ₃ (by rw [a₃, b₃, c₃]; ring) e₁ e₂ e₃,
      lim_four_eq_zero σ₄ (by rw [a₄, b₄, c₄]; ring) e₁ e₂ e₃]

end ADR11
