module

public import ADR11.Identifiability.Corollary6
public import ADR11.Identifiability.FiveTaxa.Binary
public import ADR11.Identifiability.FiveTaxa.Common

/-!
# Propositions 7 and 8: five taxa

* `proposition7`: for `|X| = 5`, `ℙ_{σ⁺}` determines the rooted topology `ψ⁺`.
* `proposition8`: for `|X| = 5`, `ℙ_{σ⁺}` determines `σ⁺`.
* `equation7`, `equation8`, `equation9`: the remaining branch length of the balanced, caterpillar
  and pseudocaterpillar trees (proof of Proposition 8), with arguments of the logarithms greater
  than `1`.

The proofs follow the paper. Proposition 7: by Corollary 6 the unrooted tree `ψ⁻` is known, and
the taxa are named so that its splits are `ab|cde` and `abc|de`; the sizes of the least probable
class and of the class of the second smallest probability give the unlabelled shape of `ψ⁺`
(inequalities (4)–(6)); a balanced tree is identified by whether `T₇` is in the least probable
class, a caterpillar by the taxa in cherries with `c` in the second class (its 2-clade) and the
sign of `ℙ(T₃) - ℙ(T₂)` (inequality (5)), and the pseudocaterpillar by the splits alone. The
classes of the seven rootings are computed in `ADR11.Identifiability.FiveTaxa.Binary`.
Proposition 8: `ψ⁺` is known by Proposition 7 and `λ⁻` by Corollary 6; after relabelling, `ψ⁺` is
one of the three representatives, every edge not at the root has the length of its split in `λ⁻`,
and the edges at the root are given by (7), (8) or (9).

* `p78_length_eq_of_not_root`, `p78_length_eq_of_sibling`: the lengths given by `λ⁻`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Proposition 7** (`prop:cases`). For `|X| = 5` the rooted species tree topology `ψ⁺` is determined by
`ℙ_{σ⁺}`. -/
theorem proposition7 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.clusters = σ'.clusters := by
  -- By Corollary 6, `σ` and `σ'` have the same unrooted topology `ψ⁻`. We name the taxa so that
  -- its splits are `ab|cde` and `abc|de`; `ψ⁺` is then one of the binary rootings of `U5 2`.
  have hψ : unroot σ.clusters = unroot σ'.clusters := (corollary6 σ σ' hσ hσ' h).1
  obtain ⟨e, he⟩ := exists_equiv_unroot_eq_U5_two_of_isBinary hX σ hσ
  have he' : unroot (σ'.relabel e.symm).clusters = U5 2 := by
    rw [SpeciesTree.relabel_clusters, unroot_relabelFamily, ← hψ, ← unroot_relabelFamily]
    exact he
  have hR := mem_binaryRootings5 _ ((σ.isBinary_relabel_iff e.symm).2 hσ) he
  have hR' := mem_binaryRootings5 _ ((σ'.isBinary_relabel_iff e.symm).2 hσ') he'
  have hd := (SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm).2 h
  refine relabelFamily_injective e.symm ?_
  change (σ.relabel e.symm).clusters = (σ'.relabel e.symm).clusters
  generalize σ.relabel e.symm = τ at hR hd ⊢
  generalize σ'.relabel e.symm = τ' at hR' hd ⊢
  -- The classes of gene trees are read off the distribution.
  have hL := cls_leastClass_congr hd
  have hS := cls_secondClass_congr hd
  -- The class sizes give the unlabelled shape of `ψ⁺`: by the inequalities (4)–(6), the least
  -- probable class has 8 elements for the pseudocaterpillar and 6 for the other shapes, and the
  -- class of the second smallest probability has 2 elements for the caterpillar and 4 for the
  -- balanced tree. So `σ` and `σ'` have the same shape (the six cases of different shapes are
  -- excluded by these sizes), and we consider the cases depending on that shape.
  rcases p78_shapes hR with hc | hb | hp <;> rcases p78_shapes hR' with hc' | hb' | hp'
  · -- Caterpillar: the 2-clade (`{a,b}` or `{d,e}`) is the set of taxa in cherries with `c` in
    -- the two trees of the second class; with 2-clade `{a,b}`, `ℙ(T₃) > ℙ(T₂)` for
    -- `((((a,b),c),d),e)` and `ℙ(T₂) > ℙ(T₃)` for `((((a,b),c),e),d)` (inequality (5)), and
    -- symmetrically for `{d,e}`.
    exact p78_caterpillar_eq hc hc' hS (cls_u_congr hd)
  · exact absurd (p78_card_caterpillar hc).2 (by rw [hS, (p78_card_balanced hb').2]; decide)
  · exact absurd (p78_card_caterpillar hc).1 (by rw [hL, p78_card_pseudocaterpillar hp']; decide)
  · exact absurd (p78_card_balanced hb).2 (by rw [hS, (p78_card_caterpillar hc').2]; decide)
  · -- Balanced: `ψ⁺ = (((a,b),c),(d,e))` or `((a,b),(c,(d,e)))`, and `T₇` lies in the least
    -- probable class for the first but not for the second.
    exact p78_balanced_eq hb hb' hL
  · exact absurd (p78_card_balanced hb).1 (by rw [hL, p78_card_pseudocaterpillar hp']; decide)
  · exact absurd (p78_card_pseudocaterpillar hp) (by rw [hL, (p78_card_caterpillar hc').1]; decide)
  · exact absurd (p78_card_pseudocaterpillar hp) (by rw [hL, (p78_card_balanced hb').1]; decide)
  · -- Pseudocaterpillar: the splits of `ψ⁻` leave only one possibility.
    rw [hp, hp']

/-- **Equation (7)** (proof of Proposition 8, balanced case): for `(((a,b):x,c):y,(d,e):z)`,
`XYZ = 6u₅ + 9u₇`, `XY³Z = 15u₇`, hence `y = (1/2) log((2u₅ + 3u₇)/(5u₇))`, and the argument of
the logarithm is greater than `1`. -/
theorem equation7 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = balanced5) :
    exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) * exp (-σ.length {3, 4}) =
        6 * u σ 5 + 9 * u σ 7 ∧
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 * exp (-σ.length {3, 4}) =
        15 * u σ 7 ∧
      σ.length {0, 1, 2} = 1 / 2 * log ((2 * u σ 5 + 3 * u σ 7) / (5 * u σ 7)) ∧
      1 < (2 * u σ 5 + 3 * u σ 7) / (5 * u σ 7) := by
  obtain ⟨-, -, -, -, -, h5, -, -, -, h7, -⟩ := equation11 σ hσ
  obtain ⟨-, -, hY, hY1, -, -⟩ := tables_bal_bounds σ hσ
  -- the argument of the logarithm is `XYZ/3 / (XYZ/3 · Y²) = Y⁻²`
  have hn : 2 * u σ 5 + 3 * u σ 7 =
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) * exp (-σ.length {3, 4}) / 3 * 1 := by
    rw [h5, h7]; ring
  have hd : 5 * u σ 7 =
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) * exp (-σ.length {3, 4}) / 3 *
        exp (-σ.length {0, 1, 2}) ^ 2 := by
    rw [h7]; ring
  have r : (2 * u σ 5 + 3 * u σ 7) / (5 * u σ 7) = (exp (-σ.length {0, 1, 2}) ^ 2)⁻¹ := by
    rw [hn, hd, mul_div_mul_left _ _ (by positivity), one_div]
  refine ⟨by rw [h5, h7]; ring, by rw [h7]; ring, ?_, ?_⟩
  · rw [r, log_inv, log_pow, log_exp]
    push_cast
    ring
  · rw [r, one_lt_inv₀ (by positivity)]
    exact pow_lt_one₀ hY.le hY1 (by norm_num)

/-- **Equation (8)** (proof of Proposition 8, caterpillar case): for
`((((a,b):x,c):y,d):z,e)`, `XY³ = 3(-u₂ + u₃ + 5u₇)`, `XY³Z⁶ = 15(u₂ - u₃ + u₇)`, hence
`z = (1/6) log((-u₂ + u₃ + 5u₇)/(5u₂ - 5u₃ + 5u₇))`, and the argument of the logarithm is greater
than `1`. -/
theorem equation8 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 =
        3 * (-u σ 2 + u σ 3 + 5 * u σ 7) ∧
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 *
          exp (-σ.length {0, 1, 2, 3}) ^ 6 = 15 * (u σ 2 - u σ 3 + u σ 7) ∧
      σ.length {0, 1, 2, 3} =
        1 / 6 * log ((-u σ 2 + u σ 3 + 5 * u σ 7) / (5 * u σ 2 - 5 * u σ 3 + 5 * u σ 7)) ∧
      1 < (-u σ 2 + u σ 3 + 5 * u σ 7) / (5 * u σ 2 - 5 * u σ 3 + 5 * u σ 7) := by
  obtain ⟨-, h2, h3, -, -, -, -, -, -, h7, -⟩ := equation12 σ hσ
  obtain ⟨-, -, -, -, hZ, hZ1⟩ := tables_cat_bounds σ hσ
  -- the argument of the logarithm is `XY³/3 / (XY³/3 · Z⁶) = Z⁻⁶`
  have hn : -u σ 2 + u σ 3 + 5 * u σ 7 =
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 / 3 * 1 := by
    rw [h2, h3, h7]; ring
  have hd : 5 * u σ 2 - 5 * u σ 3 + 5 * u σ 7 =
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 / 3 *
        exp (-σ.length {0, 1, 2, 3}) ^ 6 := by
    rw [h2, h3, h7]; ring
  have r : (-u σ 2 + u σ 3 + 5 * u σ 7) / (5 * u σ 2 - 5 * u σ 3 + 5 * u σ 7) =
      (exp (-σ.length {0, 1, 2, 3}) ^ 6)⁻¹ := by
    rw [hn, hd, mul_div_mul_left _ _ (by positivity), one_div]
  refine ⟨by rw [hn]; ring, by rw [h2, h3, h7]; ring, ?_, ?_⟩
  · rw [r, log_inv, log_pow, log_exp]
    push_cast
    ring
  · rw [r, one_lt_inv₀ (by positivity)]
    exact pow_lt_one₀ hZ.le hZ1 (by norm_num)

/-- **Equation (9)** (proof of Proposition 8, pseudocaterpillar case): for
`(((a,b):x,(d,e):y):z,c)`, `XY = 12u₅ + 3u₈`, `XYZ⁶ = 30u₅ - 15u₈`, hence
`z = (1/6) log((4u₅ + u₈)/(10u₅ - 5u₈))`, and the argument of the logarithm is greater than `1`. -/
theorem equation9 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) :
    exp (-σ.length {0, 1}) * exp (-σ.length {3, 4}) = 12 * u σ 5 + 3 * u σ 8 ∧
      exp (-σ.length {0, 1}) * exp (-σ.length {3, 4}) * exp (-σ.length {0, 1, 3, 4}) ^ 6 =
        30 * u σ 5 - 15 * u σ 8 ∧
      σ.length {0, 1, 3, 4} = 1 / 6 * log ((4 * u σ 5 + u σ 8) / (10 * u σ 5 - 5 * u σ 8)) ∧
      1 < (4 * u σ 5 + u σ 8) / (10 * u σ 5 - 5 * u σ 8) := by
  obtain ⟨-, -, -, -, -, h5, -, -, -, -, -, -, -, h8, -⟩ := equation13 σ hσ
  obtain ⟨-, -, -, -, hZ, hZ1⟩ := tables_pse_bounds σ hσ
  -- the argument of the logarithm is `XY/3 / (XY/3 · Z⁶) = Z⁻⁶`
  have hn : 4 * u σ 5 + u σ 8 = exp (-σ.length {0, 1}) * exp (-σ.length {3, 4}) / 3 * 1 := by
    rw [h5, h8]; ring
  have hd : 10 * u σ 5 - 5 * u σ 8 =
      exp (-σ.length {0, 1}) * exp (-σ.length {3, 4}) / 3 * exp (-σ.length {0, 1, 3, 4}) ^ 6 := by
    rw [h5, h8]; ring
  have r : (4 * u σ 5 + u σ 8) / (10 * u σ 5 - 5 * u σ 8) =
      (exp (-σ.length {0, 1, 3, 4}) ^ 6)⁻¹ := by
    rw [hn, hd, mul_div_mul_left _ _ (by positivity), one_div]
  refine ⟨by rw [h5, h8]; ring, by rw [h5, h8]; ring, ?_, ?_⟩
  · rw [r, log_inv, log_pow, log_exp]
    push_cast
    ring
  · rw [r, one_lt_inv₀ (by positivity)]
    exact pow_lt_one₀ hZ.le hZ1 (by norm_num)

/-- Proof of Proposition 8: the edge above a cluster `A` whose complement `B` is not a cluster (an
edge not at the root) has the length of the split `A | B` of `λ⁻`. -/
theorem p78_length_eq_of_not_root {H : Finset (Finset (Fin 5))} {τ τ' : SpeciesTree (Fin 5)}
    (hτ : τ.clusters = H) (hτ' : τ'.clusters = H) (hU : τ.SameUnrootedMetricTree τ')
    {A B : Finset (Fin 5)}
    (hAB : Aᶜ = B ∧ A ∈ H ∧ A ≠ univ ∧ B ∉ H ∧ 2 ≤ #A ∧ 2 ≤ #B) :
    τ.length A = τ'.length A := by
  obtain ⟨hAB, hA, hAu, hB, h2, h2c⟩ := hAB
  rw [← five_unrootedLength_mem τ hAB (hτ ▸ hA) hAu (hτ ▸ hB),
    ← five_unrootedLength_mem τ' hAB (hτ' ▸ hA) hAu (hτ' ▸ hB)]
  exact hU.2 A (classify_mem_unroot.2 (Or.inl ⟨hτ ▸ hA, hAu⟩)) h2 (hAB ▸ h2c)

/-- Proof of Proposition 8: the two edges at the root, above `A` and above `B = Aᶜ`, form the edge
`A | B` of `λ⁻`, so the length of one of them determines the other. -/
theorem p78_length_eq_of_sibling {H : Finset (Finset (Fin 5))} {τ τ' : SpeciesTree (Fin 5)}
    (hτ : τ.clusters = H) (hτ' : τ'.clusters = H) (hU : τ.SameUnrootedMetricTree τ')
    {A B : Finset (Fin 5)}
    (hAB : Aᶜ = B ∧ A ∈ H ∧ A ≠ univ ∧ B ∈ H ∧ B ≠ univ ∧ 2 ≤ #A ∧ 2 ≤ #B)
    (hl : τ.length B = τ'.length B) : τ.length A = τ'.length A := by
  obtain ⟨hAB, hA, hAu, hB, hBu, h2, h2c⟩ := hAB
  have e := five_unrootedLength_both τ hAB (hτ ▸ hA) hAu (hτ ▸ hB) hBu
  have e' := five_unrootedLength_both τ' hAB (hτ' ▸ hA) hAu (hτ' ▸ hB) hBu
  have := hU.2 A (classify_mem_unroot.2 (Or.inl ⟨hτ ▸ hA, hAu⟩)) h2 (hAB ▸ h2c)
  linarith

/-- **Proposition 8** (`prop:5taxa`). For `|X| = 5`, `ℙ_{σ⁺}` determines `σ⁺ = (ψ⁺, λ⁺)`. -/
theorem proposition8 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := by
  -- By Proposition 7, `ψ⁺` is determined; by Corollary 6, `λ⁻` is determined.
  have hψ := proposition7 hX σ σ' hσ hσ' h
  have hU := corollary6 σ σ' hσ hσ' h
  -- Relabelling the taxa, we may assume that `ψ⁺` is `(((a,b),c),(d,e))`, `((((a,b),c),d),e)` or
  -- `(((a,b),(d,e)),c)`.
  obtain ⟨e, he⟩ := p78_exists_relabel_rep hX σ hσ
  rw [← SpeciesTree.sameRootedMetricTree_relabel_iff σ σ' e]
  have hψ' : (σ'.relabel e).clusters = (σ.relabel e).clusters := by
    rw [SpeciesTree.relabel_clusters, SpeciesTree.relabel_clusters, hψ]
  have hU' := (SpeciesTree.sameUnrootedMetricTree_relabel_iff σ σ' e).2 hU
  have hu := cls_u_congr ((SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e).2 h)
  generalize σ.relabel e = τ at he hψ' hU' hu ⊢
  generalize σ'.relabel e = τ' at hψ' hU' hu ⊢
  -- Every edge not at the root has the length of its split in `λ⁻`; it remains to determine the
  -- edges at the root.
  rcases he with hb | hc | hp
  · -- `σ⁺ = (((a,b):x,c):y,(d,e):z)`: `y` is given by (7), and `y + z` is the length of the edge
    -- `abc|de` of `λ⁻`.
    have hb' := hψ'.trans hb
    have hy : τ.length {0, 1, 2} = τ'.length {0, 1, 2} := by
      rw [(equation7 τ hb).2.2.1, (equation7 τ' hb').2.2.1, hu 5, hu 7]
    refine five_sameRootedMetricTree_of_lengths (C := {{0, 1}, {0, 1, 2}, {3, 4}}) hb hb' ?_
    simp only [mem_insert, mem_singleton]
    rintro A (rfl | rfl | rfl)
    · exact p78_length_eq_of_not_root hb hb' hU' (B := {2, 3, 4}) (by decide)
    · exact hy
    · exact p78_length_eq_of_sibling hb hb' hU' (B := {0, 1, 2}) (by decide) hy
  · -- `σ⁺ = ((((a,b):x,c):y,d):z,e)`: `z` is given by (8).
    have hc' := hψ'.trans hc
    refine five_sameRootedMetricTree_of_lengths (C := {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}) hc hc' ?_
    simp only [mem_insert, mem_singleton]
    rintro A (rfl | rfl | rfl)
    · exact p78_length_eq_of_not_root hc hc' hU' (B := {2, 3, 4}) (by decide)
    · exact p78_length_eq_of_not_root hc hc' hU' (B := {3, 4}) (by decide)
    · rw [(equation8 τ hc).2.2.1, (equation8 τ' hc').2.2.1, hu 2, hu 3, hu 7]
  · -- `σ⁺ = (((a,b):x,(d,e):y):z,c)`: `z` is given by (9).
    have hp' := hψ'.trans hp
    refine five_sameRootedMetricTree_of_lengths (C := {{0, 1}, {3, 4}, {0, 1, 3, 4}}) hp hp' ?_
    simp only [mem_insert, mem_singleton]
    rintro A (rfl | rfl | rfl)
    · exact p78_length_eq_of_not_root hp hp' hU' (B := {2, 3, 4}) (by decide)
    · exact p78_length_eq_of_not_root hp hp' hU' (B := {0, 1, 2}) (by decide)
    · rw [(equation9 τ hp).2.2.1, (equation9 τ' hp').2.2.1, hu 5, hu 8]

end ADR11
