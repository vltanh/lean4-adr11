module

public import ADR11.Nonbinary.FiveTaxa.Ac1Classes

/-!
# Appendix C: the rootings of the star `U5 0` and of `U5 1 = AB|CDE`

Appendix C of the paper (the proof of Proposition 11) recovers a possibly nonbinary 5-taxon
species tree `σ⁺` from its distribution of unrooted gene trees once the unrooted species tree `σ⁻`
is known: first the rooted shape, from the size of the least probable class `𝒞` of gene trees and,
when `|𝒞| = 6`, of the class `𝒞₂` with the second smallest probability; then the labelling, by
the paper's rules on the cherries of the gene trees of these classes; then the branch lengths, by
solving the equations of Table 7, `P₄` and `P₈` being told apart by whether the solved `Z` is
`< 1` or `= 1`. This module carries out the argument when `σ⁻` is the star `U5 0` (rooted shapes
`P₁` and `P₃`) or `U5 1 = AB|CDE` (rooted shapes `P₂`, `P₄`, `P₇`, `P₈`, `P₉`). The classes of
each labelled rooting are computed in `ADR11.Nonbinary.FiveTaxa.Ac1Classes`.

## Main results

* `ac1_rootings_zero`, `ac1_rootings_one`: two species trees with unrooted tree `U5 0` (resp.
  `U5 1`) and the same unrooted gene tree distribution have the same rooted metric tree.
* `ac1_shape_zero`, `ac1_shape_one`: `|𝒞|`, and `|𝒞₂|` when `|𝒞| = 6`, for each rooted shape.
* The labelling rules `ac1_P3_outgroup`, `ac1_P7_outgroup`, `ac1_P9_distinguished`,
  `ac1_P9_outgroup`, and `ac1_P4_P8_rule` (`Z < 1` for `P₈`, `Z = 1` for `P₄`).
* `ac1_P2_P3_rule`: `P₂` and `P₃` are told apart by the cherries of their 3-element classes
  (on the representatives of Table 6).
* `ac1_topologyZero`, `ac1_topologyOne`: the rooted topology read off the gene tree classes by
  these rules; `ac1_topologyZero_eq`, `ac1_topologyOne_eq`: it is the topology of the species
  tree; `ac1_topologyZero_congr`, `ac1_topologyOne_congr`: it depends only on the distribution.
* `ac1_lengths_0_j`, `ac1_lengths_1_j`: the branch lengths of each rooting, solved from Table 7.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-! ### Cherries of the gene trees of a class -/

/-- The taxa that appear in no cherry of the gene trees `T_i`, `i ∈ S`. For a single gene tree
`T_i` this is the one taxon of `T_i` that is not in a cherry. -/
def ac1_noCherry (S : Finset ℕ) : Finset (Fin 5) :=
  univ.filter fun x => ∀ i ∈ S, ∀ A ∈ cls_cherries (T5 i), x ∉ A

/-- The taxa `y` that appear in a cherry with a taxon `d ∈ D`, `y ≠ d`, in exactly three of the
gene trees `T_i`, `i ∈ S`. -/
def ac1_threeCherries (D : Finset (Fin 5)) (S : Finset ℕ) : Finset (Fin 5) :=
  univ.filter fun y => ∃ d ∈ D, y ≠ d ∧
    #(S.filter fun i => ({d, y} : Finset (Fin 5)) ∈ cls_cherries (T5 i)) = 3

/-- The gene trees outside the least probable class and the class with the second smallest
probability. For `P₉` these are the six most probable gene trees, the union of the two most
probable classes (which may coincide). -/
noncomputable def ac1_topSix (τ : SpeciesTree (Fin 5)) : Finset ℕ :=
  Icc 1 15 \ (cls_leastClass τ ∪ cls_secondClass τ)

/-- The transformed length `Z = e^{-z}` of the edge `z` of `P₈ = ((a,b):z,(c,d,e):y)`, solved from
its equations of Table 7 in this labelling (`u₄ = YZ/6 - Y³Z/10` and `u₅ = Y³Z/15`, where
`Y = e^{-y}`): `YZ = 6u₄ + 9u₅` and `Y³Z = 15u₅`, so `Z² = (6u₄ + 9u₅)³/(15u₅)`. -/
noncomputable def ac1_solveZ (τ : SpeciesTree (Fin 5)) : ℝ :=
  √((6 * u τ 4 + 9 * u τ 5) ^ 3 / (15 * u τ 5))

/-- The five taxa. -/
theorem ac1_fin5 (x : Fin 5) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
  fin_cases x <;> simp

/-! ### The shape: `|𝒞|`, and `|𝒞₂|` when `|𝒞| = 6` -/

/-- Appendix C, `|𝒞|` for the rootings of the star `U5 0`: `|𝒞| = 15` for `P₁`, and `|𝒞| = 12`
for the rootings of shape `P₃` (on the pendant edge of a taxon `x`). -/
theorem ac1_shape_zero (τ : SpeciesTree (Fin 5)) :
    (τ.clusters = hierarchyOf ∅ → #(cls_leastClass τ) = 15) ∧
      ∀ x : Fin 5, τ.clusters = hierarchyOf {univ.erase x} → #(cls_leastClass τ) = 12 := by
  refine ⟨fun h => by rw [ac1_classes_0_0 τ h]; decide, fun x h => ?_⟩
  rcases ac1_fin5 x with rfl | rfl | rfl | rfl | rfl
  · rw [(ac1_classes_0_1 τ (h.trans (by decide))).1]; decide
  · rw [(ac1_classes_0_2 τ (h.trans (by decide))).1]; decide
  · rw [(ac1_classes_0_3 τ (h.trans (by decide))).1]; decide
  · rw [(ac1_classes_0_4 τ (h.trans (by decide))).1]; decide
  · rw [(ac1_classes_0_5 τ (h.trans (by decide))).1]; decide

/-- Appendix C, `|𝒞|` and `|𝒞₂|` for the rootings of `U5 1`: `|𝒞| = 12` for `P₂`; `|𝒞| = 10` for
the rootings of shape `P₇` (with outgroup `x ∈ {c, d, e}`); `|𝒞| = 6` and `|𝒞₂| = 3` for the
rootings of shape `P₉` (with the clusters `{2, 3, 4}` and `{2, 3, 4} ∪ {d}` and the outgroup `o`,
where `{d, o} = {0, 1}`); `|𝒞| = 6` and `|𝒞₂| = 6` for `P₄` and `P₈`. -/
theorem ac1_shape_one (τ : SpeciesTree (Fin 5)) :
    (τ.clusters = hierarchyOf {{0, 1}} → #(cls_leastClass τ) = 12) ∧
    (∀ x ∈ ({2, 3, 4} : Finset (Fin 5)), τ.clusters = hierarchyOf {{0, 1}, univ.erase x} →
      #(cls_leastClass τ) = 10) ∧
    (∀ d o : Fin 5, d = 1 ∧ o = 0 ∨ d = 0 ∧ o = 1 →
      τ.clusters = hierarchyOf {univ \ {d, o}, univ.erase o} →
      #(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 3) ∧
    (τ.clusters = hierarchyOf {{2, 3, 4}} →
      #(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 6) ∧
    (τ.clusters = hierarchyOf {{0, 1}, {2, 3, 4}} →
      #(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 6) := by
  refine ⟨fun h => ?_, fun x hx h => ?_, fun d o hdo h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [ac1_classes_1_0 τ h]; decide
  · simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · rw [(ac1_classes_1_5 τ (h.trans (by decide))).1]; decide
    · rw [(ac1_classes_1_6 τ (h.trans (by decide))).1]; decide
    · rw [(ac1_classes_1_7 τ (h.trans (by decide))).1]; decide
  · rcases hdo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨e1, e2⟩ := ac1_classes_1_3 τ (h.trans (by decide))
      rw [e1, e2]; decide
    · obtain ⟨e1, e2⟩ := ac1_classes_1_4 τ (h.trans (by decide))
      rw [e1, e2]; decide
  · obtain ⟨e1, e2⟩ := ac1_classes_1_1 τ h
    rw [e1, e2]; decide
  · obtain ⟨e1, e2⟩ := ac1_classes_1_2 τ h
    rw [e1, e2]; decide

/-! ### The labelling -/

/-- Appendix C, the labelling of `P₃`: for the rooting of the star `U5 0` with outgroup `x` (of
shape `P₃`), the class with the second smallest probability is the 3-element class, and `x` is the
taxon that appears in no cherry of its gene trees. -/
theorem ac1_P3_outgroup (τ : SpeciesTree (Fin 5)) (x : Fin 5)
    (h : τ.clusters = hierarchyOf {univ.erase x}) :
    #(cls_secondClass τ) = 3 ∧ ac1_noCherry (cls_secondClass τ) = {x} := by
  rcases ac1_fin5 x with rfl | rfl | rfl | rfl | rfl
  · rw [(ac1_classes_0_1 τ (h.trans (by decide))).2]; decide
  · rw [(ac1_classes_0_2 τ (h.trans (by decide))).2]; decide
  · rw [(ac1_classes_0_3 τ (h.trans (by decide))).2]; decide
  · rw [(ac1_classes_0_4 τ (h.trans (by decide))).2]; decide
  · rw [(ac1_classes_0_5 τ (h.trans (by decide))).2]; decide

/-- Appendix C, the labelling of `P₇`: for the rooting `(((a,b),·,·),x)` of `U5 1` with outgroup
`x ∈ {c, d, e}` (of shape `P₇`; its resolved cherry `{a, b}` is the side with two taxa of the
split of `U5 1`), there is one most probable gene tree, and `x` is the taxon that appears in none of
its cherries. -/
theorem ac1_P7_outgroup (τ : SpeciesTree (Fin 5)) (x : Fin 5)
    (hx : x ∈ ({2, 3, 4} : Finset (Fin 5))) (h : τ.clusters = hierarchyOf {{0, 1}, univ.erase x}) :
    #(cls_mostProbable τ) = 1 ∧ ac1_noCherry (cls_mostProbable τ) = {x} := by
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · rw [(ac1_classes_1_5 τ (h.trans (by decide))).2]; decide
  · rw [(ac1_classes_1_6 τ (h.trans (by decide))).2]; decide
  · rw [(ac1_classes_1_7 τ (h.trans (by decide))).2]; decide

/-- Appendix C, the labelling of `P₉`, first step: for the rooting of `U5 1` of shape `P₉` with the
clusters `{2, 3, 4}` (the polytomy) and `{2, 3, 4} ∪ {d}` and the outgroup `o`, where
`{d, o} = {0, 1}`, the non-outgroup taxon `d` that is not descended from the polytomy is the taxon
that appears in no cherry of the gene trees of the class with the second smallest probability. -/
theorem ac1_P9_distinguished (τ : SpeciesTree (Fin 5)) (d o : Fin 5)
    (hdo : d = 1 ∧ o = 0 ∨ d = 0 ∧ o = 1)
    (h : τ.clusters = hierarchyOf {univ \ {d, o}, univ.erase o}) :
    ac1_noCherry (cls_secondClass τ) = {d} := by
  rcases hdo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [(ac1_classes_1_3 τ (h.trans (by decide))).2]; decide
  · rw [(ac1_classes_1_4 τ (h.trans (by decide))).2]; decide

/-- Appendix C, the labelling of `P₉`, second step: with `d` as in `ac1_P9_distinguished`, the
outgroup `o` is the taxon that appears in a cherry with `d` in three of the six most probable
gene trees (the union of the two most probable classes). -/
theorem ac1_P9_outgroup (τ : SpeciesTree (Fin 5)) (d o : Fin 5)
    (hdo : d = 1 ∧ o = 0 ∨ d = 0 ∧ o = 1)
    (h : τ.clusters = hierarchyOf {univ \ {d, o}, univ.erase o}) :
    #(ac1_topSix τ) = 6 ∧ ac1_threeCherries {d} (ac1_topSix τ) = {o} := by
  rcases hdo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨e1, e2⟩ := ac1_classes_1_3 τ (h.trans (by decide))
    rw [ac1_topSix, e1, e2]; decide
  · obtain ⟨e1, e2⟩ := ac1_classes_1_4 τ (h.trans (by decide))
    rw [ac1_topSix, e1, e2]; decide

/-! ### `P₄` versus `P₈` -/

/-- Appendix C, `P₄` versus `P₈`: `P₈ = ((a,b):z,(c,d,e):y)` degenerates to `P₄ = ((c,d,e):y,a,b)`
as `z → 0` (`Z → 1`). Solving the equations of Table 7 for `P₈` for `Z` (`ac1_solveZ`) gives
`Z = e^{-z} < 1` if the species tree is `P₈`, and `Z = 1` if it is `P₄`. -/
theorem ac1_P4_P8_rule (τ : SpeciesTree (Fin 5)) :
    (τ.clusters = hierarchyOf {{0, 1}, {2, 3, 4}} →
      ac1_solveZ τ = exp (-τ.length {0, 1}) ∧ ac1_solveZ τ < 1) ∧
    (τ.clusters = hierarchyOf {{2, 3, 4}} → ac1_solveZ τ = 1) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨-, -, -, h4, h5, -⟩ := rootingDist5_1_2 τ h
    obtain ⟨z0, z1⟩ := five_exp_bounds τ (A := {0, 1}) (by rw [h]; decide) (by decide)
    obtain ⟨y0, -⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
    have key : (6 * u τ 4 + 9 * u τ 5) ^ 3 / (15 * u τ 5) = exp (-τ.length {0, 1}) ^ 2 := by
      rw [h4, h5]
      have := z0.ne'
      have := y0.ne'
      field_simp
      ring
    have e : ac1_solveZ τ = exp (-τ.length {0, 1}) := by
      rw [ac1_solveZ, key, Real.sqrt_sq z0.le]
    exact ⟨e, e ▸ z1⟩
  · obtain ⟨-, -, -, h4, h5, -⟩ := rootingDist5_1_1 τ h
    obtain ⟨y0, -⟩ := five_exp_bounds τ (A := {2, 3, 4}) (by rw [h]; decide) (by decide)
    have key : (6 * u τ 4 + 9 * u τ 5) ^ 3 / (15 * u τ 5) = 1 := by
      rw [h4, h5]
      have := y0.ne'
      field_simp
      ring
    rw [ac1_solveZ, key, Real.sqrt_one]

/-! ### `P₂` versus `P₃` -/

/-- Appendix C, `|𝒞| = 12`: `P₂` and `P₃` are told apart since all gene trees in the 3-element
class for `P₃` have the same taxon not occurring in a cherry, while for `P₂` the gene trees in the
3-element class have different taxa in this role. On the representatives `P₂ = (a,b,c,(d,e))` and
`P₃ = ((a,b,c,d),e)` of Table 6: both have `|𝒞| = 12`, and their class with the second smallest
probability is the 3-element class; the taxa in no cherry of its gene trees are pairwise
different for `P₂` and all equal for `P₃`; hence the two have different distributions. -/
theorem ac1_P2_P3_rule :
    (∀ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 2 →
      #(cls_leastClass σ) = 12 ∧ #(cls_secondClass σ) = 3 ∧
        ∀ i ∈ cls_secondClass σ, ∀ j ∈ cls_secondClass σ, i ≠ j →
          ac1_noCherry {i} ≠ ac1_noCherry {j}) ∧
    (∀ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 3 →
      #(cls_leastClass σ) = 12 ∧ #(cls_secondClass σ) = 3 ∧
        ∃ x : Fin 5, ∀ i ∈ cls_secondClass σ, ac1_noCherry {i} = {x}) ∧
    ∀ σ σ' : SpeciesTree (Fin 5), σ.clusters = polytomy5 2 → σ'.clusters = polytomy5 3 →
      σ.unrootedDist id ≠ σ'.unrootedDist id := by
  have h2 : ∀ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 2 →
      #(cls_leastClass σ) = 12 ∧ #(cls_secondClass σ) = 3 ∧
        ∀ i ∈ cls_secondClass σ, ∀ j ∈ cls_secondClass σ, i ≠ j →
          ac1_noCherry {i} ≠ ac1_noCherry {j} := fun σ h => by
    obtain ⟨e1, e2⟩ := ac1_classes_P2 σ h
    rw [e1, e2]
    decide
  have h3 : ∀ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 3 →
      #(cls_leastClass σ) = 12 ∧ #(cls_secondClass σ) = 3 ∧
        ∃ x : Fin 5, ∀ i ∈ cls_secondClass σ, ac1_noCherry {i} = {x} := fun σ h => by
    obtain ⟨e1, e2⟩ := ac1_classes_P3 σ h
    rw [e1, e2]
    exact ⟨by decide, by decide, 4, by decide⟩
  refine ⟨h2, h3, fun σ σ' h h' hd => ?_⟩
  obtain ⟨-, hc, hdiff⟩ := h2 σ h
  obtain ⟨-, -, x, hx⟩ := h3 σ' h'
  rw [cls_secondClass_congr hd] at hc hdiff
  -- two different gene trees of the 3-element class
  obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.1 (by omega : 1 < #(cls_secondClass σ'))
  exact hdiff i hi j hj hij ((hx i hi).trans (hx j hj).symm)

/-! ### The rooted topology read off the gene tree classes -/

/-- Appendix C for the rootings of the star `U5 0`: the rooted topology read off the classes of
gene trees. If `|𝒞| = 15` the species tree is `P₁`. If `|𝒞| = 12` it is `P₃` (the rooted shape
`P₂` does not have the unrooted tree `U5 0`), whose outgroup is the taxon that appears in no cherry
of the gene trees of the 3-element class. -/
noncomputable def ac1_topologyZero (τ : SpeciesTree (Fin 5)) : Finset (Finset (Fin 5)) :=
  if #(cls_leastClass τ) = 15 then hierarchyOf ∅
  else if #(cls_leastClass τ) = 12 then hierarchyOf {univ \ ac1_noCherry (cls_secondClass τ)}
  else ∅

/-- Appendix C for the rootings of `U5 1 = AB|CDE`: the rooted topology read off the classes of
gene trees. If `|𝒞| = 12` the species tree is `P₂` (not `P₃`, which does not have the unrooted
tree `U5 1`), and its labelling is that of `U5 1`. If `|𝒞| = 10` it is `P₇` (not `P₅`): its
resolved cherry `{a, b}` is given by `U5 1`, and its outgroup is the taxon in no cherry of the most
probable gene tree. If `|𝒞| = 6` and `|𝒞₂| = 3` it is `P₉`: the non-outgroup taxon `d` not
descended from the polytomy is the taxon in no cherry of the gene trees of `𝒞₂`, and the outgroup
is the taxon in a cherry with `d` in three of the six most probable gene trees. If `|𝒞| = 6` and
`|𝒞₂| = 6` it is `P₄` or `P₈`, labelled by `U5 1`: `P₈` if the solved `Z` is `< 1`, and `P₄`
otherwise (`Z = 1`). -/
noncomputable def ac1_topologyOne (τ : SpeciesTree (Fin 5)) : Finset (Finset (Fin 5)) :=
  if #(cls_leastClass τ) = 12 then hierarchyOf {{0, 1}}
  else if #(cls_leastClass τ) = 10 then
    hierarchyOf {{0, 1}, univ \ ac1_noCherry (cls_mostProbable τ)}
  else if #(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 3 then
    hierarchyOf {univ \ (ac1_noCherry (cls_secondClass τ) ∪
        ac1_threeCherries (ac1_noCherry (cls_secondClass τ)) (ac1_topSix τ)),
      univ \ ac1_threeCherries (ac1_noCherry (cls_secondClass τ)) (ac1_topSix τ)}
  else if #(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 6 then
    if ac1_solveZ τ < 1 then hierarchyOf {{0, 1}, {2, 3, 4}} else hierarchyOf {{2, 3, 4}}
  else ∅

/-- The topology read off the gene tree classes depends only on the distribution. -/
theorem ac1_topologyZero_congr {τ τ' : SpeciesTree (Fin 5)}
    (h : τ.unrootedDist id = τ'.unrootedDist id) : ac1_topologyZero τ = ac1_topologyZero τ' := by
  unfold ac1_topologyZero
  rw [cls_leastClass_congr h, cls_secondClass_congr h]

/-- The topology read off the gene tree classes depends only on the distribution. -/
theorem ac1_topologyOne_congr {τ τ' : SpeciesTree (Fin 5)}
    (h : τ.unrootedDist id = τ'.unrootedDist id) : ac1_topologyOne τ = ac1_topologyOne τ' := by
  have hZ : ac1_solveZ τ = ac1_solveZ τ' := by
    rw [ac1_solveZ, ac1_solveZ, cls_u_congr h 4, cls_u_congr h 5]
  unfold ac1_topologyOne ac1_topSix
  rw [cls_leastClass_congr h, cls_secondClass_congr h, cls_mostProbable_congr h, hZ]

/-- Appendix C for the rootings of the star `U5 0`: the shape from `|𝒞|` (`ac1_shape_zero`), then
the labelling of `P₃` (`ac1_P3_outgroup`), give the rooted topology of the species tree. -/
theorem ac1_topologyZero_eq (τ : SpeciesTree (Fin 5)) (hk : unroot τ.clusters = U5 0) :
    ac1_topologyZero τ = τ.clusters := by
  obtain ⟨s1, s3⟩ := ac1_shape_zero τ
  -- a rooting of shape `P₃`, with outgroup `x`
  have P3 : ∀ x : Fin 5, τ.clusters = hierarchyOf {univ.erase x} →
      ac1_topologyZero τ = τ.clusters := fun x hx => by
    have c12 := s3 x hx
    have c15 : ¬ #(cls_leastClass τ) = 15 := by rw [c12]; decide
    rw [ac1_topologyZero, ite_eq_right c15, ite_eq_left c12, (ac1_P3_outgroup τ x hx).2, hx,
      sdiff_singleton_eq_erase]
  have hR := classify_mem_rootings5 τ 0 (by decide) hk
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h
  · -- `P₁`
    rw [ac1_topologyZero, ite_eq_left (s1 h), h]
  · exact P3 0 (h.trans (by decide))
  · exact P3 1 (h.trans (by decide))
  · exact P3 2 (h.trans (by decide))
  · exact P3 3 (h.trans (by decide))
  · exact P3 4 (h.trans (by decide))

/-- Appendix C for the rootings of `U5 1`: the shape from `|𝒞|` and `|𝒞₂|` (`ac1_shape_one`), the
labellings of `P₇` and `P₉` (`ac1_P7_outgroup`, `ac1_P9_distinguished`, `ac1_P9_outgroup`), and
`P₄` versus `P₈` (`ac1_P4_P8_rule`) give the rooted topology of the species tree. -/
theorem ac1_topologyOne_eq (τ : SpeciesTree (Fin 5)) (hk : unroot τ.clusters = U5 1) :
    ac1_topologyOne τ = τ.clusters := by
  obtain ⟨s2, s7, s9, s4, s8⟩ := ac1_shape_one τ
  -- a rooting of shape `P₇`, with outgroup `x`
  have P7 : ∀ x ∈ ({2, 3, 4} : Finset (Fin 5)),
      τ.clusters = hierarchyOf {{0, 1}, univ.erase x} → ac1_topologyOne τ = τ.clusters :=
    fun x hx h => by
      have c10 := s7 x hx h
      have c12 : ¬ #(cls_leastClass τ) = 12 := by rw [c10]; decide
      rw [ac1_topologyOne, ite_eq_right c12, ite_eq_left c10, (ac1_P7_outgroup τ x hx h).2, h,
        sdiff_singleton_eq_erase]
  -- a rooting of shape `P₉`, with distinguished taxon `d` and outgroup `o`
  have P9 : ∀ d o : Fin 5, d = 1 ∧ o = 0 ∨ d = 0 ∧ o = 1 →
      τ.clusters = hierarchyOf {univ \ {d, o}, univ.erase o} →
      ac1_topologyOne τ = τ.clusters := fun d o hdo h => by
    obtain ⟨c6, c3⟩ := s9 d o hdo h
    have c12 : ¬ #(cls_leastClass τ) = 12 := by rw [c6]; decide
    have c10 : ¬ #(cls_leastClass τ) = 10 := by rw [c6]; decide
    rw [ac1_topologyOne, ite_eq_right c12, ite_eq_right c10, ite_eq_left ⟨c6, c3⟩,
      ac1_P9_distinguished τ d o hdo h, (ac1_P9_outgroup τ d o hdo h).2, h,
      sdiff_singleton_eq_erase, ← insert_eq]
  have hR := classify_mem_rootings5 τ 1 (by decide) hk
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h | h | h | h | h | h | h | h
  · -- `P₂`
    rw [ac1_topologyOne, ite_eq_left (s2 h), h]
  · -- `P₄`: `Z = 1`
    obtain ⟨c6, c6'⟩ := s4 h
    have c12 : ¬ #(cls_leastClass τ) = 12 := by rw [c6]; decide
    have c10 : ¬ #(cls_leastClass τ) = 10 := by rw [c6]; decide
    have c3 : ¬ (#(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 3) := by
      rw [c6, c6']; decide
    have hZ : ¬ ac1_solveZ τ < 1 := by rw [(ac1_P4_P8_rule τ).2 h]; exact lt_irrefl 1
    rw [ac1_topologyOne, ite_eq_right c12, ite_eq_right c10, ite_eq_right c3,
      ite_eq_left ⟨c6, c6'⟩, ite_eq_right hZ, h]
  · -- `P₈`: `Z < 1`
    obtain ⟨c6, c6'⟩ := s8 h
    have c12 : ¬ #(cls_leastClass τ) = 12 := by rw [c6]; decide
    have c10 : ¬ #(cls_leastClass τ) = 10 := by rw [c6]; decide
    have c3 : ¬ (#(cls_leastClass τ) = 6 ∧ #(cls_secondClass τ) = 3) := by
      rw [c6, c6']; decide
    rw [ac1_topologyOne, ite_eq_right c12, ite_eq_right c10, ite_eq_right c3,
      ite_eq_left ⟨c6, c6'⟩, ite_eq_left ((ac1_P4_P8_rule τ).1 h).2, h]
  · exact P9 1 0 (Or.inl ⟨rfl, rfl⟩) (h.trans (by decide))
  · exact P9 0 1 (Or.inr ⟨rfl, rfl⟩) (h.trans (by decide))
  · exact P7 2 (by decide) (h.trans (by decide))
  · exact P7 3 (by decide) (h.trans (by decide))
  · exact P7 4 (by decide) (h.trans (by decide))

/-! ### The branch lengths, solved from Table 7 -/

/-- Two species trees with the hierarchy `hierarchyOf {C}` have the same rooted metric tree if they
give the same probability `u_i = A Z^n + B` (`Z = e^{-ℓ(C)}`, `A ≠ 0`, `n ≠ 0`): `Z` is solved
from it. -/
theorem ac1_solve_one {τ τ' : SpeciesTree (Fin 5)} {C : Finset (Fin 5)} {i n : ℕ} {A B : ℝ}
    (h : τ.clusters = hierarchyOf {C}) (h' : τ'.clusters = hierarchyOf {C}) (hn : n ≠ 0)
    (hA : A ≠ 0) (hu : u τ i = u τ' i) (f : u τ i = A * exp (-τ.length C) ^ n + B)
    (f' : u τ' i = A * exp (-τ'.length C) ^ n + B) : τ.SameRootedMetricTree τ' :=
  five_sameRootedMetricTree_of_lengths h h' fun D hD => by
    rw [mem_singleton.1 hD]
    exact five_length_eq hn hA (hu.symm.trans f) f'

/-- `P₃ = ((b,c,d,e):z,a)`: `u₁ = 1/18 + Z⁶/90` (Table 7) gives `Z`. -/
theorem ac1_lengths_0_1 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{1, 2, 3, 4}}) (h' : τ'.clusters = hierarchyOf {{1, 2, 3, 4}}) :
    τ.SameRootedMetricTree τ' := by
  obtain ⟨f, -⟩ := rootingDist5_0_1 τ h
  obtain ⟨f', -⟩ := rootingDist5_0_1 τ' h'
  exact ac1_solve_one h h' (by norm_num) (by norm_num) (hu 1) f f'

/-- `P₃ = ((a,c,d,e):z,b)`: `u₁ = 1/18 + Z⁶/90` (Table 7) gives `Z`. -/
theorem ac1_lengths_0_2 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{0, 2, 3, 4}}) (h' : τ'.clusters = hierarchyOf {{0, 2, 3, 4}}) :
    τ.SameRootedMetricTree τ' := by
  obtain ⟨f, -⟩ := rootingDist5_0_2 τ h
  obtain ⟨f', -⟩ := rootingDist5_0_2 τ' h'
  exact ac1_solve_one h h' (by norm_num) (by norm_num) (hu 1) f f'

/-- `P₃ = ((a,b,d,e):z,c)`: `u₂ = 1/18 + Z⁶/90` (Table 7) gives `Z`. -/
theorem ac1_lengths_0_3 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{0, 1, 3, 4}}) (h' : τ'.clusters = hierarchyOf {{0, 1, 3, 4}}) :
    τ.SameRootedMetricTree τ' := by
  obtain ⟨-, f, -⟩ := rootingDist5_0_3 τ h
  obtain ⟨-, f', -⟩ := rootingDist5_0_3 τ' h'
  exact ac1_solve_one h h' (by norm_num) (by norm_num) (hu 2) f f'

/-- `P₃ = ((a,b,c,e):z,d)`: `u₁ = 1/18 + Z⁶/90` (Table 7) gives `Z`. -/
theorem ac1_lengths_0_4 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{0, 1, 2, 4}}) (h' : τ'.clusters = hierarchyOf {{0, 1, 2, 4}}) :
    τ.SameRootedMetricTree τ' := by
  obtain ⟨f, -⟩ := rootingDist5_0_4 τ h
  obtain ⟨f', -⟩ := rootingDist5_0_4 τ' h'
  exact ac1_solve_one h h' (by norm_num) (by norm_num) (hu 1) f f'

/-- `P₃ = ((a,b,c,d):z,e)`: `u₁ = 1/18 + Z⁶/90` (Table 7) gives `Z`. -/
theorem ac1_lengths_0_5 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{0, 1, 2, 3}}) (h' : τ'.clusters = hierarchyOf {{0, 1, 2, 3}}) :
    τ.SameRootedMetricTree τ' := by
  obtain ⟨f, -⟩ := rootingDist5_0_5 τ h
  obtain ⟨f', -⟩ := rootingDist5_0_5 τ' h'
  exact ac1_solve_one h h' (by norm_num) (by norm_num) (hu 1) f f'

/-- `P₂ = ((a,b):z,c,d,e)`: `u₄ = Z/15` (Table 7) gives `Z`. -/
theorem ac1_lengths_1_0 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{0, 1}}) (h' : τ'.clusters = hierarchyOf {{0, 1}}) :
    τ.SameRootedMetricTree τ' := by
  obtain ⟨-, -, -, f, -⟩ := rootingDist5_1_0 τ h
  obtain ⟨-, -, -, f', -⟩ := rootingDist5_1_0 τ' h'
  exact ac1_solve_one (n := 1) (A := 1 / 15) (B := 0) h h' one_ne_zero (by norm_num) (hu 4)
    (by rw [f]; ring) (by rw [f']; ring)

/-- `P₄ = ((c,d,e):y,a,b)`: `u₅ = Y³/15` (Table 7) gives `Y`. -/
theorem ac1_lengths_1_1 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{2, 3, 4}}) (h' : τ'.clusters = hierarchyOf {{2, 3, 4}}) :
    τ.SameRootedMetricTree τ' := by
  obtain ⟨-, -, -, -, f, -⟩ := rootingDist5_1_1 τ h
  obtain ⟨-, -, -, -, f', -⟩ := rootingDist5_1_1 τ' h'
  exact ac1_solve_one (n := 3) (A := 1 / 15) (B := 0) h h' (by norm_num) (by norm_num) (hu 5)
    (by rw [f]; ring) (by rw [f']; ring)

/-- `P₈ = ((a,b):z,(c,d,e):y)`: `Z` is the solution `ac1_solveZ` of its equations (Table 7), and
then `u₅ = Y³Z/15` gives `Y`. -/
theorem ac1_lengths_1_2 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{0, 1}, {2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {2, 3, 4}}) : τ.SameRootedMetricTree τ' := by
  have hz : τ.length {0, 1} = τ'.length {0, 1} := by
    have e : ac1_solveZ τ = ac1_solveZ τ' := by rw [ac1_solveZ, ac1_solveZ, hu 4, hu 5]
    rw [((ac1_P4_P8_rule τ).1 h).1, ((ac1_P4_P8_rule τ').1 h').1] at e
    exact neg_inj.1 (Real.exp_injective e)
  obtain ⟨-, -, -, -, f, -⟩ := rootingDist5_1_2 τ h
  obtain ⟨-, -, -, -, f', -⟩ := rootingDist5_1_2 τ' h'
  have hy : τ.length {2, 3, 4} = τ'.length {2, 3, 4} :=
    five_length_eq (n := 3) (v := u τ' 5) (A := 1 / 15 * exp (-τ'.length {0, 1})) (B := 0)
      (by norm_num) (by positivity) (by rw [← hu 5, f, hz]; ring) (by rw [f']; ring)
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨hz, hy⟩

/-- `P₉ = (((c,d,e):y,b):z,a)`: `u₁ - u₅ = (1 - Y)/3` (Table 7) gives `Y`, and then
`u₅ = Y³/18 + Y³Z⁶/90` gives `Z`. -/
theorem ac1_lengths_1_3 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}) : τ.SameRootedMetricTree τ' := by
  obtain ⟨f1, -, -, -, f5, -⟩ := rootingDist5_1_3 τ h
  obtain ⟨f1', -, -, -, f5', -⟩ := rootingDist5_1_3 τ' h'
  have hy : τ.length {2, 3, 4} = τ'.length {2, 3, 4} :=
    five_length_eq (n := 1) (v := u τ' 1 - u τ' 5) (A := -1 / 3) (B := 1 / 3) one_ne_zero
      (by norm_num) (by rw [← hu 1, ← hu 5, f1, f5]; ring) (by rw [f1', f5']; ring)
  have hz : τ.length {1, 2, 3, 4} = τ'.length {1, 2, 3, 4} :=
    five_length_eq (n := 6) (v := u τ' 5) (A := 1 / 90 * exp (-τ'.length {2, 3, 4}) ^ 3)
      (B := 1 / 18 * exp (-τ'.length {2, 3, 4}) ^ 3) (by norm_num) (by positivity)
      (by rw [← hu 5, f5, hy]) (by rw [f5'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨hy, hz⟩

/-- `P₉ = (((c,d,e):y,a):z,b)`: `u₁ - u₅ = (1 - Y)/3` (Table 7) gives `Y`, and then
`u₅ = Y³/18 + Y³Z⁶/90` gives `Z`. -/
theorem ac1_lengths_1_4 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}}) : τ.SameRootedMetricTree τ' := by
  obtain ⟨f1, -, -, -, f5, -⟩ := rootingDist5_1_4 τ h
  obtain ⟨f1', -, -, -, f5', -⟩ := rootingDist5_1_4 τ' h'
  have hy : τ.length {2, 3, 4} = τ'.length {2, 3, 4} :=
    five_length_eq (n := 1) (v := u τ' 1 - u τ' 5) (A := -1 / 3) (B := 1 / 3) one_ne_zero
      (by norm_num) (by rw [← hu 1, ← hu 5, f1, f5]; ring) (by rw [f1', f5']; ring)
  have hz : τ.length {0, 2, 3, 4} = τ'.length {0, 2, 3, 4} :=
    five_length_eq (n := 6) (v := u τ' 5) (A := 1 / 90 * exp (-τ'.length {2, 3, 4}) ^ 3)
      (B := 1 / 18 * exp (-τ'.length {2, 3, 4}) ^ 3) (by norm_num) (by positivity)
      (by rw [← hu 5, f5, hy]) (by rw [f5'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨hy, hz⟩

/-- `P₇ = (((a,b):x,d,e):z,c)`: `u₈ + 4u₄ = X/3` (Table 7) gives `X`, and then
`u₄ = X/18 + XZ⁶/90` gives `Z`. -/
theorem ac1_lengths_1_5 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 3, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {0, 1, 3, 4}}) : τ.SameRootedMetricTree τ' := by
  obtain ⟨-, -, -, f4, -, -, -, f8, -⟩ := rootingDist5_1_5 τ h
  obtain ⟨-, -, -, f4', -, -, -, f8', -⟩ := rootingDist5_1_5 τ' h'
  have hx : τ.length {0, 1} = τ'.length {0, 1} :=
    five_length_eq (n := 1) (v := u τ' 8 + 4 * u τ' 4) (A := 1 / 3) (B := 0) one_ne_zero
      (by norm_num) (by rw [← hu 8, ← hu 4, f8, f4]; ring) (by rw [f8', f4']; ring)
  have hz : τ.length {0, 1, 3, 4} = τ'.length {0, 1, 3, 4} :=
    five_length_eq (n := 6) (v := u τ' 4) (A := 1 / 90 * exp (-τ'.length {0, 1}))
      (B := 1 / 18 * exp (-τ'.length {0, 1})) (by norm_num) (by positivity)
      (by rw [← hu 4, f4, hx]) (by rw [f4'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨hx, hz⟩

/-- `P₇ = (((a,b):x,c,e):z,d)`: `u₅ + 4u₄ = X/3` (Table 7) gives `X`, and then
`u₄ = X/18 + XZ⁶/90` gives `Z`. -/
theorem ac1_lengths_1_6 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 4}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 4}}) : τ.SameRootedMetricTree τ' := by
  obtain ⟨-, -, -, f4, f5, -⟩ := rootingDist5_1_6 τ h
  obtain ⟨-, -, -, f4', f5', -⟩ := rootingDist5_1_6 τ' h'
  have hx : τ.length {0, 1} = τ'.length {0, 1} :=
    five_length_eq (n := 1) (v := u τ' 5 + 4 * u τ' 4) (A := 1 / 3) (B := 0) one_ne_zero
      (by norm_num) (by rw [← hu 5, ← hu 4, f5, f4]; ring) (by rw [f5', f4']; ring)
  have hz : τ.length {0, 1, 2, 4} = τ'.length {0, 1, 2, 4} :=
    five_length_eq (n := 6) (v := u τ' 4) (A := 1 / 90 * exp (-τ'.length {0, 1}))
      (B := 1 / 18 * exp (-τ'.length {0, 1})) (by norm_num) (by positivity)
      (by rw [← hu 4, f4, hx]) (by rw [f4'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨hx, hz⟩

/-- `P₇ = (((a,b):x,c,d):z,e)`: `u₆ + 4u₄ = X/3` (Table 7) gives `X`, and then
`u₄ = X/18 + XZ⁶/90` gives `Z`. -/
theorem ac1_lengths_1_7 {τ τ' : SpeciesTree (Fin 5)} (hu : ∀ i, u τ i = u τ' i)
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 3}})
    (h' : τ'.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 3}}) : τ.SameRootedMetricTree τ' := by
  obtain ⟨-, -, -, f4, -, f6, -⟩ := rootingDist5_1_7 τ h
  obtain ⟨-, -, -, f4', -, f6', -⟩ := rootingDist5_1_7 τ' h'
  have hx : τ.length {0, 1} = τ'.length {0, 1} :=
    five_length_eq (n := 1) (v := u τ' 6 + 4 * u τ' 4) (A := 1 / 3) (B := 0) one_ne_zero
      (by norm_num) (by rw [← hu 6, ← hu 4, f6, f4]; ring) (by rw [f6', f4']; ring)
  have hz : τ.length {0, 1, 2, 3} = τ'.length {0, 1, 2, 3} :=
    five_length_eq (n := 6) (v := u τ' 4) (A := 1 / 90 * exp (-τ'.length {0, 1}))
      (B := 1 / 18 * exp (-τ'.length {0, 1})) (by norm_num) (by positivity)
      (by rw [← hu 4, f4, hx]) (by rw [f4'])
  refine five_sameRootedMetricTree_of_lengths h h' ?_
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨hx, hz⟩

/-! ### The main results -/

/-- Appendix C for the rootings of the star `U5 0` (the rooted shapes `P₁` and `P₃`): two species
trees with unrooted tree `U5 0` and the same unrooted gene tree distribution have the same rooted
metric tree. The rooted topology is read off the gene tree classes (`ac1_topologyZero_eq`: `P₁` if
`|𝒞| = 15`; `P₃` if `|𝒞| = 12`, with the outgroup in no cherry of the gene trees of the 3-element
class), and the branch length is solved from Table 7. -/
theorem ac1_rootings_zero (τ τ' : SpeciesTree (Fin 5)) (hk : unroot τ.clusters = U5 0)
    (hk' : unroot τ'.clusters = U5 0) (h : τ.unrootedDist id = τ'.unrootedDist id) :
    τ.SameRootedMetricTree τ' := by
  -- the rooted topology, read off the classes of gene trees
  have hc : τ.clusters = τ'.clusters := by
    rw [← ac1_topologyZero_eq τ hk, ← ac1_topologyZero_eq τ' hk', ac1_topologyZero_congr h]
  -- the branch lengths, solved from Table 7
  have hu := cls_u_congr h
  have hR := classify_mem_rootings5 τ 0 (by decide) hk
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h0 | h0 | h0 | h0 | h0 | h0
  · exact five_sameRootedMetricTree_of_lengths h0 (hc.symm.trans h0) (by simp)
  · exact ac1_lengths_0_1 hu h0 (hc.symm.trans h0)
  · exact ac1_lengths_0_2 hu h0 (hc.symm.trans h0)
  · exact ac1_lengths_0_3 hu h0 (hc.symm.trans h0)
  · exact ac1_lengths_0_4 hu h0 (hc.symm.trans h0)
  · exact ac1_lengths_0_5 hu h0 (hc.symm.trans h0)

/-- Appendix C for the rootings of `U5 1 = AB|CDE` (the rooted shapes `P₂`, `P₄`, `P₇`, `P₈`,
`P₉`): two species trees with unrooted tree `U5 1` and the same unrooted gene tree distribution
have the same rooted metric tree. The rooted topology is read off the gene tree classes
(`ac1_topologyOne_eq`: the shape from `|𝒞|` and `|𝒞₂|`, the labelling of `P₇` and `P₉` by the
cherries of the most probable gene tree, of `𝒞₂` and of the six most probable gene trees, and `P₄`
versus `P₈` by `Z = 1` versus `Z < 1`), and the branch lengths are solved from Table 7. -/
theorem ac1_rootings_one (τ τ' : SpeciesTree (Fin 5)) (hk : unroot τ.clusters = U5 1)
    (hk' : unroot τ'.clusters = U5 1) (h : τ.unrootedDist id = τ'.unrootedDist id) :
    τ.SameRootedMetricTree τ' := by
  -- the rooted topology, read off the classes of gene trees
  have hc : τ.clusters = τ'.clusters := by
    rw [← ac1_topologyOne_eq τ hk, ← ac1_topologyOne_eq τ' hk', ac1_topologyOne_congr h]
  -- the branch lengths, solved from Table 7
  have hu := cls_u_congr h
  have hR := classify_mem_rootings5 τ 1 (by decide) hk
  simp only [rootings5, mem_insert, mem_singleton] at hR
  rcases hR with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0
  · exact ac1_lengths_1_0 hu h0 (hc.symm.trans h0)
  · exact ac1_lengths_1_1 hu h0 (hc.symm.trans h0)
  · exact ac1_lengths_1_2 hu h0 (hc.symm.trans h0)
  · exact ac1_lengths_1_3 hu h0 (hc.symm.trans h0)
  · exact ac1_lengths_1_4 hu h0 (hc.symm.trans h0)
  · exact ac1_lengths_1_5 hu h0 (hc.symm.trans h0)
  · exact ac1_lengths_1_6 hu h0 (hc.symm.trans h0)
  · exact ac1_lengths_1_7 hu h0 (hc.symm.trans h0)

end ADR11
