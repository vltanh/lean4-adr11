module

public import ADR11.SmallTrees
public import ADR11.Coalescent.Outcome
public import ADR11.MSC.Relabel

/-!
# Lemma 4: all coalescences above the root

If the five lineages of a 5-taxon species tree all enter the population above the root without
having coalesced, then the unrooted gene tree is uniformly distributed on the 15 unrooted gene
trees. The paper remarks that this is special to five taxa; `lemma4_six` shows that it fails for
six lineages.

## Main results

* `lemma4` (`lem:aboveroot`), and `unrootedOutcome_singletonForest_five`, the same statement in
  terms of `unrootedOutcome`.
* `lemma4_six`: the remark after Lemma 4, for six lineages.
* `f1_unrootedOutcome_relabelFamily`: from `n` uncoalesced lineages, relabelling the lineages
  does not change the probability of an unrooted gene tree.
* `f1_relabelFamily_perm_T5`: the 15 unrooted gene trees `T_i` have the same unlabelled shape:
  each is the image of `T_1` under an explicit permutation of the lineages.
* `f1_sum_unrootedOutcome_T5`: the probabilities of the 15 trees `T_i` add up to `1`.

## Proof of Lemma 4 (the paper's)

Above the root, regardless of the species tree, five labelled lineages enter the ancestral
population and coalesce: the unrooted gene tree `T` has the probability
`unrootedOutcome (singletonForest 5) T` (Kingman's coalescent run for an infinite time).
(a) Kingman's coalescent is invariant under relabelling the lineages
(`kingmanAbsorption_relabelFamily`), and a permutation of the lineages fixes the forest of the
five uncoalesced lineages, so relabelling the lineages of `T` does not change its probability.
(b) All unrooted gene trees have the same unlabelled shape: `T_i = π_i(T_1)` for a permutation
`π_i`, so all 15 probabilities are equal. (c) The 15 trees `T_i` of Table 5 are distinct and are
all the unrooted gene trees on five lineages, so their probabilities add up to `1`, and each is
`1/15`.

## The six-taxon remark

By first-step analysis (`unrootedOutcome_first_step`), and since the unrooted topology of a
forest with three roots covering all lineages is already decided
(`unrootedOutcome_of_card_roots_le_three`), the probability of `T` starting from six singletons
is the proportion of the `15 · 10 · 6 = 900` sequences of three merges that produce a forest with
unrooted topology `T`. The numbers of sequences producing the tree with three cherries and the
unrooted caterpillar on six lineages are computed by `decide`, separately for each of the `15`
first merges: `12` against `8`.
-/

@[expose] public section

namespace ADR11

open Finset

/-! ### (a) Relabelling the lineages -/

/-- A permutation of the lineages fixes the forest of uncoalesced lineages. -/
theorem f1_relabelFamily_singletonForest {n : ℕ} (π : Equiv.Perm (Fin n)) :
    relabelFamily π (singletonForest n) = singletonForest n := by
  unfold relabelFamily singletonForest
  rw [image_image]
  ext A
  simp only [mem_image, mem_univ, true_and, Function.comp_apply, Finset.map_singleton,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨π l, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨π.symm l, by rw [Equiv.apply_symm_apply]⟩

/-- Lemma 4, step (a): Kingman's coalescent run for an infinite time from `n` uncoalesced
lineages is invariant under relabelling the lineages, so relabelling an unrooted gene tree does
not change its probability: the coalescent histories producing `T` correspond, by relabelling the
lineages along `π`, to equally likely histories producing `π(T)`. -/
theorem f1_unrootedOutcome_relabelFamily {n : ℕ} (π : Equiv.Perm (Fin n))
    (T : Finset (Finset (Fin n))) :
    unrootedOutcome (singletonForest n) (relabelFamily π T) =
      unrootedOutcome (singletonForest n) T := by
  unfold unrootedOutcome
  rw [← Equiv.sum_comp (relabelFamilyEquiv π)]
  refine sum_congr rfl fun G _ => ?_
  have hK := kingmanAbsorption_relabelFamily π (singletonForest n) G
  rw [f1_relabelFamily_singletonForest] at hK
  rw [relabelFamilyEquiv_apply, unroot_relabelFamily]
  exact if_congr (relabelFamily_injective π).eq_iff hK rfl

/-! ### (b) The 15 unrooted gene trees have the same unlabelled shape -/

/-- The permutation of the lineages `A, B, C, D, E` with images `f 0, …, f 4`. -/
noncomputable def f1_perm5 (f : Fin 5 → Fin 5) (hf : Function.Bijective f) :
    Equiv.Perm (Fin 5) :=
  Equiv.ofBijective f hf

/-- Lemma 4, step (b): all unrooted 5-taxon gene trees have the same unlabelled shape. The tree
`T_1` has the cherries `AB`, `DE` and the middle lineage `C`; the tree `T_i` with the cherries
`PQ`, `RS` and the middle lineage `M` is the image of `T_1` under the permutation
`A, B, C, D, E ↦ P, Q, M, R, S`. -/
theorem f1_relabelFamily_perm_T5 :
    ∀ i ∈ Icc 1 15, ∃ π : Equiv.Perm (Fin 5), relabelFamily π (T5 1) = T5 i := by
  intro i hi
  rw [mem_Icc] at hi
  obtain ⟨h1, h15⟩ := hi
  interval_cases i
  · exact ⟨f1_perm5 ![0, 1, 2, 3, 4] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![0, 1, 3, 2, 4] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![0, 1, 4, 2, 3] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![0, 2, 1, 3, 4] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![0, 2, 3, 1, 4] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![0, 2, 4, 1, 3] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![0, 3, 1, 2, 4] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![0, 3, 2, 1, 4] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![0, 3, 4, 1, 2] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![0, 4, 1, 2, 3] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![0, 4, 2, 1, 3] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![0, 4, 3, 1, 2] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![1, 2, 0, 3, 4] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![1, 3, 0, 2, 4] (by decide), by decide⟩
  · exact ⟨f1_perm5 ![1, 4, 0, 2, 3] (by decide), by decide⟩

/-! ### (c) The probabilities of the 15 trees add up to one -/

/-- The 15 trees `T_i` of Table 5 are distinct. -/
private theorem f1_T5_injective : ∀ i ∈ Icc 1 15, ∀ j ∈ Icc 1 15, T5 i = T5 j → i = j := by
  decide

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
set_option synthInstance.maxSize 1000 in
/-- The unrooted gene trees on five lineages are the 15 trees `T_i` of Table 5: from five
uncoalesced lineages, every forest reached by two merges, which has three roots and so decides
the unrooted gene tree, has the unrooted topology of some `T_i`. -/
private theorem f1_unroot_mem_T5 : ∀ F' ∈ merges (singletonForest 5), ∀ F'' ∈ merges F',
    ∃ i ∈ Icc 1 15, unroot F'' = T5 i := by
  decide +kernel

/-- Lemma 4, step (c): from five uncoalesced lineages, the probabilities of the 15 unrooted gene
trees `T_i` add up to `1`, since these are all the unrooted gene trees on five lineages. -/
theorem f1_sum_unrootedOutcome_T5 :
    ∑ i ∈ Icc 1 15, unrootedOutcome (singletonForest 5) (T5 i) = 1 := by
  have hF := absorb_isForest_singletonForest 5
  have himage : ∑ T ∈ (Icc 1 15).image T5, unrootedOutcome (singletonForest 5) T =
      ∑ i ∈ Icc 1 15, unrootedOutcome (singletonForest 5) (T5 i) :=
    sum_image fun i hi j hj h => f1_T5_injective i hi j hj h
  rw [← himage, ← unrootedOutcome_sum hF]
  refine sum_subset (subset_univ ((Icc 1 15).image T5)) fun T _ hT => ?_
  -- an unrooted tree other than the `T_i` has probability `0`
  rw [unrootedOutcome_of_card_roots_eq_five hF (absorb_lineages_singletonForest 5)
    (absorb_card_roots_singletonForest 5)]
  have h0 : ∀ F' ∈ merges (singletonForest 5), #{F'' ∈ merges F' | unroot F'' = T} = 0 := by
    intro F' hF'
    rw [card_eq_zero, filter_eq_empty_iff]
    intro F'' hF'' hT''
    obtain ⟨i, hi, hi'⟩ := f1_unroot_mem_T5 F' hF' F'' hF''
    exact hT (mem_image.2 ⟨i, hi, hi'.symm.trans hT''⟩)
  rw [sum_congr rfl h0, sum_const_zero, Nat.cast_zero, mul_zero]

/-! ### Lemma 4 -/

/-- **Lemma 4** (`lem:aboveroot`). If all coalescent events occur above the root of a 5-taxon species tree, all 15
unrooted topological gene trees are equally likely: starting from five uncoalesced lineages, the
population above the root produces each `T_i` with probability `1/15`.

Proof (the paper's): relabelling the lineages does not change the probabilities (step (a),
`f1_unrootedOutcome_relabelFamily`), and all unrooted gene trees have the same unlabelled shape
(step (b), `f1_relabelFamily_perm_T5`), so the 15 probabilities are equal; they add up to `1`
(step (c), `f1_sum_unrootedOutcome_T5`). -/
theorem lemma4 (i : ℕ) (hi : i ∈ Icc 1 15) :
    ∑ G, (if unroot G = T5 i then kingmanAbsorption (singletonForest 5) G else 0) = 1 / 15 := by
  change unrootedOutcome (singletonForest 5) (T5 i) = 1 / 15
  -- (a), (b): every `T_j` is as likely as `T_1`
  have heq : ∀ j ∈ Icc 1 15, unrootedOutcome (singletonForest 5) (T5 j) =
      unrootedOutcome (singletonForest 5) (T5 1) := by
    intro j hj
    obtain ⟨π, hπ⟩ := f1_relabelFamily_perm_T5 j hj
    rw [← hπ, f1_unrootedOutcome_relabelFamily]
  -- (c): the 15 equal probabilities add up to `1`
  have hsum := f1_sum_unrootedOutcome_T5
  rw [sum_congr rfl heq, sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
  rw [heq i hi]
  norm_num at hsum ⊢
  linarith

/-- `lemma4` in terms of `unrootedOutcome`. -/
theorem unrootedOutcome_singletonForest_five (i : ℕ) (hi : i ∈ Icc 1 15) :
    unrootedOutcome (singletonForest 5) (T5 i) = 1 / 15 :=
  lemma4 i hi

/-! ### Six lineages -/

/-- From a forest with six roots covering all lineages, the unrooted gene tree is decided by the
first three merges: each of the `15 · 10 · 6 = 900` sequences of three merges has probability
`1/900`. -/
theorem absorb_unrootedOutcome_of_card_roots_eq_six {L : Type*} [Fintype L] [DecidableEq L]
    {F : Finset (Finset L)} (hF : IsForest F) (hcov : lineages F = univ) (h₆ : #(roots F) = 6)
    (T : Finset (Finset L)) :
    unrootedOutcome F T =
      (900 : ℝ)⁻¹ * ((∑ F₁ ∈ merges F, ∑ F₂ ∈ merges F₁,
        #{F₃ ∈ merges F₂ | unroot F₃ = T} : ℕ) : ℝ) := by
  rw [unrootedOutcome_first_step hF (by omega), h₆]
  have h : ∀ F₁ ∈ merges F, unrootedOutcome F₁ T =
      (60 : ℝ)⁻¹ * ((∑ F₂ ∈ merges F₁, #{F₃ ∈ merges F₂ | unroot F₃ = T} : ℕ) : ℝ) := by
    intro F₁ hF₁
    obtain ⟨hF₁f, hcard, -, -, hlin⟩ := hF.of_mem_merges hF₁
    exact unrootedOutcome_of_card_roots_eq_five hF₁f (hlin.trans hcov) (by omega) T
  rw [sum_congr rfl h, ← mul_sum, Nat.cast_sum, ← mul_assoc]
  norm_num [Nat.choose]

/-- The two counts of `absorb_count_six` among the sequences of merges that start with the
forest `F₁`: the sequences of two merges from `F₁` producing the unrooted tree with the three
cherries `AB`, `CD`, `EF`, and those producing the unrooted caterpillar `((A,B),C,D,(E,F))`. -/
private def f1_counts6 (F₁ : Finset (Finset (Fin 6))) : ℕ × ℕ :=
  ∑ F₂ ∈ merges F₁, ∑ F₃ ∈ merges F₂,
    ((if unroot F₃ = treeOfClusters {{0, 1}, {2, 3}, {4, 5}} then 1 else 0 : ℕ),
      (if unroot F₃ = treeOfClusters {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}} then 1 else 0 : ℕ))

/-- The `15` forests reached from six singletons by one merge. -/
private theorem f1_merges_six : merges (singletonForest 6) =
    {insert {0, 1} (singletonForest 6), insert {0, 2} (singletonForest 6),
     insert {0, 3} (singletonForest 6), insert {0, 4} (singletonForest 6),
     insert {0, 5} (singletonForest 6), insert {1, 2} (singletonForest 6),
     insert {1, 3} (singletonForest 6), insert {1, 4} (singletonForest 6),
     insert {1, 5} (singletonForest 6), insert {2, 3} (singletonForest 6),
     insert {2, 4} (singletonForest 6), insert {2, 5} (singletonForest 6),
     insert {3, 4} (singletonForest 6), insert {3, 5} (singletonForest 6),
     insert {4, 5} (singletonForest 6)} := by
  decide +kernel

/-! The counts of `absorb_count_six` by first merge, one computation each (computing them in one
pass needs several gigabytes of memory more). -/

private theorem f1_counts6_01 :
    f1_counts6 (insert {0, 1} (singletonForest 6)) = (4, 4) := by
  decide +kernel

private theorem f1_counts6_02 :
    f1_counts6 (insert {0, 2} (singletonForest 6)) = (0, 0) := by
  decide +kernel

private theorem f1_counts6_03 :
    f1_counts6 (insert {0, 3} (singletonForest 6)) = (0, 0) := by
  decide +kernel

private theorem f1_counts6_04 :
    f1_counts6 (insert {0, 4} (singletonForest 6)) = (0, 0) := by
  decide +kernel

private theorem f1_counts6_05 :
    f1_counts6 (insert {0, 5} (singletonForest 6)) = (0, 0) := by
  decide +kernel

private theorem f1_counts6_12 :
    f1_counts6 (insert {1, 2} (singletonForest 6)) = (0, 0) := by
  decide +kernel

private theorem f1_counts6_13 :
    f1_counts6 (insert {1, 3} (singletonForest 6)) = (0, 0) := by
  decide +kernel

private theorem f1_counts6_14 :
    f1_counts6 (insert {1, 4} (singletonForest 6)) = (0, 0) := by
  decide +kernel

private theorem f1_counts6_15 :
    f1_counts6 (insert {1, 5} (singletonForest 6)) = (0, 0) := by
  decide +kernel

private theorem f1_counts6_23 :
    f1_counts6 (insert {2, 3} (singletonForest 6)) = (4, 0) := by
  decide +kernel

private theorem f1_counts6_24 :
    f1_counts6 (insert {2, 4} (singletonForest 6)) = (0, 0) := by
  decide +kernel

private theorem f1_counts6_25 :
    f1_counts6 (insert {2, 5} (singletonForest 6)) = (0, 0) := by
  decide +kernel

private theorem f1_counts6_34 :
    f1_counts6 (insert {3, 4} (singletonForest 6)) = (0, 0) := by
  decide +kernel

private theorem f1_counts6_35 :
    f1_counts6 (insert {3, 5} (singletonForest 6)) = (0, 0) := by
  decide +kernel

private theorem f1_counts6_45 :
    f1_counts6 (insert {4, 5} (singletonForest 6)) = (4, 4) := by
  decide +kernel

/-- Among the `900` sequences of three merges starting from six singletons, `12` produce the
unrooted tree with the three cherries `AB`, `CD`, `EF` and `8` produce the unrooted caterpillar
`((A,B),C,D,(E,F))` (both counts in one pass). The counts are computed for each of the `15` first
merges separately (`f1_counts6_01`, …, `f1_counts6_45`). -/
private theorem absorb_count_six :
    (∑ F₁ ∈ merges (singletonForest 6), ∑ F₂ ∈ merges F₁, ∑ F₃ ∈ merges F₂,
      ((if unroot F₃ = treeOfClusters {{0, 1}, {2, 3}, {4, 5}} then 1 else 0 : ℕ),
        (if unroot F₃ = treeOfClusters {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}} then 1 else 0 : ℕ))) =
      (12, 8) := by
  change ∑ F₁ ∈ merges (singletonForest 6), f1_counts6 F₁ = (12, 8)
  rw [f1_merges_six, sum_insert, sum_insert, sum_insert, sum_insert, sum_insert, sum_insert,
    sum_insert, sum_insert, sum_insert, sum_insert, sum_insert, sum_insert, sum_insert, sum_insert,
    sum_singleton, f1_counts6_01, f1_counts6_02, f1_counts6_03, f1_counts6_04, f1_counts6_05,
    f1_counts6_12, f1_counts6_13, f1_counts6_14, f1_counts6_15, f1_counts6_23,
    f1_counts6_24, f1_counts6_25, f1_counts6_34, f1_counts6_35, f1_counts6_45]
  · rfl
  -- the `15` forests are distinct
  all_goals decide

/-- The remark after Lemma 4: for six taxa the analogous statement is false. Starting from six
uncoalesced lineages, the unrooted gene tree with the three cherries `AB`, `CD`, `EF` and the
unrooted caterpillar `((A,B),C,D,(E,F))` (splits `AB|CDEF`, `ABC|DEF`, `ABCD|EF`) have different
probabilities. -/
theorem lemma4_six :
    ∑ G, (if unroot G = treeOfClusters {{0, 1}, {2, 3}, {4, 5}}
        then kingmanAbsorption (singletonForest 6) G else 0) ≠
      ∑ G, (if unroot G = treeOfClusters {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}
        then kingmanAbsorption (singletonForest 6) G else 0) := by
  have key : ∀ T : Finset (Finset (Fin 6)),
      ∑ G, (if unroot G = T then kingmanAbsorption (singletonForest 6) G else 0) =
        (900 : ℝ)⁻¹ * ((∑ F₁ ∈ merges (singletonForest 6), ∑ F₂ ∈ merges F₁,
          #{F₃ ∈ merges F₂ | unroot F₃ = T} : ℕ) : ℝ) :=
    absorb_unrootedOutcome_of_card_roots_eq_six (absorb_isForest_singletonForest 6)
      (absorb_lineages_singletonForest 6) (absorb_card_roots_singletonForest 6)
  have h₁ := congrArg Prod.fst absorb_count_six
  have h₂ := congrArg Prod.snd absorb_count_six
  simp only [Prod.fst_sum, Prod.snd_sum] at h₁ h₂
  rw [key, key]
  simp only [card_filter]
  rw [h₁, h₂]
  norm_num

end ADR11
