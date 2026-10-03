module

public import ADR11.SmallTrees
public import ADR11.Coalescent.Outcome

/-!
# Lemma 4: all coalescences above the root

If the five lineages of a 5-taxon species tree all enter the population above the root without
having coalesced, then the unrooted gene tree is uniformly distributed on the 15 unrooted gene
trees. The paper remarks that this is special to five taxa; `lemma4_six` shows that it fails for
six lineages.

## Proof

By first-step analysis (`unrootedOutcome_first_step`), and since the unrooted topology of a
forest with three roots covering all lineages is already decided
(`unrootedOutcome_of_card_roots_le_three`), the probability of `T` starting from `n` singletons
is the proportion of the sequences of `n - 3` merges that produce a forest with unrooted topology
`T`: there are `10 · 6 = 60` such sequences for `n = 5` and `15 · 10 · 6 = 900` for `n = 6`. The
numbers of sequences producing each tree are computed by `decide`: `4` for each `T_i`, and `12`
for the tree with three cherries against `8` for the unrooted caterpillar on six lineages.
-/

@[expose] public section

namespace ADR11

open Finset

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

/-- Each of the 15 unrooted 5-taxon trees is produced by exactly `4` of the `60` sequences of two
merges starting from five singletons. -/
private theorem absorb_count_five : ∀ i ∈ Icc 1 15,
    (∑ F' ∈ merges (singletonForest 5), #{F'' ∈ merges F' | unroot F'' = T5 i}) = 4 := by
  decide +kernel

/-- Among the `900` sequences of three merges starting from six singletons, `12` produce the
unrooted tree with the three cherries `AB`, `CD`, `EF` and `8` produce the unrooted caterpillar
`((A,B),C,D,(E,F))` (both counts in one pass). -/
private theorem absorb_count_six :
    (∑ F₁ ∈ merges (singletonForest 6), ∑ F₂ ∈ merges F₁, ∑ F₃ ∈ merges F₂,
      ((if unroot F₃ = treeOfClusters {{0, 1}, {2, 3}, {4, 5}} then 1 else 0 : ℕ),
        (if unroot F₃ = treeOfClusters {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}} then 1 else 0 : ℕ))) =
      (12, 8) := by
  decide +kernel

/-- **Lemma 4.** If all coalescent events occur above the root of a 5-taxon species tree, all 15
unrooted topological gene trees are equally likely: starting from five uncoalesced lineages, the
population above the root produces each `T_i` with probability `1/15`. -/
theorem lemma4 (i : ℕ) (hi : i ∈ Icc 1 15) :
    ∑ G, (if unroot G = T5 i then kingmanAbsorption (singletonForest 5) G else 0) = 1 / 15 := by
  change unrootedOutcome (singletonForest 5) (T5 i) = 1 / 15
  rw [unrootedOutcome_of_card_roots_eq_five (absorb_isForest_singletonForest 5)
    (absorb_lineages_singletonForest 5) (absorb_card_roots_singletonForest 5),
    absorb_count_five i hi]
  norm_num

/-- `lemma4` in terms of `unrootedOutcome`. -/
theorem unrootedOutcome_singletonForest_five (i : ℕ) (hi : i ∈ Icc 1 15) :
    unrootedOutcome (singletonForest 5) (T5 i) = 1 / 15 :=
  lemma4 i hi

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
