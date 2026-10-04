module

public import ADR11.Coalescent.Absorption

/-!
# The unrooted gene tree produced above the root

`unrootedOutcome F T` is the probability that the population above the root of the species tree,
entered by the forest `F`, produces a gene tree with unrooted topology `T`.

## Main results

* `unrootedOutcome_of_card_roots_le_three`: if `F` covers all lineages and has at most three
  roots, its unrooted topology is already decided: all ways of completing it give `unroot F`.
* `unrootedOutcome_first_step`: first-step analysis.
* `unrootedOutcome_nonneg`, `unrootedOutcome_sum`.
* `unrootedOutcome_of_card_roots_eq_four`, `unrootedOutcome_of_card_roots_eq_five`: from four
  (five) roots covering all lineages, the outcome is the proportion of the `6` (`60`) sequences
  of merges down to three roots that produce `T`.
* `absorb_isForest_singletonForest`, `absorb_card_roots_singletonForest`,
  `absorb_lineages_singletonForest`: the forest of `n` uncoalesced lineages is a forest with `n`
  roots covering all lineages.
-/

@[expose] public section

namespace ADR11

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The probability that the population above the root, entered by the forest `F`, produces a
gene tree with unrooted topology `T`. -/
noncomputable def unrootedOutcome (F T : Finset (Finset L)) : ℝ :=
  ∑ G, if unroot G = T then kingmanAbsorption F G else 0

/-- The sides of the splits of `unroot G`: the clusters of `G` other than `univ`, and their
complements. -/
theorem absorb_mem_unroot {G : Finset (Finset L)} {A : Finset L} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := by
  unfold unroot
  simp only [mem_union, mem_erase, mem_image]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨B, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl ⟨h2, h1⟩
    · right
      rw [compl_compl]
      exact ⟨h2, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨Aᶜ, ⟨h2, h1⟩, compl_compl A⟩

/-- Adding the root cluster `univ` does not change the unrooted tree. -/
theorem absorb_unroot_insert_univ (F : Finset (Finset L)) : unroot (insert univ F) = unroot F := by
  unfold unroot
  rw [erase_insert_eq_erase]

/-- Adding a cluster that is already a side of a split does not change the unrooted tree. -/
theorem absorb_unroot_insert_of_mem {F : Finset (Finset L)} {D : Finset L} (hD : D ∈ unroot F) :
    unroot (insert D F) = unroot F := by
  rw [absorb_mem_unroot] at hD
  ext A
  rw [absorb_mem_unroot, absorb_mem_unroot, mem_insert, mem_insert]
  constructor
  · rintro (⟨h | h, hne⟩ | ⟨h | h, hne⟩)
    · subst h
      exact hD
    · exact Or.inl ⟨h, hne⟩
    · subst h
      rcases hD with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · rw [compl_compl] at h1 h2
        exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h, hne⟩
  · rintro (⟨h, hne⟩ | ⟨h, hne⟩)
    · exact Or.inl ⟨Or.inr h, hne⟩
    · exact Or.inr ⟨Or.inr h, hne⟩

omit [Fintype L] in
/-- The lineages of the forest consisting of the clusters `A` and `B`. -/
private theorem absorb_lineages_pair (A B : Finset L) : lineages {A, B} = A ∪ B := by
  simp [lineages]

/-- In a forest with exactly two roots covering all lineages, the only merge completes it by
adding the cluster `univ`. -/
theorem absorb_merges_of_card_roots_eq_two {F G : Finset (Finset L)} (hF : IsForest F)
    (hcov : lineages F = univ) (h₂ : #(roots F) = 2) (hG : G ∈ merges F) :
    G = insert univ F := by
  obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hG
  have hroots : roots F = {A, B} := by
    symm
    refine eq_of_subset_of_card_le (fun x hx => ?_) (by rw [h₂, card_pair hAB])
    rcases mem_insert.1 hx with rfl | hx
    · exact hA
    · rw [mem_singleton.1 hx]
      exact hB
  have hunion : A ∪ B = univ := by
    rw [← hcov, ← lineages_roots, hroots, absorb_lineages_pair]
  rw [hunion]

/-- In a forest with exactly three roots covering all lineages, the union of two roots is the
complement of the third, hence already a side of a split of the forest. -/
theorem absorb_union_mem_unroot {F : Finset (Finset L)} (hF : IsForest F)
    (hcov : lineages F = univ) (h₃ : #(roots F) = 3) {A B : Finset L} (hA : A ∈ roots F)
    (hB : B ∈ roots F) (hAB : A ≠ B) : A ∪ B ∈ unroot F := by
  have hcard : #(((roots F).erase A).erase B) = 1 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨hAB.symm, hB⟩), card_erase_of_mem hA, h₃]
  obtain ⟨C, hC⟩ := card_eq_one.1 hcard
  have hCmem : C ∈ ((roots F).erase A).erase B := by
    rw [hC]
    exact mem_singleton_self C
  simp only [mem_erase] at hCmem
  obtain ⟨hCB, hCA, hCr⟩ := hCmem
  have hroots : roots F = insert A {B, C} := by
    symm
    refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hA
      · exact hB
      · exact hCr
    · rw [h₃, card_insert_of_notMem, card_pair hCB.symm]
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hAB, fun h => hCA h.symm⟩
  have hunion : A ∪ (B ∪ C) = univ := by
    rw [← hcov, ← lineages_roots, hroots]
    simp [lineages]
  have hdisjA : Disjoint C A := hF.disjoint_of_mem_roots hCr hA hCA
  have hdisjB : Disjoint C B := hF.disjoint_of_mem_roots hCr hB hCB
  have hcompl : (A ∪ B)ᶜ = C := by
    ext x
    simp only [mem_compl, mem_union, not_or]
    constructor
    · rintro ⟨hxA, hxB⟩
      have hx : x ∈ A ∪ (B ∪ C) := by
        rw [hunion]
        exact mem_univ x
      simp only [mem_union] at hx
      tauto
    · intro hxC
      exact ⟨disjoint_left.1 hdisjA hxC, disjoint_left.1 hdisjB hxC⟩
  rw [absorb_mem_unroot, hcompl]
  refine Or.inr ⟨roots_subset F hCr, fun hCu => ?_⟩
  obtain ⟨a, ha⟩ := hF.1 A (roots_subset F hA)
  exact disjoint_left.1 hdisjA (by rw [hCu]; exact mem_univ a) ha

/-- From a forest with at most three roots covering all lineages, every gene tree produced above
the root has the unrooted topology of the forest. -/
theorem absorb_unroot_eq_of_kingmanAbsorption_ne_zero {F : Finset (Finset L)} (hF : IsForest F)
    (hcov : lineages F = univ) (h₁ : 1 ≤ #(roots F)) (h₃ : #(roots F) ≤ 3)
    {G : Finset (Finset L)} (hG : kingmanAbsorption F G ≠ 0) : unroot G = unroot F := by
  rw [kingmanAbsorption_apply hF, ite_eq_right (by omega)] at hG
  split_ifs at hG with hG1
  swap
  · exact absurd rfl hG
  obtain h | h | h : #(roots F) = 1 ∨ #(roots F) = 2 ∨ #(roots F) = 3 := by omega
  · rw [h, Nat.sub_self, pow_zero, Matrix.one_apply] at hG
    split_ifs at hG with hFG
    · rw [hFG]
    · exact absurd rfl hG
  · rw [h, show 2 - 1 = 1 from rfl, pow_one, jumpMatrix_apply_of_isForest (by omega)] at hG
    split_ifs at hG with hm
    · rw [absorb_merges_of_card_roots_eq_two hF hcov h hm, absorb_unroot_insert_univ]
    · exact absurd rfl hG
  · rw [h, show 3 - 1 = 1 + 1 from rfl, jumpMatrix_pow_succ_apply (by omega)] at hG
    obtain ⟨F', hF', hne⟩ := exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hG)
    obtain ⟨hF'f, hcard, -, -, hlin⟩ := hF.of_mem_merges hF'
    rw [pow_one, jumpMatrix_apply_of_isForest (by omega)] at hne
    split_ifs at hne with hm
    · rw [absorb_merges_of_card_roots_eq_two hF'f (hlin.trans hcov) (by omega) hm,
        absorb_unroot_insert_univ]
      obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hF'
      exact absorb_unroot_insert_of_mem (absorb_union_mem_unroot hF hcov h hA hB hAB)
    · exact absurd rfl hne

theorem unrootedOutcome_of_card_roots_le_three {F : Finset (Finset L)} (hF : IsForest F)
    (hcov : lineages F = univ) (h₁ : 1 ≤ #(roots F)) (h₃ : #(roots F) ≤ 3)
    (T : Finset (Finset L)) :
    unrootedOutcome F T = if unroot F = T then 1 else 0 := by
  unfold unrootedOutcome
  have h : ∀ G, (if unroot G = T then kingmanAbsorption F G else 0) =
      if unroot F = T then kingmanAbsorption F G else 0 := by
    intro G
    by_cases h0 : kingmanAbsorption F G = 0
    · simp [h0]
    · rw [absorb_unroot_eq_of_kingmanAbsorption_ne_zero hF hcov h₁ h₃ h0]
  rw [sum_congr rfl fun G _ => h G]
  split_ifs
  · exact kingmanAbsorption_sum hF
  · simp

theorem unrootedOutcome_first_step {F : Finset (Finset L)} (hF : IsForest F)
    (hk : 2 ≤ #(roots F)) (T : Finset (Finset L)) :
    unrootedOutcome F T =
      (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ * ∑ F' ∈ merges F, unrootedOutcome F' T := by
  unfold unrootedOutcome
  have h : ∀ G, (if unroot G = T then kingmanAbsorption F G else 0) =
      ∑ F' ∈ merges F, (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ *
        (if unroot G = T then kingmanAbsorption F' G else 0) := by
    intro G
    rw [kingmanAbsorption_first_step hF hk G, ← mul_sum]
    by_cases hT : unroot G = T <;> simp [hT]
  rw [sum_congr rfl fun G _ => h G, sum_comm, mul_sum]
  refine sum_congr rfl fun F' _ => ?_
  rw [mul_sum]

theorem unrootedOutcome_nonneg {F : Finset (Finset L)} (hF : IsForest F)
    (T : Finset (Finset L)) : 0 ≤ unrootedOutcome F T := by
  unfold unrootedOutcome
  refine sum_nonneg fun G _ => ?_
  split_ifs
  · exact kingmanAbsorption_nonneg hF G
  · exact le_rfl

theorem unrootedOutcome_sum {F : Finset (Finset L)} (hF : IsForest F) :
    ∑ T, unrootedOutcome F T = 1 := by
  unfold unrootedOutcome
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true]
  exact kingmanAbsorption_sum hF

/-- From a forest with four roots covering all lineages, the unrooted gene tree is decided by
the first merge: each of the `6` merges has probability `1/6`. -/
theorem unrootedOutcome_of_card_roots_eq_four {F : Finset (Finset L)} (hF : IsForest F)
    (hcov : lineages F = univ) (h₄ : #(roots F) = 4) (T : Finset (Finset L)) :
    unrootedOutcome F T = (6 : ℝ)⁻¹ * #{F' ∈ merges F | unroot F' = T} := by
  rw [unrootedOutcome_first_step hF (by omega), h₄, ← sum_boole]
  have h : ∀ F' ∈ merges F, unrootedOutcome F' T = if unroot F' = T then 1 else 0 := by
    intro F' hF'
    obtain ⟨hF'f, hcard, -, -, hlin⟩ := hF.of_mem_merges hF'
    exact unrootedOutcome_of_card_roots_le_three hF'f (hlin.trans hcov) (by omega) (by omega) T
  rw [sum_congr rfl h]
  norm_num [Nat.choose]

/-- From a forest with five roots covering all lineages, the unrooted gene tree is decided by
the first two merges: each of the `10 · 6 = 60` sequences of two merges has probability
`1/60`. -/
theorem unrootedOutcome_of_card_roots_eq_five {F : Finset (Finset L)} (hF : IsForest F)
    (hcov : lineages F = univ) (h₅ : #(roots F) = 5) (T : Finset (Finset L)) :
    unrootedOutcome F T =
      (60 : ℝ)⁻¹ * ((∑ F' ∈ merges F, #{F'' ∈ merges F' | unroot F'' = T} : ℕ) : ℝ) := by
  rw [unrootedOutcome_first_step hF (by omega), h₅]
  have h : ∀ F' ∈ merges F,
      unrootedOutcome F' T = (6 : ℝ)⁻¹ * #{F'' ∈ merges F' | unroot F'' = T} := by
    intro F' hF'
    obtain ⟨hF'f, hcard, -, -, hlin⟩ := hF.of_mem_merges hF'
    exact unrootedOutcome_of_card_roots_eq_four hF'f (hlin.trans hcov) (by omega) T
  rw [sum_congr rfl h, ← mul_sum, Nat.cast_sum, ← mul_assoc]
  norm_num [Nat.choose]

/-! ### The forest of uncoalesced lineages -/

/-- The singleton forest is a forest. -/
theorem absorb_isForest_singletonForest (n : ℕ) : IsForest (singletonForest n) := by
  refine ⟨fun A hA => ?_, fun A hA B hB => ?_⟩
  · obtain ⟨a, -, rfl⟩ := mem_image.1 hA
    exact singleton_nonempty a
  · obtain ⟨a, -, rfl⟩ := mem_image.1 hA
    obtain ⟨b, -, rfl⟩ := mem_image.1 hB
    by_cases hab : a = b
    · exact Or.inl (by rw [hab])
    · exact Or.inr (Or.inr (disjoint_singleton.2 hab))

/-- Every singleton is a root of the singleton forest. -/
theorem absorb_roots_singletonForest (n : ℕ) : roots (singletonForest n) = singletonForest n := by
  unfold roots
  refine filter_true_of_mem fun A hA B hB hAB => ?_
  obtain ⟨a, -, rfl⟩ := mem_image.1 hA
  obtain ⟨b, -, rfl⟩ := mem_image.1 hB
  rw [singleton_subset_singleton.1 hAB]

theorem absorb_card_singletonForest (n : ℕ) : #(singletonForest n) = n := by
  unfold singletonForest
  rw [card_image_of_injective _ singleton_injective, card_univ, Fintype.card_fin]

theorem absorb_card_roots_singletonForest (n : ℕ) : #(roots (singletonForest n)) = n := by
  rw [absorb_roots_singletonForest, absorb_card_singletonForest]

theorem absorb_lineages_singletonForest (n : ℕ) : lineages (singletonForest n) = univ := by
  refine eq_univ_of_forall fun a => ?_
  unfold lineages singletonForest
  exact mem_sup.2 ⟨{a}, mem_image_of_mem _ (mem_univ a), mem_singleton_self a⟩

end ADR11
