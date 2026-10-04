module

public import ADR11.MSC.Basic

/-!
# Marginalization

The paper's Lemma 5 is "clear from the structure of the coalescent model". It combines two facts:

* *Dropping lineages* (`forestDist_comp_embedding`): the forest formed by a subset of the lineages
  is distributed as the multispecies coalescent of that subset. Kingman's coalescent is
  consistent: restricting a forest to a subset of the lineages lumps the chain into Kingman's
  coalescent on the subset (`kingmanTransition_lump`, `kingmanAbsorption_lump`).
* *Pruning the species tree* (`rootedDist_restrict`): when only taxa in `S` are sampled, the
  populations without lineages do nothing, populations in a chain with the same lineages merge
  into one population whose length is the sum (`kingmanTransition_add`), and the populations above
  the most recent common ancestor of `S` merge into the population above the root.

* `restrictForest e F`: the restriction of a forest on `L` to the lineages `L'`, along an
  embedding `e : L' ↪ L`.
* `restrictUnrooted e T`: the restriction of an unrooted tree (given by the sides of its splits)
  to the lineages `L'`.

## Main results

* `kingmanTransition_lump`, `kingmanAbsorption_lump`: lumpability of Kingman's coalescent. The
  generators intertwine, `Q M = M Q'` on the rows of forests, where `M` is the restriction map:
  merging two roots that both meet the range of `e` merges their traces, and the other merges do
  not change the restriction.
* `forestDist_comp_embedding`, `SpeciesTree.rootedDist_comp_embedding`,
  `SpeciesTree.unrootedDist_comp_embedding`: dropping lineages.
* `SpeciesTree.rootedDist_restrict`: pruning the species tree. It is proved by strong induction
  on the clusters `A ≠ univ` meeting `S`: the forest leaving `A` is the forest entering the trace
  `A ∩ S` in `σ(S)`, evolved for the sum of the lengths of the clusters `A' ⊆ A` with the same
  trace (a chain).
* `unroot_restrictForest`: unrooting commutes with restricting (for any family of clusters).
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {L : Type*} [Fintype L] [DecidableEq L] {L' : Type*} [Fintype L'] [DecidableEq L']

/-- The restriction of a forest on `L` to the lineages `L'`, along an embedding `e : L' ↪ L`: the
nonempty traces of its clusters. -/
def restrictForest (e : L' ↪ L) (F : Finset (Finset L)) : Finset (Finset L') :=
  (F.filter fun A => ∃ l, e l ∈ A).image fun A => univ.filter fun l => e l ∈ A

/-! ### Restricting forests -/

omit [Fintype L] in
private theorem marg_mem_restrictForest (e : L' ↪ L) {F : Finset (Finset L)} {D : Finset L'} :
    D ∈ restrictForest e F ↔ ∃ A ∈ F, (∃ l, e l ∈ A) ∧ (univ.filter fun l => e l ∈ A) = D := by
  unfold restrictForest
  simp only [mem_image, mem_filter, and_assoc]

omit [Fintype L] in
private theorem marg_tr_mem_restrictForest (e : L' ↪ L) {F : Finset (Finset L)} {A : Finset L}
    (hA : A ∈ F) (hmeet : ∃ l, e l ∈ A) :
    (univ.filter fun l => e l ∈ A) ∈ restrictForest e F :=
  (marg_mem_restrictForest e).2 ⟨A, hA, hmeet, rfl⟩

omit [Fintype L] [DecidableEq L'] in
private theorem marg_tr_mono (e : L' ↪ L) {A B : Finset L} (h : A ⊆ B) :
    (univ.filter fun l => e l ∈ A) ⊆ univ.filter fun l => e l ∈ B :=
  fun l hl => mem_filter.2 ⟨mem_univ l, h (mem_filter.1 hl).2⟩

omit [Fintype L] [DecidableEq L'] in
private theorem marg_tr_disjoint (e : L' ↪ L) {A B : Finset L} (h : Disjoint A B) :
    Disjoint (univ.filter fun l => e l ∈ A) (univ.filter fun l => e l ∈ B) :=
  disjoint_left.2 fun _ hlA hlB => disjoint_left.1 h (mem_filter.1 hlA).2 (mem_filter.1 hlB).2

omit [Fintype L] in
private theorem marg_tr_union (e : L' ↪ L) (A B : Finset L) :
    (univ.filter fun l => e l ∈ A ∪ B) =
      (univ.filter fun l => e l ∈ A) ∪ univ.filter fun l => e l ∈ B := by
  ext l
  simp

omit [Fintype L] [DecidableEq L'] in
private theorem marg_tr_eq_empty (e : L' ↪ L) {A : Finset L} (h : ¬ ∃ l, e l ∈ A) :
    (univ.filter fun l => e l ∈ A) = ∅ := by
  ext l
  simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
  exact fun hl => h ⟨l, hl⟩

theorem IsForest.restrictForest {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) :
    IsForest (restrictForest e F) := by
  refine ⟨fun D hD => ?_, fun D hD D' hD' => ?_⟩
  · obtain ⟨A, -, ⟨l, hl⟩, rfl⟩ := (marg_mem_restrictForest e).1 hD
    exact ⟨l, mem_filter.2 ⟨mem_univ l, hl⟩⟩
  · obtain ⟨A, hA, -, rfl⟩ := (marg_mem_restrictForest e).1 hD
    obtain ⟨B, hB, -, rfl⟩ := (marg_mem_restrictForest e).1 hD'
    rcases hF.2 A hA B hB with h | h | h
    · exact Or.inl (marg_tr_mono e h)
    · exact Or.inr (Or.inl (marg_tr_mono e h))
    · exact Or.inr (Or.inr (marg_tr_disjoint e h))

omit [Fintype L] in
private theorem marg_restrictForest_insert (e : L' ↪ L) (C : Finset L) (F : Finset (Finset L)) :
    restrictForest e (insert C F) =
      if ∃ l, e l ∈ C then insert (univ.filter fun l => e l ∈ C) (restrictForest e F)
      else restrictForest e F := by
  unfold restrictForest
  rw [filter_insert]
  split_ifs <;> simp [image_insert]

omit [Fintype L'] [DecidableEq L'] in
/-- Two roots of a forest whose traces share a lineage are equal. -/
private theorem marg_eq_of_tr {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) {l : L'} (hlA : e l ∈ A)
    (hlB : e l ∈ B) : A = B :=
  hF.eq_of_mem_roots_of_mem hA hB hlA hlB

omit [DecidableEq L'] in
/-- The trace is injective on the roots meeting the range of `e`. -/
private theorem marg_tr_inj {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hmeet : ∃ l, e l ∈ A)
    (h : (univ.filter fun l => e l ∈ A) = univ.filter fun l => e l ∈ B) : A = B := by
  obtain ⟨l, hl⟩ := hmeet
  have hlB : l ∈ univ.filter fun l => e l ∈ B := h ▸ mem_filter.2 ⟨mem_univ l, hl⟩
  exact marg_eq_of_tr hF e hA hB hl (mem_filter.1 hlB).2

/-- The roots of the restriction of a forest are the traces of its roots meeting the range. -/
private theorem marg_mem_roots_restrictForest {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) {D : Finset L'} :
    D ∈ roots (restrictForest e F) ↔
      ∃ A ∈ roots F, (∃ l, e l ∈ A) ∧ (univ.filter fun l => e l ∈ A) = D := by
  constructor
  · intro hD
    obtain ⟨hDF, hmax⟩ := mem_roots.1 hD
    obtain ⟨A, hA, hmeet, rfl⟩ := (marg_mem_restrictForest e).1 hDF
    obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
    obtain ⟨l, hl⟩ := hmeet
    have hRmeet : ∃ l, e l ∈ R := ⟨l, hAR hl⟩
    refine ⟨R, hR, hRmeet, ?_⟩
    exact hmax _ (marg_tr_mem_restrictForest e (roots_subset F hR) hRmeet) (marg_tr_mono e hAR)
  · rintro ⟨A, hA, hmeet, rfl⟩
    refine mem_roots.2 ⟨marg_tr_mem_restrictForest e (roots_subset F hA) hmeet, fun D hD hAD => ?_⟩
    obtain ⟨B, hB, hBmeet, rfl⟩ := (marg_mem_restrictForest e).1 hD
    obtain ⟨R, hR, hBR⟩ := exists_mem_roots_subset hB
    obtain ⟨l, hl⟩ := hmeet
    have hlB : e l ∈ B := (mem_filter.1 (hAD (mem_filter.2 ⟨mem_univ l, hl⟩))).2
    have hAR : A = R := marg_eq_of_tr hF e hA hR hl (hBR hlB)
    subst hAR
    exact subset_antisymm (marg_tr_mono e hBR) hAD

/-- The restriction of a merge: merging two roots that both meet the range of `e` merges their
traces; otherwise the restriction does not change. -/
private theorem marg_restrictForest_merge {F : Finset (Finset L)} (e : L' ↪ L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) :
    restrictForest e (insert (A ∪ B) F) =
      if (∃ l, e l ∈ A) ∧ (∃ l, e l ∈ B) then
        insert ((univ.filter fun l => e l ∈ A) ∪ univ.filter fun l => e l ∈ B)
          (restrictForest e F)
      else restrictForest e F := by
  rw [marg_restrictForest_insert, marg_tr_union]
  by_cases hAm : ∃ l, e l ∈ A <;> by_cases hBm : ∃ l, e l ∈ B
  · have hU : ∃ l, e l ∈ A ∪ B := let ⟨l, hl⟩ := hAm; ⟨l, mem_union_left _ hl⟩
    rw [ite_eq_left hU, ite_eq_left ⟨hAm, hBm⟩]
  · have hU : ∃ l, e l ∈ A ∪ B := let ⟨l, hl⟩ := hAm; ⟨l, mem_union_left _ hl⟩
    rw [ite_eq_left hU, ite_eq_right (fun h => hBm h.2), marg_tr_eq_empty e hBm, union_empty]
    exact insert_eq_of_mem (marg_tr_mem_restrictForest e (roots_subset F hA) hAm)
  · have hU : ∃ l, e l ∈ A ∪ B := let ⟨l, hl⟩ := hBm; ⟨l, mem_union_right _ hl⟩
    rw [ite_eq_left hU, ite_eq_right (fun h => hAm h.1), marg_tr_eq_empty e hAm, empty_union]
    exact insert_eq_of_mem (marg_tr_mem_restrictForest e (roots_subset F hB) hBm)
  · have hU : ¬ ∃ l, e l ∈ A ∪ B := by
      rintro ⟨l, hl⟩
      rcases mem_union.1 hl with h | h
      · exact hAm ⟨l, h⟩
      · exact hBm ⟨l, h⟩
    rw [ite_eq_right hU, ite_eq_right (fun h => hAm h.1)]


/-- The merges of `F` whose restriction differs from the restriction of `F`: the merges of two
roots that both meet the range of `e`. -/
private theorem marg_mem_merges_ne {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    {H : Finset (Finset L)} :
    (H ∈ merges F ∧ restrictForest e H ≠ restrictForest e F) ↔
      ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ (∃ l, e l ∈ A) ∧ (∃ l, e l ∈ B) ∧
        H = insert (A ∪ B) F := by
  constructor
  · rintro ⟨hH, hne⟩
    obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hH
    rw [marg_restrictForest_merge e hA hB] at hne
    by_cases h : (∃ l, e l ∈ A) ∧ (∃ l, e l ∈ B)
    · exact ⟨A, hA, B, hB, hAB, h.1, h.2, rfl⟩
    · rw [ite_eq_right h] at hne
      exact absurd rfl hne
  · rintro ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩
    refine ⟨mem_merges.2 ⟨A, hA, B, hB, hAB, rfl⟩, ?_⟩
    rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
    intro h
    have hrA := (marg_mem_roots_restrictForest hF e).2 ⟨A, hA, hAm, rfl⟩
    have hrB := (marg_mem_roots_restrictForest hF e).2 ⟨B, hB, hBm, rfl⟩
    have hne : (univ.filter fun l => e l ∈ A) ≠ univ.filter fun l => e l ∈ B :=
      fun h' => hAB (marg_tr_inj hF e hA hB hAm h')
    exact union_not_mem_of_mem_roots hrA hrB hne (h ▸ mem_insert_self _ _)

/-- The key count behind lumpability: summing a function of the restriction over the merges of
`F` gives the sum over the merges of the restriction, plus the merges that do not change the
restriction. -/
private theorem marg_sum_merges {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    (u : Finset (Finset L') → ℝ) :
    -((#(roots F)).choose 2 : ℝ) * u (restrictForest e F) +
        ∑ H ∈ merges F, u (restrictForest e H) =
      -((#(roots (restrictForest e F))).choose 2 : ℝ) * u (restrictForest e F) +
        ∑ H' ∈ merges (restrictForest e F), u H' := by
  set rF := restrictForest e F with hrF
  have hrFf : IsForest rF := hF.restrictForest e
  set M₂ := (merges F).filter fun H => restrictForest e H ≠ rF with hM₂
  -- the restriction maps `M₂` onto the merges of `rF`
  have himage : M₂.image (restrictForest e) = merges rF := by
    ext H'
    rw [mem_image]
    constructor
    · rintro ⟨H, hH, rfl⟩
      obtain ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩ :=
        (marg_mem_merges_ne hF e).1 (mem_filter.1 hH)
      rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
      exact mem_merges.2 ⟨_, (marg_mem_roots_restrictForest hF e).2 ⟨A, hA, hAm, rfl⟩, _,
        (marg_mem_roots_restrictForest hF e).2 ⟨B, hB, hBm, rfl⟩,
        fun h' => hAB (marg_tr_inj hF e hA hB hAm h'), rfl⟩
    · intro hH'
      obtain ⟨A', hA', B', hB', hAB', rfl⟩ := mem_merges.1 hH'
      obtain ⟨A, hA, hAm, rfl⟩ := (marg_mem_roots_restrictForest hF e).1 hA'
      obtain ⟨B, hB, hBm, rfl⟩ := (marg_mem_roots_restrictForest hF e).1 hB'
      have hAB : A ≠ B := by
        rintro rfl
        exact hAB' rfl
      refine ⟨insert (A ∪ B) F, mem_filter.2 ((marg_mem_merges_ne hF e).2
        ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩), ?_⟩
      rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
  -- and is injective on `M₂`
  have hinj : Set.InjOn (restrictForest e) (M₂ : Set (Finset (Finset L))) := by
    intro H₁ hH₁ H₂ hH₂ h12
    obtain ⟨A₁, hA₁, B₁, hB₁, hAB₁, hA₁m, hB₁m, rfl⟩ :=
      (marg_mem_merges_ne hF e).1 (mem_filter.1 (mem_coe.1 hH₁))
    obtain ⟨A₂, hA₂, B₂, hB₂, hAB₂, hA₂m, hB₂m, rfl⟩ :=
      (marg_mem_merges_ne hF e).1 (mem_filter.1 (mem_coe.1 hH₂))
    rw [marg_restrictForest_merge e hA₁ hB₁, ite_eq_left ⟨hA₁m, hB₁m⟩,
      marg_restrictForest_merge e hA₂ hB₂, ite_eq_left ⟨hA₂m, hB₂m⟩] at h12
    have hr := fun {A} (hA : A ∈ roots F) (hAm : ∃ l, e l ∈ A) =>
      (marg_mem_roots_restrictForest hF e).2 ⟨A, hA, hAm, rfl⟩
    have hU : ((univ.filter fun l => e l ∈ A₁) ∪ univ.filter fun l => e l ∈ B₁) =
        (univ.filter fun l => e l ∈ A₂) ∪ univ.filter fun l => e l ∈ B₂ := by
      have hmem := h12 ▸ mem_insert_self ((univ.filter fun l => e l ∈ A₁) ∪
        univ.filter fun l => e l ∈ B₁) rF
      rcases mem_insert.1 hmem with h | h
      · exact h
      · exact absurd h (union_not_mem_of_mem_roots (hr hA₁ hA₁m) (hr hB₁ hB₁m)
          (fun h' => hAB₁ (marg_tr_inj hF e hA₁ hB₁ hA₁m h')))
    -- each of `A₁`, `B₁` is one of `A₂`, `B₂`
    have hin : ∀ {C}, C ∈ roots F → (∃ l, e l ∈ C) →
        (univ.filter fun l => e l ∈ C) ⊆
          ((univ.filter fun l => e l ∈ A₂) ∪ (univ.filter fun l => e l ∈ B₂)) →
        C = A₂ ∨ C = B₂ := by
      intro C hC hCm hsub
      obtain ⟨l, hl⟩ := hCm
      rcases mem_union.1 (hsub (mem_filter.2 ⟨mem_univ l, hl⟩)) with h | h
      · exact Or.inl (marg_eq_of_tr hF e hC hA₂ hl (mem_filter.1 h).2)
      · exact Or.inr (marg_eq_of_tr hF e hC hB₂ hl (mem_filter.1 h).2)
    have h1 := hin hA₁ hA₁m (hU ▸ subset_union_left)
    have h2 := hin hB₁ hB₁m (hU ▸ subset_union_right)
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact absurd rfl hAB₁
    · rfl
    · rw [union_comm]
    · exact absurd rfl hAB₁
  have hcard₂ : #M₂ = (#(roots rF)).choose 2 := by
    rw [← card_image_of_injOn hinj, himage, hrFf.card_merges]
  have hcard : #((merges F).filter fun H => restrictForest e H = rF) + #M₂ =
      (#(roots F)).choose 2 := by
    rw [hM₂, card_filter_add_card_filter_not, hF.card_merges]
  have hsum : ∑ H ∈ merges F, u (restrictForest e H) =
      #((merges F).filter fun H => restrictForest e H = rF) * u rF + ∑ H' ∈ merges rF, u H' := by
    rw [← sum_filter_add_sum_filter_not (merges F) (fun H => restrictForest e H = rF)]
    congr 1
    · rw [sum_congr rfl fun H hH => by rw [(mem_filter.1 hH).2], sum_const, nsmul_eq_mul]
    · rw [← himage, sum_image hinj]
  rw [hsum]
  have hcard' : ((#((merges F).filter fun H => restrictForest e H = rF) : ℕ) : ℝ) =
      ((#(roots F)).choose 2 : ℝ) - ((#(roots rF)).choose 2 : ℝ) := by
    rw [← hcard, ← hcard₂]
    push_cast
    ring
  rw [hcard']
  ring

/-- Intertwining of the generators: `Q M = M Q'` on the rows of forests, tested against `w`. -/
private theorem marg_sum_kingmanGenerator {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) (w : Finset (Finset L') → ℝ) :
    ∑ G, kingmanGenerator F G * w (restrictForest e G) =
      ∑ G', kingmanGenerator (restrictForest e F) G' * w G' := by
  rw [hF.sum_kingmanGenerator_mul (fun G => w (restrictForest e G)),
    (hF.restrictForest e).sum_kingmanGenerator_mul w]
  exact marg_sum_merges hF e w

/-- The generator is supported on the forest itself and its merges. -/
private theorem marg_kingmanGenerator_ne_zero {F G : Finset (Finset L)} (hF : IsForest F)
    (h : kingmanGenerator F G ≠ 0) : IsForest G := by
  rw [kingmanGenerator_apply_of_isForest] at h
  split_ifs at h with h1 h2
  · exact h1 ▸ hF
  · exact (hF.of_mem_merges h2).1
  · exact absurd rfl h

private theorem marg_sum_kingmanGenerator_pow (e : L' ↪ L) (n : ℕ) {F : Finset (Finset L)}
    (hF : IsForest F) (w : Finset (Finset L') → ℝ) :
    ∑ G, (kingmanGenerator ^ n) F G * w (restrictForest e G) =
      ∑ G', (kingmanGenerator ^ n) (restrictForest e F) G' * w G' := by
  induction n generalizing F w with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ,
      ite_true]
  | succ n ih =>
    set u : Finset (Finset L') → ℝ := fun H' => ∑ G', (kingmanGenerator ^ n) H' G' * w G'
      with hu
    have hstep : ∀ H : Finset (Finset L), kingmanGenerator F H *
        ∑ G, (kingmanGenerator ^ n) H G * w (restrictForest e G) =
          kingmanGenerator F H * u (restrictForest e H) := by
      intro H
      by_cases hQ : kingmanGenerator F H = 0
      · rw [hQ, zero_mul, zero_mul]
      · rw [ih (marg_kingmanGenerator_ne_zero hF hQ) w]
    calc ∑ G, (kingmanGenerator ^ (n + 1)) F G * w (restrictForest e G)
        = ∑ H, kingmanGenerator F H *
            ∑ G, (kingmanGenerator ^ n) H G * w (restrictForest e G) := by
          simp_rw [pow_succ', Matrix.mul_apply, sum_mul]
          rw [sum_comm]
          simp_rw [mul_sum, mul_assoc]
      _ = ∑ H, kingmanGenerator F H * u (restrictForest e H) := sum_congr rfl fun H _ => hstep H
      _ = ∑ H', kingmanGenerator (restrictForest e F) H' * u H' :=
          marg_sum_kingmanGenerator hF e u
      _ = ∑ G', (kingmanGenerator ^ (n + 1)) (restrictForest e F) G' * w G' := by
          simp_rw [hu, pow_succ', Matrix.mul_apply, sum_mul, mul_sum, mul_assoc]
          rw [sum_comm]


set_option backward.isDefEq.respectTransparency false in
/-- The entries of the exponential of a real matrix are given by the exponential series. -/
private theorem marg_hasSum_exp_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ * (A ^ n) i j) (NormedSpace.exp A i j) := by
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have h2 := Pi.hasSum.mp (Pi.hasSum.mp h i) j
  simpa using h2

/-- Lumpability of Kingman's coalescent, tested against a function `w` of the restriction. -/
private theorem marg_sum_kingmanTransition {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) (t : ℝ) (w : Finset (Finset L') → ℝ) :
    ∑ G, kingmanTransition t F G * w (restrictForest e G) =
      ∑ G', kingmanTransition t (restrictForest e F) G' * w G' := by
  have h1 : HasSum (fun n : ℕ => ∑ G, ((n.factorial : ℝ))⁻¹ *
      ((t • kingmanGenerator (L := L)) ^ n) F G * w (restrictForest e G))
      (∑ G, kingmanTransition t F G * w (restrictForest e G)) :=
    hasSum_sum fun G _ => (marg_hasSum_exp_apply _ F G).mul_right _
  have h2 : HasSum (fun n : ℕ => ∑ G', ((n.factorial : ℝ))⁻¹ *
      ((t • kingmanGenerator (L := L')) ^ n) (restrictForest e F) G' * w G')
      (∑ G', kingmanTransition t (restrictForest e F) G' * w G') :=
    hasSum_sum fun G' _ => (marg_hasSum_exp_apply _ _ G').mul_right _
  refine h1.unique ?_
  convert h2 using 1
  funext n
  simp_rw [smul_pow, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]
  rw [marg_sum_kingmanGenerator_pow e n hF w]

/-- Consistency of Kingman's coalescent (lumpability). -/
theorem kingmanTransition_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) (t : ℝ)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then kingmanTransition t F G else 0) =
      kingmanTransition t (restrictForest e F) G' := by
  have h := marg_sum_kingmanTransition hF e t fun G'' => if G'' = G' then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at h
  exact h

theorem kingmanAbsorption_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then kingmanAbsorption F G else 0) =
      kingmanAbsorption (restrictForest e F) G' := by
  have h1 : Filter.Tendsto
      (fun t => ∑ G, (if restrictForest e G = G' then kingmanTransition t F G else 0))
      Filter.atTop
      (nhds (∑ G, (if restrictForest e G = G' then kingmanAbsorption F G else 0))) := by
    refine tendsto_finsetSum _ fun G _ => ?_
    split_ifs
    · exact tendsto_kingmanTransition hF G
    · exact tendsto_const_nhds
  have h2 := tendsto_kingmanTransition (hF.restrictForest e) G'
  simp_rw [kingmanTransition_lump hF e] at h1
  exact tendsto_nhds_unique h1 h2


/-! ### Dropping lineages -/

omit [Fintype L] in
private theorem marg_restrictForest_union (e : L' ↪ L) (F₁ F₂ : Finset (Finset L)) :
    restrictForest e (F₁ ∪ F₂) = restrictForest e F₁ ∪ restrictForest e F₂ := by
  unfold restrictForest
  rw [filter_union, image_union]

omit [Fintype L] in
private theorem marg_restrictForest_empty (e : L' ↪ L) :
    restrictForest e (∅ : Finset (Finset L)) = ∅ := by
  simp [restrictForest]

omit [Fintype L] in
private theorem marg_restrictForest_sup {ι : Type*} (e : L' ↪ L) (T : Finset ι)
    (f : ι → Finset (Finset L)) :
    restrictForest e (T.sup f) = T.sup fun i => restrictForest e (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [marg_restrictForest_empty]
  | insert i T hi ih => rw [sup_insert, sup_insert, sup_eq_union, sup_eq_union,
      marg_restrictForest_union, ih]

omit [Fintype X] in
private theorem marg_restrictForest_sampledForest (e : L' ↪ L) (s : L → X) (A : Finset X) :
    restrictForest e (sampledForest s A) = sampledForest (s ∘ e) A := by
  ext D
  rw [marg_mem_restrictForest, mem_sampledForest]
  constructor
  · rintro ⟨_, hC, ⟨l', hl'⟩, rfl⟩
    obtain ⟨l, hl, rfl⟩ := mem_sampledForest.1 hC
    rw [mem_singleton] at hl'
    subst hl'
    refine ⟨l', hl, ?_⟩
    ext m
    simp [e.injective.eq_iff, eq_comm]
  · rintro ⟨l', hl', rfl⟩
    refine ⟨{e l'}, mem_sampledForest.2 ⟨e l', hl', rfl⟩, ⟨l', mem_singleton_self _⟩, ?_⟩
    ext m
    simp [e.injective.eq_iff]

/-- A sum of the form `∑ b, [g b = c] ∑ a, [f a = b] p a` is a pushforward. -/
private theorem marg_sum_ite_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] (f : α → β) (g : β → γ) (p : α → ℝ) (c : γ) :
    ∑ b, (if g b = c then ∑ a, (if f a = b then p a else 0) else 0) =
      ∑ a, if g (f a) = c then p a else 0 := by
  have h : ∀ b, (if g b = c then ∑ a, (if f a = b then p a else 0) else 0) =
      ∑ a, if f a = b then (if g b = c then p a else 0) else 0 := by
    intro b
    split_ifs with hb
    · rfl
    · simp
  simp_rw [h]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_ite_eq]
  simp

/-- The pushforward of a product is the product of the pushforwards. -/
private theorem marg_prod_pushforward {ι : Type*} [Fintype ι] [DecidableEq ι] (e : L' ↪ L)
    (φ : ι → Finset (Finset L) → ℝ) (f' : ι → Finset (Finset L')) :
    ∏ i, (∑ F, if restrictForest e F = f' i then φ i F else 0) =
      ∑ f : ι → Finset (Finset L),
        if (fun i => restrictForest e (f i)) = f' then ∏ i, φ i (f i) else 0 := by
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun f _ => ?_
  rw [prod_ite_zero]
  simp [funext_iff]

private theorem marg_populationKernel_lump (len : Finset X → ℝ) (A : Finset X)
    {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then populationKernel len A F G else 0) =
      populationKernel len A (restrictForest e F) G' := by
  unfold populationKernel
  split_ifs
  · exact kingmanAbsorption_lump hF e G'
  · exact kingmanTransition_lump hF e _ G'

/-- Dropping lineages, for the forest entering a population. -/
private theorem marg_enteringDist_comp_embedding {H : Finset (Finset X)} (len : Finset X → ℝ)
    (s : L → X) (e : L' ↪ L) {A : Finset X}
    (ih : ∀ B ∈ childClusters H A, ∀ G' : Finset (Finset L'), forestDist H len (s ∘ e) B G' =
      ∑ G, if restrictForest e G = G' then forestDist H len s B G else 0)
    (F' : Finset (Finset L')) :
    enteringDist H len (s ∘ e) A F' =
      ∑ F, if restrictForest e F = F' then enteringDist H len s A F else 0 := by
  unfold enteringDist
  rw [marg_sum_ite_comp (fun f : childClusters H A → Finset (Finset L) =>
      univ.sup f ∪ sampledForest s A) (restrictForest e)]
  have hP : ∀ f' : childClusters H A → Finset (Finset L'),
      ∏ B : childClusters H A, forestDist H len (s ∘ e) B (f' B) =
        ∑ f : childClusters H A → Finset (Finset L),
          if (fun B => restrictForest e (f B)) = f' then
            ∏ B : childClusters H A, forestDist H len s B (f B) else 0 := by
    intro f'
    rw [← marg_prod_pushforward e (fun B : childClusters H A => forestDist H len s B)]
    exact prod_congr rfl fun B _ => ih B B.2 (f' B)
  simp_rw [hP]
  rw [marg_sum_ite_comp (fun f : childClusters H A → Finset (Finset L) =>
      fun B => restrictForest e (f B)) (fun f' => univ.sup f' ∪ sampledForest (s ∘ e) A)]
  refine sum_congr rfl fun f _ => ?_
  rw [marg_restrictForest_union, marg_restrictForest_sup, marg_restrictForest_sampledForest]

/-- Dropping lineages: the multispecies coalescent of the lineages `L'` (sampled through
`s ∘ e`) is the restriction of the multispecies coalescent of the lineages `L`. -/
theorem forestDist_comp_embedding {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (s : L → X) (e : L' ↪ L) {A : Finset X} (hA : A ∈ H)
    (G' : Finset (Finset L')) :
    forestDist H len (s ∘ e) A G' =
      ∑ G, if restrictForest e G = G' then forestDist H len s A G else 0 := by
  induction A using Finset.strongInduction generalizing G' with
  | H A ih =>
  have hent := marg_enteringDist_comp_embedding (H := H) len s e (A := A)
    (fun B hB G' => ih B (mem_childClusters.1 hB).2.1 (mem_childClusters.1 hB).1 G')
  have hK : ∀ F, enteringDist H len s A F * ∑ G, (if restrictForest e G = G' then
      populationKernel len A F G else 0) =
        enteringDist H len s A F * populationKernel len A (restrictForest e F) G' := by
    intro F
    by_cases h0 : enteringDist H len s A F = 0
    · rw [h0, zero_mul, zero_mul]
    · rw [marg_populationKernel_lump len A (enteringDist_support hH len s h0).1 e G']
  calc forestDist H len (s ∘ e) A G'
      = ∑ F', enteringDist H len (s ∘ e) A F' * populationKernel len A F' G' :=
        forestDist_eq_sum_entering H len (s ∘ e) A G'
    _ = ∑ F', ∑ F, if restrictForest e F = F' then
          enteringDist H len s A F * populationKernel len A F' G' else 0 := by
        simp_rw [hent, sum_mul, ite_mul, zero_mul]
    _ = ∑ F, enteringDist H len s A F * populationKernel len A (restrictForest e F) G' := by
        rw [sum_comm]
        refine sum_congr rfl fun F _ => ?_
        rw [sum_ite_eq]
        simp
    _ = ∑ F, enteringDist H len s A F * ∑ G, (if restrictForest e G = G' then
          populationKernel len A F G else 0) := (sum_congr rfl fun F _ => hK F).symm
    _ = ∑ G, if restrictForest e G = G' then forestDist H len s A G else 0 := by
        simp_rw [mul_sum, mul_ite, mul_zero]
        rw [sum_comm]
        refine sum_congr rfl fun G _ => ?_
        rw [forestDist_eq_sum_entering H len s A G]
        split_ifs <;> simp


theorem SpeciesTree.rootedDist_comp_embedding (σ : SpeciesTree X) (s : L → X) (e : L' ↪ L)
    (G' : Finset (Finset L')) :
    σ.rootedDist (s ∘ e) G' = ∑ G, if restrictForest e G = G' then σ.rootedDist s G else 0 :=
  forestDist_comp_embedding σ.isHierarchy σ.length s e σ.univ_mem G'

/-! ### Pruning the species tree -/

/-- Reindexing the sum defining the entering distribution: the children `i` with `¬ P i` always
produce the empty forest, and the others correspond bijectively, through `τ`, to the index set
`T'`. -/
private theorem marg_sum_pi_reindex {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']
    {T : Finset ι} {T' : Finset ι'} (P : ι → Prop) [DecidablePred P] (τ : ι → ι')
    (hmaps : ∀ i ∈ T, P i → τ i ∈ T')
    (hinj : ∀ i ∈ T, ∀ j ∈ T, P i → P j → τ i = τ j → i = j)
    (hsurj : ∀ i' ∈ T', ∃ i ∈ T, P i ∧ τ i = i')
    (φ : ι → Finset (Finset L) → ℝ) (ψ : ι' → Finset (Finset L) → ℝ)
    (h0 : ∀ i ∈ T, ¬ P i → ∀ F, φ i F = if F = ∅ then 1 else 0)
    (h1 : ∀ i ∈ T, P i → φ i = ψ (τ i)) (c F : Finset (Finset L)) :
    (∑ f : T → Finset (Finset L), if univ.sup f ∪ c = F then ∏ i : T, φ i (f i) else 0) =
      ∑ g : T' → Finset (Finset L), if univ.sup g ∪ c = F then ∏ i : T', ψ i (g i) else 0 := by
  choose j hjT hjP hjτ using hsurj
  -- `j` inverts `τ`
  have hji : ∀ (i : T) (hP : P i), (⟨j (τ i) (hmaps i i.2 hP), hjT _ _⟩ : T) = i :=
    fun i hP => Subtype.ext (hinj _ (hjT _ _) i i.2 (hjP _ _) hP (hjτ _ _))
  have hij : ∀ i' : T', (⟨τ (j i'.1 i'.2), hmaps _ (hjT _ _) (hjP _ _)⟩ : T') = i' :=
    fun i' => Subtype.ext (hjτ _ _)
  -- the functions vanishing outside `P`
  have hsub : (∑ f : T → Finset (Finset L),
      if univ.sup f ∪ c = F then ∏ i : T, φ i (f i) else 0) =
      ∑ f ∈ (univ : Finset (T → Finset (Finset L))).filter
        (fun f => ∀ i : T, ¬ P i → f i = ∅),
        if univ.sup f ∪ c = F then ∏ i : T, φ i (f i) else 0 := by
    refine (sum_subset (filter_subset _ _) fun f _ hf => ?_).symm
    simp only [mem_filter, mem_univ, true_and, not_forall] at hf
    obtain ⟨i, hPi, hfi⟩ := hf
    rw [prod_eq_zero (mem_univ i) (by rw [h0 i i.2 hPi, ite_eq_right hfi]), ite_self]
  rw [hsub]
  refine sum_nbij' (fun f i' => f ⟨j i'.1 i'.2, hjT _ _⟩)
    (fun g i => if h : P i then g ⟨τ i, hmaps i i.2 h⟩ else ∅)
    (fun _ _ => mem_univ _) (fun g _ => ?_) (fun f hf => ?_) (fun g _ => ?_) (fun f hf => ?_)
  · simp only [mem_filter, mem_univ, true_and]
    intro i hi
    rw [dite_eq_right hi]
  · simp only [mem_filter, mem_univ, true_and] at hf
    funext i
    dsimp only
    by_cases hi : P i
    · rw [dite_eq_left hi, hji i hi]
    · rw [dite_eq_right hi, hf i hi]
  · funext i'
    dsimp only
    rw [dite_eq_left (hjP _ _), hij i']
  · simp only [mem_filter, mem_univ, true_and] at hf
    have hsup : univ.sup f = univ.sup fun i' : T' => f ⟨j i'.1 i'.2, hjT _ _⟩ := by
      refine le_antisymm (Finset.sup_le fun i _ => ?_) (Finset.sup_le fun i' _ => ?_)
      · by_cases hi : P i
        · have hfi : f i = (fun i' : T' => f ⟨j i'.1 i'.2, hjT _ _⟩) ⟨τ i, hmaps i i.2 hi⟩ := by
            dsimp only
            rw [hji i hi]
          rw [hfi]
          exact le_sup (f := fun i' : T' => f ⟨j i'.1 i'.2, hjT _ _⟩) (mem_univ _)
        · rw [hf i hi]
          exact bot_le
      · exact le_sup (f := f) (mem_univ _)
    have hprod : ∏ i : T, φ i (f i) = ∏ i' : T', ψ i' (f ⟨j i'.1 i'.2, hjT _ _⟩) := by
      rw [← prod_filter_of_ne (p := fun i : T => P i) fun i _ hne => ?_]
      · refine prod_bij' (fun i hi => ⟨τ i, hmaps i i.2 (mem_filter.1 hi).2⟩)
          (fun i' _ => ⟨j i'.1 i'.2, hjT _ _⟩) (fun _ _ => mem_univ _)
          (fun i' _ => mem_filter.2 ⟨mem_univ _, hjP _ _⟩) (fun i hi => ?_) (fun i' _ => ?_)
          (fun i hi => ?_)
        · exact hji i (mem_filter.1 hi).2
        · exact hij i'
        · dsimp only
          rw [h1 i i.2 (mem_filter.1 hi).2, hji i (mem_filter.1 hi).2]
      · by_contra hi
        exact hne (by rw [h0 i i.2 hi, hf i hi, ite_eq_left rfl])
    dsimp only
    rw [hsup, hprod]

omit [DecidableEq X] in
/-- Two clusters of a hierarchy sharing an element are nested. -/
private theorem marg_nested {H : Finset (Finset X)} (hH : IsHierarchy H) {A B : Finset X}
    (hA : A ∈ H) (hB : B ∈ H) {x : X} (hxA : x ∈ A) (hxB : x ∈ B) : A ⊆ B ∨ B ⊆ A := by
  rcases hH.2.2.2 A hA B hB with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hxB (Finset.disjoint_left.1 h hxA)

/-- A cluster strictly inside a cluster `A` of a hierarchy lies inside a child of `A`. -/
private theorem marg_subset_child {H : Finset (Finset X)} (hH : IsHierarchy H) {A E : Finset X}
    (hE : E ∈ H) (hEA : E ⊂ A) : ∃ B ∈ childClusters H A, E ⊆ B := by
  obtain ⟨x, hx⟩ := hH.2.2.1 E hE
  obtain ⟨y, hyA, hyE⟩ := exists_of_ssubset hEA
  have hA2 : 2 ≤ #A := one_lt_card.2 ⟨x, hEA.subset hx, y, hyA, fun h => hyE (h ▸ hx)⟩
  obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters hA2 (hEA.subset hx)
  refine ⟨B, hB, ?_⟩
  rcases marg_nested hH hE (mem_childClusters.1 hB).1 hx hxB with h | h
  · exact h
  · rcases h.eq_or_ssubset with h' | h'
    · rw [h']
    · exact absurd hEA ((mem_childClusters.1 hB).2.2 E hE h')

omit [Fintype X] in
private theorem marg_subtype_nonempty {S A : Finset X} :
    (A.subtype (· ∈ S)).Nonempty ↔ (A ∩ S).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, mem_inter.2 ⟨mem_subtype.1 hx, x.2⟩⟩
  · rintro ⟨x, hx⟩
    rw [mem_inter] at hx
    exact ⟨⟨x, hx.2⟩, mem_subtype.2 hx.1⟩

omit [Fintype X] in
private theorem marg_mem_restrictClusters {S : Finset X} {H : Finset (Finset X)}
    {D : Finset S} :
    D ∈ restrictClusters S H ↔ ∃ A ∈ H, (A ∩ S).Nonempty ∧ A.subtype (· ∈ S) = D := by
  unfold restrictClusters
  simp only [mem_image, mem_filter, and_assoc]

/-- The trace of a child of `A` meeting `S`, with a trace different from that of `A`, is a child
of the trace of `A` in the induced tree. -/
private theorem marg_subtype_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {S A B : Finset X} (hA : A ∈ H) (hB : B ∈ childClusters H A) (hBS : (B ∩ S).Nonempty)
    (hne : B.subtype (· ∈ S) ≠ A.subtype (· ∈ S)) :
    B.subtype (· ∈ S) ∈ childClusters (restrictClusters S H) (A.subtype (· ∈ S)) := by
  obtain ⟨hBH, hBA, hBmax⟩ := mem_childClusters.1 hB
  refine mem_childClusters.2 ⟨marg_mem_restrictClusters.2 ⟨B, hBH, hBS, rfl⟩,
    (subtype_mono hBA.subset).ssubset_of_ne hne, fun E' hE' hBE' hE'A => ?_⟩
  obtain ⟨E, hE, -, rfl⟩ := marg_mem_restrictClusters.1 hE'
  obtain ⟨x, hx⟩ := marg_subtype_nonempty.2 hBS
  have hxB : (x : X) ∈ B := mem_subtype.1 hx
  have hxE : (x : X) ∈ E := mem_subtype.1 (hBE'.subset hx)
  have hxA : (x : X) ∈ A := hBA.subset hxB
  rcases marg_nested hH hE hA hxE hxA with hEA | hAE
  · rcases marg_nested hH hE hBH hxE hxB with hEB | hBE
    · exact not_subset_of_ssubset hBE' (subtype_mono hEB)
    · have hBE_ne : B ≠ E := by
        rintro rfl
        exact lt_irrefl _ hBE'
      have hEA_ne : E ≠ A := by
        rintro rfl
        exact lt_irrefl _ hE'A
      exact hBmax E hE (hBE.ssubset_of_ne hBE_ne) (hEA.ssubset_of_ne hEA_ne)
  · exact not_subset_of_ssubset hE'A (subtype_mono hAE)

/-- Two children of a cluster meeting `S` with the same trace are equal. -/
private theorem marg_eq_of_subtype_eq {H : Finset (Finset X)} (hH : IsHierarchy H)
    {S A B₁ B₂ : Finset X} (hB₁ : B₁ ∈ childClusters H A) (hB₂ : B₂ ∈ childClusters H A)
    (hB₁S : (B₁ ∩ S).Nonempty) (h : B₁.subtype (· ∈ S) = B₂.subtype (· ∈ S)) : B₁ = B₂ := by
  by_contra hne
  obtain ⟨x, hx⟩ := marg_subtype_nonempty.2 hB₁S
  have hx2 : x ∈ B₂.subtype (· ∈ S) := h ▸ hx
  exact Finset.disjoint_left.1 (hH.disjoint_of_mem_childClusters hB₁ hB₂ hne)
    (mem_subtype.1 hx) (mem_subtype.1 hx2)

/-- If no child of `A` has the trace of `A`, every child of the trace of `A` in the induced tree
is the trace of a child of `A`. -/
private theorem marg_exists_child {H : Finset (Finset X)} (hH : IsHierarchy H) {S A : Finset X}
    (hH' : IsHierarchy (restrictClusters S H)) (hA : A ∈ H)
    (hbot : ∀ B ∈ childClusters H A, B.subtype (· ∈ S) ≠ A.subtype (· ∈ S))
    {D : Finset S} (hD : D ∈ childClusters (restrictClusters S H) (A.subtype (· ∈ S))) :
    ∃ B ∈ childClusters H A, (B ∩ S).Nonempty ∧ B.subtype (· ∈ S) = D := by
  obtain ⟨hDH, hDA, -⟩ := mem_childClusters.1 hD
  obtain ⟨x, hx⟩ := hH'.2.2.1 D hDH
  obtain ⟨y, hyA, hyD⟩ := exists_of_ssubset hDA
  have hxA : (x : X) ∈ A := mem_subtype.1 (hDA.subset hx)
  have hyA' : (y : X) ∈ A := mem_subtype.1 hyA
  have hA2 : 2 ≤ #A := one_lt_card.2 ⟨x, hxA, y, hyA', fun h => hyD (Subtype.ext h ▸ hx)⟩
  obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters hA2 hxA
  have hBS : (B ∩ S).Nonempty := ⟨x, mem_inter.2 ⟨hxB, x.2⟩⟩
  refine ⟨B, hB, hBS, ?_⟩
  have hBc := marg_subtype_mem_childClusters hH hA hB hBS (hbot B hB)
  by_contra hne
  exact Finset.disjoint_left.1 (hH'.disjoint_of_mem_childClusters hBc hD hne)
    (mem_subtype.2 hxB) hx

/-- A child `B` of `A` whose trace differs from that of `A` is the largest cluster with its
trace. -/
private theorem marg_filter_top {H : Finset (Finset X)} (hH : IsHierarchy H) {S A B : Finset X}
    (hA : A ∈ H) (hB : B ∈ childClusters H A) (hBS : (B ∩ S).Nonempty)
    (hne : B.subtype (· ∈ S) ≠ A.subtype (· ∈ S)) :
    H.filter (fun A' => A' ≠ univ ∧ A'.subtype (· ∈ S) = B.subtype (· ∈ S)) =
      H.filter (fun A' => A' ⊆ B ∧ A'.subtype (· ∈ S) = B.subtype (· ∈ S)) := by
  obtain ⟨hBH, hBA, hBmax⟩ := mem_childClusters.1 hB
  ext A'
  simp only [mem_filter]
  constructor
  · rintro ⟨hA'H, -, htr⟩
    refine ⟨hA'H, ?_, htr⟩
    obtain ⟨x, hx⟩ := marg_subtype_nonempty.2 hBS
    have hxB : (x : X) ∈ B := mem_subtype.1 hx
    have hxA' : (x : X) ∈ A' := mem_subtype.1 (htr.symm ▸ hx)
    have hxA : (x : X) ∈ A := hBA.subset hxB
    rcases marg_nested hH hA'H hBH hxA' hxB with h | hBA'
    · exact h
    · rcases hBA'.eq_or_ssubset with h | hBA'
      · rw [h]
      · exfalso
        rcases marg_nested hH hA'H hA hxA' hxA with hA'A | hAA'
        · rcases hA'A.eq_or_ssubset with h | hA'A
          · subst h
            exact hne htr.symm
          · exact hBmax A' hA'H hBA' hA'A
        · exact hne (subset_antisymm (subtype_mono hBA.subset) (htr ▸ subtype_mono hAA'))
  · rintro ⟨hA'H, hA'B, htr⟩
    refine ⟨hA'H, fun h => ?_, htr⟩
    subst h
    exact not_subset_of_ssubset hBA (hA'B.trans' (subset_univ A))

/-- Along a chain of clusters with the same trace, the lengths add up. -/
private theorem marg_filter_chain {H : Finset (Finset X)} (hH : IsHierarchy H) {S A B₀ : Finset X}
    (hB₀ : B₀ ∈ childClusters H A) (htr : B₀.subtype (· ∈ S) = A.subtype (· ∈ S))
    (hAS : (A ∩ S).Nonempty) (hA : A ∈ H) :
    H.filter (fun A' => A' ⊆ A ∧ A'.subtype (· ∈ S) = A.subtype (· ∈ S)) =
      insert A (H.filter (fun A' => A' ⊆ B₀ ∧ A'.subtype (· ∈ S) = B₀.subtype (· ∈ S))) := by
  obtain ⟨hB₀H, hB₀A, -⟩ := mem_childClusters.1 hB₀
  ext A'
  simp only [mem_insert, mem_filter]
  constructor
  · rintro ⟨hA'H, hA'A, htr'⟩
    rcases hA'A.eq_or_ssubset with h | hA'A
    · exact Or.inl h
    · right
      refine ⟨hA'H, ?_, htr'.trans htr.symm⟩
      obtain ⟨B, hB, hA'B⟩ := marg_subset_child hH hA'H hA'A
      obtain ⟨x, hx⟩ := marg_subtype_nonempty.2 hAS
      have hxA' : (x : X) ∈ A' := mem_subtype.1 (htr'.symm ▸ hx)
      have hxB₀ : (x : X) ∈ B₀ := mem_subtype.1 (htr.symm ▸ hx)
      have hBB₀ : B = B₀ := by
        by_contra hne
        exact Finset.disjoint_left.1 (hH.disjoint_of_mem_childClusters hB hB₀ hne)
          (hA'B hxA') hxB₀
      exact hBB₀ ▸ hA'B
  · rintro (rfl | ⟨hA'H, hA'B₀, htr'⟩)
    · exact ⟨hA, subset_rfl, rfl⟩
    · exact ⟨hA'H, hA'B₀.trans hB₀A.subset, htr'.trans htr⟩

/-- At the bottom of a chain of clusters with the same trace, only the cluster itself counts. -/
private theorem marg_filter_bot {H : Finset (Finset X)} (hH : IsHierarchy H) {S A : Finset X}
    (hA : A ∈ H) (hbot : ∀ B ∈ childClusters H A, B.subtype (· ∈ S) ≠ A.subtype (· ∈ S)) :
    H.filter (fun A' => A' ⊆ A ∧ A'.subtype (· ∈ S) = A.subtype (· ∈ S)) = {A} := by
  ext A'
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hA'H, hA'A, htr'⟩
    by_contra hne
    obtain ⟨B, hB, hA'B⟩ := marg_subset_child hH hA'H (hA'A.ssubset_of_ne hne)
    refine hbot B hB (subset_antisymm (subtype_mono (mem_childClusters.1 hB).2.1.subset) ?_)
    rw [← htr']
    exact subtype_mono hA'B
  · rintro rfl
    exact ⟨hA, subset_rfl, rfl⟩

/-- A population from which no lineage is sampled produces the empty forest. -/
private theorem marg_forestDist_eq_empty {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {s : L → X} {B : Finset X} (hB : B ∈ H) (hs : ∀ l, s l ∉ B)
    (G : Finset (Finset L)) : forestDist H len s B G = if G = ∅ then 1 else 0 := by
  have hz : ∀ G : Finset (Finset L), G ≠ ∅ → forestDist H len s B G = 0 := by
    intro G hG
    by_contra h
    obtain ⟨hGf, -, hlin⟩ := forestDist_support hH len s hB h
    obtain ⟨C, hC⟩ := nonempty_iff_ne_empty.2 hG
    obtain ⟨l, hl⟩ := hGf.1 C hC
    have hl' := subset_lineages hC hl
    rw [hlin, mem_filter] at hl'
    exact hs l hl'.2
  split_ifs with hG
  · subst hG
    have hsum := forestDist_sum hH len s hB
    rw [← sum_erase_add _ _ (mem_univ ∅), sum_eq_zero fun G hG => hz G (ne_of_mem_erase hG),
      zero_add] at hsum
    exact hsum
  · exact hz G hG

/-- At a cluster `A` with a child `B₀` with the same trace, the forest entering `A` is the forest
leaving `B₀`. -/
private theorem marg_enteringDist_chain {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {S : Finset X} {s : L → X} (hs : ∀ l, s l ∈ S) {A B₀ : Finset X}
    (hB₀ : B₀ ∈ childClusters H A) (htr : B₀.subtype (· ∈ S) = A.subtype (· ∈ S))
    (F : Finset (Finset L)) : enteringDist H len s A F = forestDist H len s B₀ F := by
  have hB₀A := (mem_childClusters.1 hB₀).2.1
  -- the other children receive no lineage
  have hother : ∀ B ∈ childClusters H A, B ≠ B₀ → ∀ l, s l ∉ B := by
    intro B hB hne l hl
    have h1 : (⟨s l, hs l⟩ : S) ∈ A.subtype (· ∈ S) :=
      mem_subtype.2 ((mem_childClusters.1 hB).2.1.subset hl)
    rw [← htr, mem_subtype] at h1
    exact Finset.disjoint_left.1 (hH.disjoint_of_mem_childClusters hB hB₀ hne) hl h1
  have hSF : sampledForest s A = sampledForest s B₀ := by
    unfold sampledForest
    congr 1
    ext l
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun h => ?_, fun h => hB₀A.subset h⟩
    have h1 : (⟨s l, hs l⟩ : S) ∈ A.subtype (· ∈ S) := mem_subtype.2 h
    rw [← htr, mem_subtype] at h1
    exact h1
  unfold enteringDist
  rw [marg_sum_pi_reindex (T' := ({B₀} : Finset (Finset X))) (fun B => B = B₀) id
    (fun B _ h => h ▸ mem_singleton_self _) (fun B _ B' _ h h' _ => h.trans h'.symm)
    (fun i' hi' => ⟨B₀, hB₀, rfl, (mem_singleton.1 hi').symm⟩)
    (fun B => forestDist H len s B) (fun B => forestDist H len s B)
    (fun B hB hne F => marg_forestDist_eq_empty hH len (mem_childClusters.1 hB).1
      (hother B hB hne) F) (fun _ _ _ => rfl)]
  let eqv : (({B₀} : Finset (Finset X)) → Finset (Finset L)) ≃ Finset (Finset L) :=
    { toFun := fun g => g ⟨B₀, mem_singleton_self _⟩
      invFun := fun F₀ _ => F₀
      left_inv := fun g => funext fun i => congr_arg g (Subtype.ext (mem_singleton.1 i.2).symm)
      right_inv := fun F₀ => rfl }
  rw [← eqv.symm.sum_comp, hSF]
  have hterm : ∀ F₀ : Finset (Finset L),
      (if univ.sup (eqv.symm F₀) ∪ sampledForest s B₀ = F then
        ∏ i : ({B₀} : Finset (Finset X)), forestDist H len s i (eqv.symm F₀ i) else 0) =
      if F₀ = F then forestDist H len s B₀ F₀ else 0 := by
    intro F₀
    have h1 : univ.sup (eqv.symm F₀) = F₀ := sup_const univ_nonempty F₀
    have h2 : ∏ i : ({B₀} : Finset (Finset X)), forestDist H len s i (eqv.symm F₀ i) =
        forestDist H len s B₀ F₀ :=
      (prod_coe_sort {B₀} (fun B => forestDist H len s B F₀)).trans (prod_singleton _ _)
    rw [h1, h2]
    by_cases h0 : forestDist H len s B₀ F₀ = 0
    · simp [h0]
    · rw [union_eq_left.2 (forestDist_support hH len s (mem_childClusters.1 hB₀).1 h0).2.1]
  rw [sum_congr rfl fun F₀ _ => hterm F₀, sum_ite_eq']
  simp

/-- At the bottom of a chain of clusters with the same trace, the forest entering `A` is the
forest entering its trace in the induced tree. -/
private theorem marg_enteringDist_restrict (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty)
    (s : L → S) {A : Finset X} (hA : A ∈ σ.clusters)
    (hbot : ∀ B ∈ childClusters σ.clusters A, B.subtype (· ∈ S) ≠ A.subtype (· ∈ S))
    (ih : ∀ B ∈ childClusters σ.clusters A, (B ∩ S).Nonempty → ∀ G,
      forestDist σ.clusters σ.length (fun l => (s l : X)) B G =
        ∑ F, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
            (B.subtype (· ∈ S)) F *
          kingmanTransition (∑ A' ∈ σ.clusters with A' ⊆ B ∧
            A'.subtype (· ∈ S) = B.subtype (· ∈ S), σ.length A') F G)
    (F : Finset (Finset L)) :
    enteringDist σ.clusters σ.length (fun l => (s l : X)) A F =
      enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
        (A.subtype (· ∈ S)) F := by
  have hH := σ.isHierarchy
  have hH' : IsHierarchy (restrictClusters S σ.clusters) := (σ.restrict S hS).isHierarchy
  have hSF : sampledForest (fun l => (s l : X)) A = sampledForest s (A.subtype (· ∈ S)) := by
    unfold sampledForest
    congr 1
    ext l
    simp [mem_subtype]
  unfold enteringDist
  rw [hSF]
  refine marg_sum_pi_reindex (fun B => (B ∩ S).Nonempty) (fun B => B.subtype (· ∈ S))
    (fun B hB hBS => marg_subtype_mem_childClusters hH hA hB hBS (hbot B hB))
    (fun B₁ hB₁ B₂ hB₂ hB₁S _ h => marg_eq_of_subtype_eq hH hB₁ hB₂ hB₁S h)
    (fun D hD => marg_exists_child hH hH' hA hbot hD)
    (fun B => forestDist σ.clusters σ.length (fun l => (s l : X)) B)
    (fun D => forestDist (σ.restrict S hS).clusters (σ.restrict S hS).length s D)
    (fun B hB hBS G => marg_forestDist_eq_empty hH σ.length (mem_childClusters.1 hB).1
      (fun l hl => hBS ⟨s l, mem_inter.2 ⟨hl, (s l).2⟩⟩) G)
    (fun B hB hBS => ?_) _ F
  funext G
  have hBc := marg_subtype_mem_childClusters hH hA hB hBS (hbot B hB)
  have hBu : B.subtype (· ∈ S) ≠ univ := by
    intro h
    have h' := (mem_childClusters.1 hBc).2.1
    rw [h] at h'
    exact not_subset_of_ssubset h' (subset_univ _)
  have hlen : (σ.restrict S hS).length (B.subtype (· ∈ S)) =
      ∑ A' ∈ σ.clusters with A' ⊆ B ∧ A'.subtype (· ∈ S) = B.subtype (· ∈ S), σ.length A' := by
    show σ.restrictLength S _ = _
    unfold SpeciesTree.restrictLength
    rw [marg_filter_top hH hA hB hBS (hbot B hB)]
  rw [ih B hB hBS G, forestDist_eq_sum_entering]
  unfold populationKernel
  rw [ite_eq_right hBu, hlen]

/-- Pruning, below the root: the forest leaving a cluster `A ≠ univ` meeting `S` is the forest
entering the trace of `A` in the induced tree, evolved for the lengths of the clusters below `A`
with the same trace. -/
private theorem marg_prune (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty) (s : L → S)
    {A : Finset X} (hA : A ∈ σ.clusters) (hAS : (A ∩ S).Nonempty) (hAu : A ≠ univ)
    (G : Finset (Finset L)) :
    forestDist σ.clusters σ.length (fun l => (s l : X)) A G =
      ∑ F, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
          (A.subtype (· ∈ S)) F *
        kingmanTransition (∑ A' ∈ σ.clusters with A' ⊆ A ∧
          A'.subtype (· ∈ S) = A.subtype (· ∈ S), σ.length A') F G := by
  have hH := σ.isHierarchy
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  have hPK : populationKernel (L := L) σ.length A = kingmanTransition (σ.length A) := by
    unfold populationKernel
    rw [ite_eq_right hAu]
  rw [forestDist_eq_sum_entering, hPK]
  by_cases hc : ∃ B₀ ∈ childClusters σ.clusters A, B₀.subtype (· ∈ S) = A.subtype (· ∈ S)
  · obtain ⟨B₀, hB₀, htr⟩ := hc
    obtain ⟨hB₀H, hB₀A, -⟩ := mem_childClusters.1 hB₀
    have hB₀S : (B₀ ∩ S).Nonempty :=
      marg_subtype_nonempty.1 (htr ▸ marg_subtype_nonempty.2 hAS)
    have hB₀u : B₀ ≠ univ := by
      intro h
      rw [h] at hB₀A
      exact not_subset_of_ssubset hB₀A (subset_univ A)
    have hAB₀ : A ∉ σ.clusters.filter
        (fun A' => A' ⊆ B₀ ∧ A'.subtype (· ∈ S) = B₀.subtype (· ∈ S)) :=
      fun h => not_subset_of_ssubset hB₀A (mem_filter.1 h).2.1
    rw [marg_filter_chain hH hB₀ htr hAS hA, sum_insert hAB₀]
    calc ∑ F, enteringDist σ.clusters σ.length (fun l => (s l : X)) A F *
          kingmanTransition (σ.length A) F G
        = ∑ F, (∑ F₀, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
            (B₀.subtype (· ∈ S)) F₀ * kingmanTransition (∑ A' ∈ σ.clusters with A' ⊆ B₀ ∧
              A'.subtype (· ∈ S) = B₀.subtype (· ∈ S), σ.length A') F₀ F) *
            kingmanTransition (σ.length A) F G := by
          refine sum_congr rfl fun F _ => ?_
          rw [marg_enteringDist_chain hH σ.length (fun l => (s l).2) hB₀ htr,
            ih B₀ hB₀A hB₀H hB₀S hB₀u F]
      _ = _ := by
          simp_rw [sum_mul]
          rw [sum_comm]
          refine sum_congr rfl fun F₀ _ => ?_
          rw [htr, add_comm, kingmanTransition_add, Matrix.mul_apply, mul_sum]
          refine sum_congr rfl fun F _ => ?_
          ring
  · push Not at hc
    have ih' : ∀ B ∈ childClusters σ.clusters A, (B ∩ S).Nonempty → ∀ G,
        forestDist σ.clusters σ.length (fun l => (s l : X)) B G =
          ∑ F, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
              (B.subtype (· ∈ S)) F *
            kingmanTransition (∑ A' ∈ σ.clusters with A' ⊆ B ∧
              A'.subtype (· ∈ S) = B.subtype (· ∈ S), σ.length A') F G := by
      intro B hB hBS G
      obtain ⟨hBH, hBA, -⟩ := mem_childClusters.1 hB
      refine ih B hBA hBH hBS ?_ G
      intro h
      rw [h] at hBA
      exact not_subset_of_ssubset hBA (subset_univ A)
    rw [marg_filter_bot hH hA hc, sum_singleton]
    exact sum_congr rfl fun F _ => by rw [marg_enteringDist_restrict σ hS s hA hc ih' F]

/-- Pruning the species tree: if all lineages are sampled from taxa in `S`, the multispecies
coalescent on `σ` is the multispecies coalescent on the induced species tree `σ(S)`. -/
theorem SpeciesTree.rootedDist_restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty)
    (s : L → S) (G : Finset (Finset L)) :
    (σ.restrict S hS).rootedDist s G = σ.rootedDist (fun l => (s l : X)) G := by
  have hH := σ.isHierarchy
  have hH' := (σ.restrict S hS).isHierarchy
  unfold SpeciesTree.rootedDist
  have hPK : populationKernel (L := L) σ.length (univ : Finset X) = kingmanAbsorption := by
    unfold populationKernel
    rw [ite_eq_left rfl]
  have hPK' : populationKernel (L := L) (σ.restrict S hS).length (univ : Finset S) =
      kingmanAbsorption := by
    unfold populationKernel
    rw [ite_eq_left rfl]
  have htru : (univ : Finset X).subtype (· ∈ S) = univ := subtype_univ _
  have hunivS : ((univ : Finset X) ∩ S).Nonempty := by simpa using hS
  rw [forestDist_eq_sum_entering, forestDist_eq_sum_entering, hPK, hPK']
  by_cases hc : ∃ B₀ ∈ childClusters σ.clusters univ,
      B₀.subtype (· ∈ S) = (univ : Finset X).subtype (· ∈ S)
  · obtain ⟨B₀, hB₀, htr⟩ := hc
    obtain ⟨hB₀H, hB₀A, -⟩ := mem_childClusters.1 hB₀
    have hB₀S : (B₀ ∩ S).Nonempty :=
      marg_subtype_nonempty.1 (htr ▸ marg_subtype_nonempty.2 hunivS)
    have hB₀u : B₀ ≠ univ := by
      intro h
      rw [h] at hB₀A
      exact lt_irrefl _ hB₀A
    symm
    calc ∑ F, enteringDist σ.clusters σ.length (fun l => (s l : X)) univ F *
          kingmanAbsorption F G
        = ∑ F, (∑ F₀, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
            (B₀.subtype (· ∈ S)) F₀ * kingmanTransition (∑ A' ∈ σ.clusters with A' ⊆ B₀ ∧
              A'.subtype (· ∈ S) = B₀.subtype (· ∈ S), σ.length A') F₀ F) *
            kingmanAbsorption F G := by
          refine sum_congr rfl fun F _ => ?_
          rw [marg_enteringDist_chain hH σ.length (fun l => (s l).2) hB₀ htr,
            marg_prune σ hS s hB₀H hB₀S hB₀u F]
      _ = _ := by
          simp_rw [sum_mul]
          rw [sum_comm]
          refine sum_congr rfl fun F₀ _ => ?_
          rw [htr, htru]
          by_cases h0 : enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
              univ F₀ = 0
          · simp only [h0, zero_mul, sum_const_zero]
          · simp_rw [mul_assoc, ← mul_sum]
            rw [kingmanTransition_mul_kingmanAbsorption (enteringDist_support hH' _ s h0).1]
  · push Not at hc
    have ih' : ∀ B ∈ childClusters σ.clusters univ, (B ∩ S).Nonempty → ∀ G,
        forestDist σ.clusters σ.length (fun l => (s l : X)) B G =
          ∑ F, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
              (B.subtype (· ∈ S)) F *
            kingmanTransition (∑ A' ∈ σ.clusters with A' ⊆ B ∧
              A'.subtype (· ∈ S) = B.subtype (· ∈ S), σ.length A') F G := by
      intro B hB hBS G
      obtain ⟨hBH, hBA, -⟩ := mem_childClusters.1 hB
      refine marg_prune σ hS s hBH hBS ?_ G
      intro h
      rw [h] at hBA
      exact lt_irrefl _ hBA
    refine sum_congr rfl fun F _ => ?_
    rw [marg_enteringDist_restrict σ hS s σ.univ_mem hc ih' F, htru]

/-! ### Unrooting -/

/-- The restriction of an unrooted tree (given by the sides of its splits, as in `ADR11.unroot`)
to the lineages `L'`, along an embedding `e : L' ↪ L`: the splits whose two sides both meet the
range of `e`, restricted to `L'`. -/
def restrictUnrooted (e : L' ↪ L) (T : Finset (Finset L)) : Finset (Finset L') :=
  (T.filter fun A => (∃ l, e l ∈ A) ∧ ∃ l, e l ∉ A).image fun A => univ.filter fun l => e l ∈ A

private theorem marg_tr_compl (e : L' ↪ L) (A : Finset L) :
    (univ.filter fun l => e l ∈ A)ᶜ = univ.filter fun l => e l ∈ Aᶜ := by
  ext l
  simp

omit [Fintype L] [DecidableEq L'] in
private theorem marg_tr_ne_univ (e : L' ↪ L) {A : Finset L} :
    (univ.filter fun l => e l ∈ A) ≠ univ ↔ ∃ l, e l ∉ A := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    exact h (filter_true_of_mem fun l _ => h' l)
  · rintro ⟨l, hl⟩ h
    have hl' : l ∈ univ.filter fun l => e l ∈ A := by
      rw [h]
      exact mem_univ l
    exact hl (mem_filter.1 hl').2

/-- Unrooting commutes with restricting to a subset of the lineages, for any family of clusters. -/
private theorem marg_unroot_restrictForest (e : L' ↪ L) (G : Finset (Finset L)) :
    unroot (restrictForest e G) = restrictUnrooted e (unroot G) := by
  ext D
  rw [absorb_mem_unroot]
  unfold restrictUnrooted
  rw [mem_image]
  simp only [mem_filter, absorb_mem_unroot]
  constructor
  · rintro (⟨hD, hDu⟩ | ⟨hD, hDu⟩)
    · obtain ⟨A, hA, hAm, rfl⟩ := (marg_mem_restrictForest e).1 hD
      have hout := (marg_tr_ne_univ e).1 hDu
      have hAu : A ≠ univ := by
        rintro rfl
        obtain ⟨l, hl⟩ := hout
        exact hl (mem_univ _)
      exact ⟨A, ⟨Or.inl ⟨hA, hAu⟩, hAm, hout⟩, rfl⟩
    · obtain ⟨A, hA, hAm, hAD⟩ := (marg_mem_restrictForest e).1 hD
      have hout := (marg_tr_ne_univ e).1 (hAD ▸ hDu)
      have hAu : A ≠ univ := by
        rintro rfl
        obtain ⟨l, hl⟩ := hout
        exact hl (mem_univ _)
      refine ⟨Aᶜ, ⟨Or.inr ⟨by rwa [compl_compl], by rwa [compl_compl]⟩, ?_, ?_⟩, ?_⟩
      · obtain ⟨l, hl⟩ := hout
        exact ⟨l, mem_compl.2 hl⟩
      · obtain ⟨l, hl⟩ := hAm
        exact ⟨l, fun h => mem_compl.1 h hl⟩
      · rw [← marg_tr_compl, hAD, compl_compl]
  · rintro ⟨A, ⟨hA, hAm, hout⟩, rfl⟩
    rcases hA with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact Or.inl ⟨marg_tr_mem_restrictForest e hA hAm, (marg_tr_ne_univ e).2 hout⟩
    · right
      rw [marg_tr_compl]
      have hAcm : ∃ l, e l ∈ Aᶜ := let ⟨l, hl⟩ := hout; ⟨l, mem_compl.2 hl⟩
      refine ⟨marg_tr_mem_restrictForest e hA hAcm, (marg_tr_ne_univ e).2 ?_⟩
      obtain ⟨l, hl⟩ := hAm
      exact ⟨l, fun h => mem_compl.1 h hl⟩

/-- Unrooting commutes with restricting a complete gene tree to a subset of the lineages. -/
theorem unroot_restrictForest {G : Finset (Finset L)}     (e : L' ↪ L) [Nonempty L'] :
    unroot (restrictForest e G) =
      ((unroot G).filter fun A => (∃ l, e l ∈ A) ∧ ∃ l, e l ∉ A).image
        fun A => univ.filter fun l => e l ∈ A :=
  marg_unroot_restrictForest e G

/-- Dropping lineages, for unrooted gene trees. -/
theorem SpeciesTree.unrootedDist_comp_embedding (σ : SpeciesTree X) (s : L → X) (e : L' ↪ L)
    (T' : Finset (Finset L')) :
    σ.unrootedDist (s ∘ e) T' =
      ∑ T, if restrictUnrooted e T = T' then σ.unrootedDist s T else 0 := by
  unfold SpeciesTree.unrootedDist
  simp_rw [σ.rootedDist_comp_embedding s e]
  rw [marg_sum_ite_comp (restrictForest e) unroot (σ.rootedDist s) T',
    marg_sum_ite_comp unroot (restrictUnrooted e) (σ.rootedDist s) T']
  simp_rw [marg_unroot_restrictForest]

end ADR11
