module

public import ADR11.Defs

/-!
# Forests of gene lineages

A forest of rooted gene trees on the lineages `L` is represented by its set of clusters
`F : Finset (Finset L)`. `IsForest F` says the clusters are nonempty and any two are nested or
disjoint; its roots (`ADR11.roots`) are then pairwise disjoint and every cluster lies below a
root. `merges F` is the set of forests obtained by merging two roots of `F`, the transitions of
Kingman's coalescent.

## Main results

* `IsForest.disjoint_of_mem_roots`, `IsForest.exists_mem_roots_subset`: the roots partition the
  lineages of a forest.
* `IsForest.isForest_merge`, `IsForest.roots_merge`, `IsForest.card_roots_merge`: merging two
  roots gives a forest with one root fewer.
* `IsForest.card_merges`: a forest with `k` roots has `k.choose 2` distinct merges.
* `kingmanGenerator_apply_of_isForest`: the rows of the generator at forests;
  `IsForest.sum_kingmanGenerator_mul`, `IsForest.kingmanGenerator_mul_apply`: the first-step
  decomposition `∑ G, Q(F, G) v(G) = -(k choose 2) v(F) + ∑ G ∈ merges F, v(G)`.
* `IsForest.union_of_disjoint`, `isForest_sup`, `IsForest.roots_union`: unions of forests on
  disjoint sets of lineages; `isForest_sampledForest`, `lineages_sampledForest`.
-/

@[expose] public section

namespace ADR11

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- A forest: nonempty clusters, any two of which are nested or disjoint. -/
def IsForest (F : Finset (Finset L)) : Prop :=
  (∀ A ∈ F, A.Nonempty) ∧ ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- The forests obtained from `F` by merging two distinct roots. -/
def merges (F : Finset (Finset L)) : Finset (Finset (Finset L)) :=
  ((roots F ×ˢ roots F).filter fun p => p.1 ≠ p.2).image fun p => insert (p.1 ∪ p.2) F

/-- The lineages of a forest: the union of its clusters. -/
def lineages (F : Finset (Finset L)) : Finset L :=
  F.sup id

theorem mem_roots {F : Finset (Finset L)} {A : Finset L} :
    A ∈ roots F ↔ A ∈ F ∧ ∀ B ∈ F, A ⊆ B → B = A := by
  unfold roots
  exact mem_filter

theorem roots_subset (F : Finset (Finset L)) : roots F ⊆ F := by
  unfold roots
  exact filter_subset _ _

@[simp] theorem roots_empty : roots (∅ : Finset (Finset L)) = ∅ := by
  unfold roots
  exact filter_empty _

theorem mem_merges {F G : Finset (Finset L)} :
    G ∈ merges F ↔ ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F := by
  unfold merges
  simp only [mem_image, mem_filter, mem_product, Prod.exists]
  constructor
  · rintro ⟨A, B, ⟨⟨hA, hB⟩, hAB⟩, rfl⟩
    exact ⟨A, hA, B, hB, hAB, rfl⟩
  · rintro ⟨A, hA, B, hB, hAB, rfl⟩
    exact ⟨A, B, ⟨⟨hA, hB⟩, hAB⟩, rfl⟩

theorem isForest_empty : IsForest (∅ : Finset (Finset L)) := by
  constructor <;> simp

/-! ### Lineages -/

section Lineages

omit [Fintype L]

theorem mem_lineages {F : Finset (Finset L)} {l : L} : l ∈ lineages F ↔ ∃ A ∈ F, l ∈ A := by
  unfold lineages
  simp only [mem_sup, id]

theorem subset_lineages {F : Finset (Finset L)} {A : Finset L} (hA : A ∈ F) :
    A ⊆ lineages F :=
  le_sup (f := id) hA

theorem lineages_subset_iff {F : Finset (Finset L)} {S : Finset L} :
    lineages F ⊆ S ↔ ∀ A ∈ F, A ⊆ S :=
  Finset.sup_le_iff

theorem lineages_mono {F G : Finset (Finset L)} (h : F ⊆ G) : lineages F ⊆ lineages G :=
  sup_mono h

@[simp] theorem lineages_empty : lineages (∅ : Finset (Finset L)) = ∅ :=
  sup_empty

@[simp] theorem lineages_singleton (A : Finset L) : lineages {A} = A :=
  sup_singleton

@[simp] theorem lineages_insert (A : Finset L) (F : Finset (Finset L)) :
    lineages (insert A F) = A ∪ lineages F :=
  sup_insert

@[simp] theorem lineages_union (F G : Finset (Finset L)) :
    lineages (F ∪ G) = lineages F ∪ lineages G :=
  sup_union

theorem lineages_sup {ι : Type*} (s : Finset ι) (f : ι → Finset (Finset L)) :
    lineages (s.sup f) = s.sup fun i => lineages (f i) := by
  unfold lineages
  rw [sup_eq_biUnion s f, sup_biUnion]

end Lineages

/-! ### Roots and merges of forests -/

/-- Every cluster lies below a maximal one (for any finite family of clusters). -/
private theorem forest_exists_mem_roots_subset {F : Finset (Finset L)} {A : Finset L}
    (hA : A ∈ F) : ∃ R ∈ roots F, A ⊆ R := by
  obtain ⟨R, hAR, hR⟩ := F.exists_le_maximal hA
  exact ⟨R, mem_roots.2 ⟨hR.1, fun B hB hRB => le_antisymm (hR.2 hB hRB) hRB⟩, hAR⟩

theorem IsForest.disjoint_of_mem_roots {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : Disjoint A B := by
  rw [mem_roots] at hA hB
  rcases hF.2 A hA.1 B hB.1 with h | h | h
  · exact absurd (hA.2 B hB.1 h).symm hAB
  · exact absurd (hB.2 A hA.1 h) hAB
  · exact h

theorem IsForest.exists_mem_roots_subset {F : Finset (Finset L)} (hF : IsForest F) {A : Finset L}
    (hA : A ∈ F) : ∃ R ∈ roots F, A ⊆ R := by
  exact forest_exists_mem_roots_subset hA

theorem IsForest.lineages_roots {F : Finset (Finset L)} (hF : IsForest F) :
    lineages (roots F) = lineages F := by
  refine (lineages_mono (roots_subset F)).antisymm (lineages_subset_iff.2 fun A hA => ?_)
  obtain ⟨R, hR, hAR⟩ := hF.exists_mem_roots_subset hA
  exact hAR.trans (subset_lineages hR)

theorem IsForest.union_not_mem {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : A ∪ B ∉ F := by
  intro h
  rw [mem_roots] at hA hB
  have h1 : A ∪ B = A := hA.2 _ h subset_union_left
  have h2 : B ⊆ A := by
    rw [← h1]
    exact subset_union_right
  exact hAB (hB.2 A hA.1 h2)

/-- A root contained in the union of two roots is one of them. -/
private theorem forest_root_subset_union {F : Finset (Finset L)} (hF : IsForest F)
    {A B C : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hC : C ∈ roots F)
    (h : C ⊆ A ∪ B) : C = A ∨ C = B := by
  by_contra hne
  push Not at hne
  obtain ⟨x, hx⟩ := hF.1 C (roots_subset F hC)
  rcases mem_union.1 (h hx) with h' | h'
  · exact disjoint_left.1 (hF.disjoint_of_mem_roots hC hA hne.1) hx h'
  · exact disjoint_left.1 (hF.disjoint_of_mem_roots hC hB hne.2) hx h'

/-- A cluster of a forest is contained in, or disjoint from, the union of two roots. -/
private theorem forest_subset_or_disjoint_union {F : Finset (Finset L)} (hF : IsForest F)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) {C : Finset L} (hC : C ∈ F) :
    C ⊆ A ∪ B ∨ Disjoint C (A ∪ B) := by
  obtain ⟨R, hR, hCR⟩ := hF.exists_mem_roots_subset hC
  by_cases hRA : R = A
  · subst hRA
    exact Or.inl (hCR.trans subset_union_left)
  by_cases hRB : R = B
  · subst hRB
    exact Or.inl (hCR.trans subset_union_right)
  right
  rw [disjoint_union_right]
  exact ⟨(hF.disjoint_of_mem_roots hR hA hRA).mono_left hCR,
    (hF.disjoint_of_mem_roots hR hB hRB).mono_left hCR⟩

theorem IsForest.isForest_merge {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : IsForest (insert (A ∪ B) F) := by
  have hAF : A ∈ F := roots_subset F hA
  refine ⟨fun C hC => ?_, fun C hC D hD => ?_⟩
  · rcases mem_insert.1 hC with rfl | hC
    · exact (hF.1 A hAF).mono subset_union_left
    · exact hF.1 C hC
  · rcases mem_insert.1 hC with rfl | hC <;> rcases mem_insert.1 hD with rfl | hD
    · exact Or.inl subset_rfl
    · rcases forest_subset_or_disjoint_union hF hA hB hD with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h.symm)
    · rcases forest_subset_or_disjoint_union hF hA hB hC with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact hF.2 C hC D hD

theorem IsForest.roots_merge {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) :
    roots (insert (A ∪ B) F) = insert (A ∪ B) (((roots F).erase A).erase B) := by
  have hA' := mem_roots.1 hA
  have hB' := mem_roots.1 hB
  ext C
  constructor
  · intro hCm
    obtain ⟨hCi, hmax⟩ := mem_roots.1 hCm
    rcases mem_insert.1 hCi with rfl | hC
    · exact mem_insert_self _ _
    · have hCr : C ∈ roots F :=
        mem_roots.2 ⟨hC, fun D hD hCD => hmax D (mem_insert_of_mem hD) hCD⟩
      refine mem_insert_of_mem (mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, hCr⟩⟩)
      · rintro rfl
        have h1 : A ∪ C = C := hmax _ (mem_insert_self _ _) subset_union_right
        have h2 : A ⊆ C := by
          rw [← h1]
          exact subset_union_left
        exact hAB (hA'.2 C hC h2).symm
      · rintro rfl
        have h1 : C ∪ B = C := hmax _ (mem_insert_self _ _) subset_union_left
        have h2 : B ⊆ C := by
          rw [← h1]
          exact subset_union_right
        exact hAB (hB'.2 C hC h2)
  · intro hCm
    rcases mem_insert.1 hCm with rfl | hC
    · refine mem_roots.2 ⟨mem_insert_self _ _, fun D hDi hUD => ?_⟩
      rcases mem_insert.1 hDi with rfl | hD
      · rfl
      · have h1 : D = A := hA'.2 D hD (subset_union_left.trans hUD)
        subst h1
        exact absurd (hB'.2 D hD (subset_union_right.trans hUD)) hAB
    · obtain ⟨hCB, hCe⟩ := mem_erase.1 hC
      obtain ⟨hCA, hCr⟩ := mem_erase.1 hCe
      have hC' := mem_roots.1 hCr
      refine mem_roots.2 ⟨mem_insert_of_mem hC'.1, fun D hD hCD => ?_⟩
      rcases mem_insert.1 hD with rfl | hD
      · exfalso
        rcases forest_root_subset_union hF hA hB hCr hCD with h | h
        · exact hCA h
        · exact hCB h
      · exact hC'.2 D hD hCD

theorem IsForest.card_roots_merge {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) :
    #(roots (insert (A ∪ B) F)) + 1 = #(roots F) := by
  have hU : A ∪ B ∉ ((roots F).erase A).erase B := fun h =>
    hF.union_not_mem hA hB hAB (roots_subset F (mem_of_mem_erase (mem_of_mem_erase h)))
  rw [hF.roots_merge hA hB hAB, card_insert_of_notMem hU,
    card_erase_add_one (mem_erase.2 ⟨hAB.symm, hB⟩), card_erase_add_one hA]

theorem IsForest.lineages_merge {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) :
    lineages (insert (A ∪ B) F) = lineages F := by
  rw [lineages_insert, union_eq_right]
  exact union_subset (subset_lineages (roots_subset F hA)) (subset_lineages (roots_subset F hB))

/-- A forest with `k` roots has exactly `k.choose 2` merges: distinct pairs of roots give
distinct forests. -/
theorem IsForest.card_merges {F : Finset (Finset L)} (hF : IsForest F) :
    #(merges F) = (#(roots F)).choose 2 := by
  -- A merge depends only on the unordered pair of roots, and determines it.
  let g : Sym2 (Finset L) → Finset (Finset L) :=
    Sym2.lift ⟨fun A B => insert (A ∪ B) F, fun A B => by simp only [union_comm]⟩
  have hg : ∀ A B, g s(A, B) = insert (A ∪ B) F := fun A B => Sym2.lift_mk _ A B
  have h1 : merges F = ((roots F).offDiag.image Sym2.mk.uncurry).image g := by
    ext G
    rw [mem_merges, image_image, mem_image]
    constructor
    · rintro ⟨A, hA, B, hB, hAB, rfl⟩
      exact ⟨(A, B), mem_offDiag.2 ⟨hA, hB, hAB⟩, hg A B⟩
    · rintro ⟨⟨A, B⟩, hp, rfl⟩
      obtain ⟨hA, hB, hAB⟩ : A ∈ roots F ∧ B ∈ roots F ∧ A ≠ B := mem_offDiag.1 hp
      exact ⟨A, hA, B, hB, hAB, (hg A B).symm⟩
  rw [h1, card_image_of_injOn, Sym2.card_image_offDiag]
  rintro _ hz _ hw hzw
  obtain ⟨⟨A, B⟩, hp, rfl⟩ := mem_image.1 hz
  obtain ⟨⟨C, D⟩, hq, rfl⟩ := mem_image.1 hw
  obtain ⟨hA, hB, hAB⟩ : A ∈ roots F ∧ B ∈ roots F ∧ A ≠ B := mem_offDiag.1 hp
  obtain ⟨hC, hD, hCD⟩ : C ∈ roots F ∧ D ∈ roots F ∧ C ≠ D := mem_offDiag.1 hq
  change g s(A, B) = g s(C, D) at hzw
  rw [hg, hg] at hzw
  have hU : A ∪ B = C ∪ D := by
    have h : A ∪ B ∈ insert (C ∪ D) F := hzw ▸ mem_insert_self _ _
    rcases mem_insert.1 h with h | h
    · exact h
    · exact absurd h (hF.union_not_mem hA hB hAB)
  have hC' := forest_root_subset_union hF hA hB hC (hU ▸ subset_union_left)
  have hD' := forest_root_subset_union hF hA hB hD (hU ▸ subset_union_right)
  change s(A, B) = s(C, D)
  rcases hC' with rfl | rfl <;> rcases hD' with rfl | rfl
  · exact absurd rfl hCD
  · rfl
  · exact Sym2.eq_swap
  · exact absurd rfl hCD

/-- What a merge of a forest is. -/
theorem IsForest.of_mem_merges {F G : Finset (Finset L)} (hF : IsForest F) (hG : G ∈ merges F) :
    IsForest G ∧ #(roots G) + 1 = #(roots F) ∧ F ⊆ G ∧ G ≠ F ∧ lineages G = lineages F := by
  obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hG
  refine ⟨hF.isForest_merge hA hB hAB, hF.card_roots_merge hA hB hAB, subset_insert _ _,
    fun h => hF.union_not_mem hA hB hAB ?_, hF.lineages_merge hA hB⟩
  rw [← h]
  exact mem_insert_self _ _

/-- The generator of Kingman's coalescent at a forest: `-(k choose 2)` on the diagonal and `1` at
each of the `k choose 2` merges. -/
theorem kingmanGenerator_apply_of_isForest {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    kingmanGenerator F G =
      if G = F then -((#(roots F)).choose 2 : ℝ) else if G ∈ merges F then 1 else 0 := by
  simp only [kingmanGenerator, mem_merges]

/-! ### More on roots -/

theorem roots_eq_empty_iff {F : Finset (Finset L)} : roots F = ∅ ↔ F = ∅ := by
  refine ⟨fun h => eq_empty_of_forall_notMem fun A hA => ?_, fun h => h ▸ roots_empty⟩
  obtain ⟨R, hR, -⟩ := forest_exists_mem_roots_subset hA
  rw [h] at hR
  exact notMem_empty R hR

theorem card_roots_eq_zero_iff {F : Finset (Finset L)} : #(roots F) = 0 ↔ F = ∅ := by
  rw [card_eq_zero, roots_eq_empty_iff]

theorem roots_nonempty_iff {F : Finset (Finset L)} : (roots F).Nonempty ↔ F.Nonempty := by
  rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, Ne, Ne, roots_eq_empty_iff]

/-- Every lineage of a forest lies in a root. -/
theorem IsForest.exists_mem_roots_of_mem_lineages {F : Finset (Finset L)} (hF : IsForest F)
    {l : L} (hl : l ∈ lineages F) : ∃ R ∈ roots F, l ∈ R := by
  rwa [← hF.lineages_roots, mem_lineages] at hl

/-- A lineage of a forest lies in only one root. -/
theorem IsForest.eq_of_mem_roots_of_mem {F : Finset (Finset L)} (hF : IsForest F)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) {l : L} (hlA : l ∈ A) (hlB : l ∈ B) :
    A = B := by
  by_contra hAB
  exact disjoint_left.1 (hF.disjoint_of_mem_roots hA hB hAB) hlA hlB

/-- A forest with a single root is a tree: the root is the set of all its lineages. -/
theorem IsForest.roots_eq_singleton_lineages {F : Finset (Finset L)} (hF : IsForest F)
    (h : #(roots F) = 1) : roots F = {lineages F} := by
  obtain ⟨R, hR⟩ := card_eq_one.1 h
  rw [hR, ← hF.lineages_roots, hR, lineages_singleton]

theorem IsForest.lineages_mem_of_card_roots_eq_one {F : Finset (Finset L)} (hF : IsForest F)
    (h : #(roots F) = 1) : lineages F ∈ F :=
  roots_subset F (by rw [hF.roots_eq_singleton_lineages h]; exact mem_singleton_self _)

/-- The roots of a forest partition its lineages. -/
theorem IsForest.sum_card_roots {F : Finset (Finset L)} (hF : IsForest F) :
    ∑ R ∈ roots F, #R = #(lineages F) := by
  rw [← hF.lineages_roots, lineages, sup_eq_biUnion, card_biUnion]
  · rfl
  · intro A hA B hB hAB
    exact hF.disjoint_of_mem_roots hA hB hAB

theorem IsForest.card_roots_le_card_lineages {F : Finset (Finset L)} (hF : IsForest F) :
    #(roots F) ≤ #(lineages F) := by
  rw [← hF.sum_card_roots, card_eq_sum_ones]
  exact sum_le_sum fun R hR => Nat.succ_le_of_lt (hF.1 R (roots_subset F hR)).card_pos

/-! ### More on merges and the generator -/

@[simp] theorem merges_empty : merges (∅ : Finset (Finset L)) = ∅ := by
  refine eq_empty_of_forall_notMem fun G hG => ?_
  obtain ⟨A, hA, -⟩ := mem_merges.1 hG
  rw [roots_empty] at hA
  exact notMem_empty A hA

/-- A forest with at most one root has no merges. -/
theorem merges_eq_empty_of_card_roots_le_one {F : Finset (Finset L)} (h : #(roots F) ≤ 1) :
    merges F = ∅ := by
  refine eq_empty_of_forall_notMem fun G hG => ?_
  obtain ⟨A, hA, B, hB, hAB, -⟩ := mem_merges.1 hG
  exact hAB (card_le_one.1 h A hA B hB)

theorem IsForest.merges_eq_empty_iff {F : Finset (Finset L)} (hF : IsForest F) :
    merges F = ∅ ↔ #(roots F) ≤ 1 := by
  rw [← card_eq_zero, hF.card_merges, Nat.choose_eq_zero_iff]
  omega

theorem IsForest.merges_nonempty {F : Finset (Finset L)} (hF : IsForest F)
    (h : 2 ≤ #(roots F)) : (merges F).Nonempty := by
  rw [← card_pos, hF.card_merges]
  exact Nat.choose_pos h

theorem IsForest.self_not_mem_merges {F : Finset (Finset L)} (hF : IsForest F) :
    F ∉ merges F := fun h =>
  (hF.of_mem_merges h).2.2.2.1 rfl

theorem kingmanGenerator_apply_self (F : Finset (Finset L)) :
    kingmanGenerator F F = -((#(roots F)).choose 2 : ℝ) := by
  simp [kingmanGenerator]

/-- The generator at a forest, split into its diagonal part and its merge part. -/
private theorem forest_kingmanGenerator_eq_add {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    kingmanGenerator F G =
      (if G = F then -((#(roots F)).choose 2 : ℝ) else 0) + (if G ∈ merges F then 1 else 0) := by
  rw [kingmanGenerator_apply_of_isForest hF]
  by_cases h1 : G = F
  · subst h1
    simp [hF.self_not_mem_merges]
  · simp [h1]

/-- First-step decomposition at a forest `F` with `k` roots:
`∑ G, Q(F, G) v(G) = -(k choose 2) v(F) + ∑ G ∈ merges F, v(G)`. -/
theorem IsForest.sum_kingmanGenerator_mul {F : Finset (Finset L)} (hF : IsForest F)
    (v : Finset (Finset L) → ℝ) :
    ∑ G, kingmanGenerator F G * v G =
      -((#(roots F)).choose 2 : ℝ) * v F + ∑ G ∈ merges F, v G := by
  simp only [forest_kingmanGenerator_eq_add hF, add_mul, ite_mul, one_mul, zero_mul,
    sum_add_distrib, sum_ite_eq', mem_univ, ite_true, sum_ite_mem, univ_inter]

/-- The rows of `Q * M` at a forest. -/
theorem IsForest.kingmanGenerator_mul_apply {F : Finset (Finset L)} (hF : IsForest F)
    (M : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) (G : Finset (Finset L)) :
    (kingmanGenerator (L := L) * M) F G =
      -((#(roots F)).choose 2 : ℝ) * M F G + ∑ F' ∈ merges F, M F' G := by
  rw [Matrix.mul_apply]
  exact hF.sum_kingmanGenerator_mul fun F' => M F' G

/-- The rows of the generator at forests sum to `0`. -/
theorem IsForest.sum_kingmanGenerator {F : Finset (Finset L)} (hF : IsForest F) :
    ∑ G, kingmanGenerator F G = 0 := by
  have h := hF.sum_kingmanGenerator_mul fun _ => 1
  simp only [mul_one, sum_const, nsmul_eq_mul, hF.card_merges] at h
  rw [h]
  ring

/-! ### Building forests -/

section Building

omit [Fintype L]

omit [DecidableEq L] in
theorem IsForest.subset {F G : Finset (Finset L)} (hG : IsForest G) (h : F ⊆ G) : IsForest F :=
  ⟨fun A hA => hG.1 A (h hA), fun A hA B hB => hG.2 A (h hA) B (h hB)⟩

/-- The union of two forests whose clusters are pairwise nested or disjoint is a forest. -/
theorem IsForest.union {F G : Finset (Finset L)} (hF : IsForest F) (hG : IsForest G)
    (h : ∀ A ∈ F, ∀ B ∈ G, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) : IsForest (F ∪ G) := by
  refine ⟨fun A hA => ?_, fun A hA B hB => ?_⟩
  · rcases mem_union.1 hA with hA | hA
    · exact hF.1 A hA
    · exact hG.1 A hA
  · rcases mem_union.1 hA with hA | hA <;> rcases mem_union.1 hB with hB | hB
    · exact hF.2 A hA B hB
    · exact h A hA B hB
    · rcases h B hB A hA with h' | h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inl h'
      · exact Or.inr (Or.inr h'.symm)
    · exact hG.2 A hA B hB

/-- The union of two forests on disjoint sets of lineages is a forest. -/
theorem IsForest.union_of_disjoint {F G : Finset (Finset L)} (hF : IsForest F) (hG : IsForest G)
    (h : Disjoint (lineages F) (lineages G)) : IsForest (F ∪ G) :=
  hF.union hG fun _ hA _ hB =>
    Or.inr (Or.inr (h.mono (subset_lineages hA) (subset_lineages hB)))

/-- The union of a family of forests on pairwise disjoint sets of lineages is a forest. -/
theorem isForest_sup {ι : Type*} (s : Finset ι) (f : ι → Finset (Finset L))
    (hf : ∀ i ∈ s, IsForest (f i)) (hd : (s : Set ι).PairwiseDisjoint fun i => lineages (f i)) :
    IsForest (s.sup f) := by
  classical
  refine ⟨fun A hA => ?_, fun A hA B hB => ?_⟩
  · obtain ⟨i, hi, hA⟩ := mem_sup.1 hA
    exact (hf i hi).1 A hA
  · obtain ⟨i, hi, hA⟩ := mem_sup.1 hA
    obtain ⟨j, hj, hB⟩ := mem_sup.1 hB
    by_cases hij : i = j
    · subst hij
      exact (hf i hi).2 A hA B hB
    · exact Or.inr (Or.inr ((hd hi hj hij).mono (subset_lineages hA) (subset_lineages hB)))

/-- A forest of singletons. -/
private theorem forest_isForest_image_singleton (S : Finset L) :
    IsForest (S.image fun l => {l}) := by
  refine ⟨fun A hA => ?_, fun A hA B hB => ?_⟩
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hA
    exact singleton_nonempty l
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hA
    obtain ⟨m, -, rfl⟩ := mem_image.1 hB
    by_cases hlm : l = m
    · subst hlm
      exact Or.inl subset_rfl
    · exact Or.inr (Or.inr (disjoint_singleton.2 hlm))

@[simp] theorem lineages_image_singleton (S : Finset L) :
    lineages (S.image fun l => {l}) = S := by
  ext l
  simp [mem_lineages]

/-- Adding singletons to a forest gives a forest. -/
theorem IsForest.union_image_singleton {F : Finset (Finset L)} (hF : IsForest F)
    (S : Finset L) : IsForest (F ∪ S.image fun l => {l}) := by
  refine hF.union (forest_isForest_image_singleton S) fun A _ B hB => ?_
  obtain ⟨l, -, rfl⟩ := mem_image.1 hB
  by_cases hl : l ∈ A
  · exact Or.inr (Or.inl (singleton_subset_iff.2 hl))
  · exact Or.inr (Or.inr (disjoint_singleton_right.2 hl))

end Building

/-- Every cluster of a forest of singletons is a root. -/
private theorem forest_roots_image_singleton (S : Finset L) :
    roots (S.image fun l => {l}) = S.image fun l => {l} := by
  refine subset_antisymm (roots_subset _) fun A hA => mem_roots.2 ⟨hA, fun B hB hAB => ?_⟩
  obtain ⟨l, -, rfl⟩ := mem_image.1 hA
  obtain ⟨m, -, rfl⟩ := mem_image.1 hB
  rw [singleton_subset_singleton.1 hAB]

private theorem forest_card_roots_image_singleton (S : Finset L) :
    #(roots (S.image fun l => {l})) = #S := by
  rw [forest_roots_image_singleton, card_image_of_injective S singleton_injective]

/-- The roots of the union of two forests on disjoint sets of lineages. -/
theorem IsForest.roots_union {F G : Finset (Finset L)} (hF : IsForest F) (hG : IsForest G)
    (h : Disjoint (lineages F) (lineages G)) : roots (F ∪ G) = roots F ∪ roots G := by
  have key : ∀ {F G : Finset (Finset L)}, IsForest F → Disjoint (lineages F) (lineages G) →
      ∀ A ∈ F, ∀ B ∈ G, ¬ A ⊆ B := by
    intro F G hF h A hA B hB hAB
    obtain ⟨x, hx⟩ := hF.1 A hA
    exact disjoint_left.1 h (subset_lineages hA hx) (subset_lineages hB (hAB hx))
  ext A
  simp only [mem_union, mem_roots]
  constructor
  · rintro ⟨hA | hA, hmax⟩
    · exact Or.inl ⟨hA, fun B hB => hmax B (Or.inl hB)⟩
    · exact Or.inr ⟨hA, fun B hB => hmax B (Or.inr hB)⟩
  · rintro (⟨hA, hmax⟩ | ⟨hA, hmax⟩)
    · refine ⟨Or.inl hA, fun B hB hAB => ?_⟩
      rcases hB with hB | hB
      · exact hmax B hB hAB
      · exact absurd hAB (key hF h A hA B hB)
    · refine ⟨Or.inr hA, fun B hB hAB => ?_⟩
      rcases hB with hB | hB
      · exact absurd hAB (key hG h.symm A hA B hB)
      · exact hmax B hB hAB

theorem IsForest.card_roots_union {F G : Finset (Finset L)} (hF : IsForest F) (hG : IsForest G)
    (h : Disjoint (lineages F) (lineages G)) : #(roots (F ∪ G)) = #(roots F) + #(roots G) := by
  rw [hF.roots_union hG h, card_union_of_disjoint]
  refine disjoint_left.2 fun A hAF hAG => ?_
  obtain ⟨x, hx⟩ := hF.1 A (roots_subset F hAF)
  exact disjoint_left.1 h (subset_lineages (roots_subset F hAF) hx)
    (subset_lineages (roots_subset G hAG) hx)

/-! ### The forests of sampled lineages -/

theorem isForest_sampledForest {X : Type*} [DecidableEq X] (s : L → X) (A : Finset X) :
    IsForest (sampledForest s A) :=
  forest_isForest_image_singleton _

theorem roots_sampledForest {X : Type*} [DecidableEq X] (s : L → X) (A : Finset X) :
    roots (sampledForest s A) = sampledForest s A :=
  forest_roots_image_singleton _

theorem card_roots_sampledForest {X : Type*} [DecidableEq X] (s : L → X) (A : Finset X) :
    #(roots (sampledForest s A)) = #(univ.filter fun l => s l ∈ A) :=
  forest_card_roots_image_singleton _

@[simp] theorem lineages_sampledForest {X : Type*} [DecidableEq X] (s : L → X) (A : Finset X) :
    lineages (sampledForest s A) = univ.filter fun l => s l ∈ A :=
  lineages_image_singleton _

end ADR11
