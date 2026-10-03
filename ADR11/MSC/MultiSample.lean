module

public import ADR11.MSC.Marginal

/-!
# Several lineages per taxon: the extended species tree (proof of Corollary 10)

When at most two lineages are sampled from each taxon, the multispecies coalescent with lineages
`L` sampled through a surjection `s : L → X` is the multispecies coalescent with one lineage per
leaf on the *extended species tree* `σ.extend s` on the taxon set `L`: its clusters are the
preimages `s⁻¹(A)` of the clusters of `σ` and the singletons of `L`; the edge above `s⁻¹(A)` keeps
the length of the edge above `A` (so the pendant edge of a taxon sampled twice becomes an internal
edge), and the new pendant edges get length `1`.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

/-- The clusters of the extended species tree. -/
def extendClusters (H : Finset (Finset X)) (s : L → X) : Finset (Finset L) :=
  H.image (fun A => univ.filter fun l => s l ∈ A) ∪ univ.image fun l => {l}

/-! ### Preimages of clusters under the sampling map -/

omit [Fintype X] in
private lemma multi_mem_extendClusters {H : Finset (Finset X)} (s : L → X) {A : Finset X}
    (hA : A ∈ H) : (univ.filter fun l => s l ∈ A) ∈ extendClusters H s :=
  mem_union_left _ (mem_image_of_mem _ hA)

omit [DecidableEq L] in
private lemma multi_pre_univ (s : L → X) :
    (univ.filter fun l => s l ∈ (univ : Finset X)) = univ :=
  filter_true_of_mem fun _ _ => mem_univ _

omit [Fintype X] [DecidableEq L] in
private lemma multi_pre_singleton (s : L → X) (x : X) :
    (univ.filter fun l => s l ∈ ({x} : Finset X)) = univ.filter fun l => s l = x := by
  simp only [mem_singleton]

omit [Fintype X] [DecidableEq L] in
private lemma multi_pre_mono (s : L → X) {A B : Finset X} (h : A ⊆ B) :
    (univ.filter fun l => s l ∈ A) ⊆ univ.filter fun l => s l ∈ B :=
  fun l hl => mem_filter.2 ⟨mem_univ l, h (mem_filter.1 hl).2⟩

omit [Fintype X] [DecidableEq L] in
private lemma multi_pre_subset_pre {s : L → X} (hs : Function.Surjective s) {A B : Finset X} :
    (univ.filter fun l => s l ∈ A) ⊆ (univ.filter fun l => s l ∈ B) ↔ A ⊆ B := by
  refine ⟨fun h x hx => ?_, multi_pre_mono s⟩
  obtain ⟨l, rfl⟩ := hs x
  exact (mem_filter.1 (h (mem_filter.2 ⟨mem_univ l, hx⟩))).2

omit [Fintype X] [DecidableEq L] in
private lemma multi_pre_inj {s : L → X} (hs : Function.Surjective s) {A B : Finset X} :
    (univ.filter fun l => s l ∈ A) = (univ.filter fun l => s l ∈ B) ↔ A = B := by
  refine ⟨fun h => subset_antisymm ?_ ?_, fun h => h ▸ rfl⟩
  · exact (multi_pre_subset_pre hs).1 h.le
  · exact (multi_pre_subset_pre hs).1 h.ge

omit [Fintype X] [DecidableEq L] in
private lemma multi_pre_ssubset_pre {s : L → X} (hs : Function.Surjective s) {A B : Finset X} :
    (univ.filter fun l => s l ∈ A) ⊂ (univ.filter fun l => s l ∈ B) ↔ A ⊂ B := by
  rw [ssubset_iff_subset_ne, ssubset_iff_subset_ne, multi_pre_subset_pre hs, Ne, Ne,
    multi_pre_inj hs]

omit [DecidableEq L] in
private lemma multi_pre_ne_univ {s : L → X} (hs : Function.Surjective s) {A : Finset X}
    (hA : A ≠ univ) : (univ.filter fun l => s l ∈ A) ≠ univ :=
  fun h => hA ((multi_pre_inj hs).1 (h.trans (multi_pre_univ s).symm))

omit [Fintype X] [DecidableEq L] in
private lemma multi_pre_disjoint (s : L → X) {A B : Finset X} (h : Disjoint A B) :
    Disjoint (univ.filter fun l => s l ∈ A) (univ.filter fun l => s l ∈ B) :=
  disjoint_left.2 fun _ hlA hlB =>
    disjoint_left.1 h (mem_filter.1 hlA).2 (mem_filter.1 hlB).2

omit [Fintype X] [DecidableEq L] in
private lemma multi_pre_nonempty {s : L → X} (hs : Function.Surjective s) {A : Finset X}
    (hA : A.Nonempty) : (univ.filter fun l => s l ∈ A).Nonempty := by
  obtain ⟨x, hx⟩ := hA
  obtain ⟨l, rfl⟩ := hs x
  exact ⟨l, mem_filter.2 ⟨mem_univ l, hx⟩⟩

omit [Fintype X] [DecidableEq L] in
private lemma multi_card_le_card_pre {s : L → X} (hs : Function.Surjective s) (A : Finset X) :
    #A ≤ #(univ.filter fun l => s l ∈ A) := by
  refine (card_le_card (t := (univ.filter fun l => s l ∈ A).image s) fun x hx => ?_).trans
    card_image_le
  obtain ⟨l, rfl⟩ := hs x
  exact mem_image_of_mem s (mem_filter.2 ⟨mem_univ l, hx⟩)

omit [Fintype X] [DecidableEq L] in
/-- A set of taxa whose preimage is a singleton `{l}` is the singleton `{s l}`. -/
private lemma multi_eq_singleton_of_pre_eq {s : L → X} (hs : Function.Surjective s)
    {A : Finset X} {l : L} (h : {l} = univ.filter fun l => s l ∈ A) : A = {s l} := by
  ext y
  rw [mem_singleton]
  constructor
  · intro hy
    obtain ⟨l', rfl⟩ := hs y
    have : l' ∈ ({l} : Finset L) := h ▸ mem_filter.2 ⟨mem_univ l', hy⟩
    rw [mem_singleton.1 this]
  · rintro rfl
    have hl : l ∈ univ.filter fun l => s l ∈ A := by
      rw [← h]
      exact mem_singleton_self l
    exact (mem_filter.1 hl).2

omit [Fintype X] in
private lemma multi_sampledForest_pre (s : L → X) (A : Finset X) :
    sampledForest s A = sampledForest id (univ.filter fun l => s l ∈ A) := by
  unfold sampledForest
  congr 1
  ext l
  simp

/-! ### The extended species tree -/

theorem SpeciesTree.extend_univ_mem (σ : SpeciesTree X) (s : L → X) :
    (univ : Finset L) ∈ extendClusters σ.clusters s := by
  rw [← multi_pre_univ s]
  exact multi_mem_extendClusters s σ.univ_mem

theorem SpeciesTree.extend_singleton_mem (σ : SpeciesTree X) (s : L → X) (l : L) :
    {l} ∈ extendClusters σ.clusters s :=
  mem_union_right _ (mem_image_of_mem _ (mem_univ l))

theorem SpeciesTree.extend_nonempty_of_mem (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) : ∀ B ∈ extendClusters σ.clusters s, B.Nonempty := by
  intro B hB
  rcases mem_union.1 hB with hB | hB
  · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    exact multi_pre_nonempty hs (σ.nonempty_of_mem A hA)
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hB
    exact singleton_nonempty l

omit [Fintype L] in
private lemma multi_singleton_laminar (l : L) (C : Finset L) :
    {l} ⊆ C ∨ C ⊆ {l} ∨ Disjoint {l} C := by
  by_cases h : l ∈ C
  · exact Or.inl (singleton_subset_iff.2 h)
  · exact Or.inr (Or.inr (disjoint_singleton_left.2 h))

theorem SpeciesTree.extend_laminar (σ : SpeciesTree X) (s : L → X) :
    ∀ B ∈ extendClusters σ.clusters s, ∀ C ∈ extendClusters σ.clusters s,
      B ⊆ C ∨ C ⊆ B ∨ Disjoint B C := by
  intro B hB C hC
  rcases mem_union.1 hB with hB | hB
  · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    rcases mem_union.1 hC with hC | hC
    · obtain ⟨A', hA', rfl⟩ := mem_image.1 hC
      rcases σ.laminar A hA A' hA' with h | h | h
      · exact Or.inl (multi_pre_mono s h)
      · exact Or.inr (Or.inl (multi_pre_mono s h))
      · exact Or.inr (Or.inr (multi_pre_disjoint s h))
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hC
      rcases multi_singleton_laminar l (univ.filter fun l => s l ∈ A) with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h.symm)
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hB
    exact multi_singleton_laminar l C

/-- The lengths of the extended species tree: a cluster `s⁻¹(A)` keeps the length of `A`; a new
singleton cluster gets length `1`. -/
noncomputable def SpeciesTree.extendLength (σ : SpeciesTree X) (s : L → X) (B : Finset L) : ℝ :=
  if h : ∃ A ∈ σ.clusters, (univ.filter fun l => s l ∈ A) = B ∧ 2 ≤ #B then
    σ.length h.choose else 1

theorem SpeciesTree.extendLength_pos (σ : SpeciesTree X) (s : L → X) :
    ∀ B ∈ extendClusters σ.clusters s, B ≠ univ → 0 < σ.extendLength s B := by
  intro B _ hBu
  unfold SpeciesTree.extendLength
  split_ifs with h
  · obtain ⟨hA, hAB, -⟩ := h.choose_spec
    refine σ.length_pos _ hA fun hu => hBu ?_
    rw [← hAB, hu, multi_pre_univ]
  · exact one_pos

/-- The extended species tree on the lineages `L`. -/
noncomputable def SpeciesTree.extend (σ : SpeciesTree X) (s : L → X)
    (hs : Function.Surjective s) : SpeciesTree L where
  clusters := extendClusters σ.clusters s
  univ_mem := σ.extend_univ_mem s
  singleton_mem := σ.extend_singleton_mem s
  nonempty_of_mem := σ.extend_nonempty_of_mem hs
  laminar := σ.extend_laminar s
  length := σ.extendLength s
  length_pos := σ.extendLength_pos s

/-- The edge above the preimage of a cluster with at least two lineages keeps its length. -/
private lemma multi_extendLength_pre (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) {A : Finset X} (hA : A ∈ σ.clusters)
    (h2 : 2 ≤ #(univ.filter fun l => s l ∈ A)) :
    σ.extendLength s (univ.filter fun l => s l ∈ A) = σ.length A := by
  unfold SpeciesTree.extendLength
  have h : ∃ A' ∈ σ.clusters, (univ.filter fun l => s l ∈ A') =
      (univ.filter fun l => s l ∈ A) ∧ 2 ≤ #(univ.filter fun l => s l ∈ A) := ⟨A, hA, rfl, h2⟩
  rw [dite_eq_left h, (multi_pre_inj hs).1 h.choose_spec.2.1]

/-- The population above the preimage of a cluster with at least two lineages is the population
above the cluster. -/
private lemma multi_populationKernel_pre (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) {A : Finset X} (hA : A ∈ σ.clusters)
    (h2 : 2 ≤ #(univ.filter fun l => s l ∈ A)) :
    populationKernel (L := L) σ.length A =
      populationKernel (σ.extendLength s) (univ.filter fun l => s l ∈ A) := by
  unfold populationKernel
  by_cases hAu : A = univ
  · subst hAu
    rw [ite_eq_left rfl, ite_eq_left (multi_pre_univ s)]
  · rw [ite_eq_right hAu, ite_eq_right (multi_pre_ne_univ hs hAu),
      multi_extendLength_pre σ hs hA h2]

/-- The children of the preimage of a cluster with at least two taxa are the preimages of its
children. -/
private lemma multi_childClusters_pre (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) {A : Finset X} (h2 : 2 ≤ #A) :
    childClusters (extendClusters σ.clusters s) (univ.filter fun l => s l ∈ A) =
      (childClusters σ.clusters A).image fun B => univ.filter fun l => s l ∈ B := by
  ext C
  rw [mem_image]
  constructor
  · intro hC
    obtain ⟨hCE, hCA, hmax⟩ := mem_childClusters.1 hC
    rcases mem_union.1 hCE with hCE | hCE
    · obtain ⟨D, hD, rfl⟩ := mem_image.1 hCE
      refine ⟨D, mem_childClusters.2 ⟨hD, (multi_pre_ssubset_pre hs).1 hCA,
        fun D' hD' hDD' hD'A => ?_⟩, rfl⟩
      exact hmax _ (multi_mem_extendClusters s hD') ((multi_pre_ssubset_pre hs).2 hDD')
        ((multi_pre_ssubset_pre hs).2 hD'A)
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hCE
      have hl : s l ∈ A := (mem_filter.1 (hCA.subset (mem_singleton_self l))).2
      obtain ⟨B, hB, hlB⟩ := σ.isHierarchy.exists_mem_childClusters h2 hl
      refine ⟨B, hB, ?_⟩
      have hsub : {l} ⊆ univ.filter fun l => s l ∈ B :=
        singleton_subset_iff.2 (mem_filter.2 ⟨mem_univ _, hlB⟩)
      rcases hsub.eq_or_ssubset with h | h
      · exact h.symm
      · exact absurd ((multi_pre_ssubset_pre hs).2 (mem_childClusters.1 hB).2.1)
          (hmax _ (multi_mem_extendClusters s (mem_childClusters.1 hB).1) h)
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨hBH, hBA, hmax⟩ := mem_childClusters.1 hB
    refine mem_childClusters.2 ⟨multi_mem_extendClusters s hBH, (multi_pre_ssubset_pre hs).2 hBA,
      fun C hC hBC hCA => ?_⟩
    rcases mem_union.1 hC with hC | hC
    · obtain ⟨D, hD, rfl⟩ := mem_image.1 hC
      exact hmax D hD ((multi_pre_ssubset_pre hs).1 hBC) ((multi_pre_ssubset_pre hs).1 hCA)
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hC
      rw [ssubset_singleton_iff] at hBC
      exact (multi_pre_nonempty hs (σ.nonempty_of_mem B hBH)).ne_empty hBC

/-- Reindexing a sum over the functions on a finset along an equivalence. -/
private lemma multi_sum_pi_equiv {ι κ α : Type*} [Fintype α] [DecidableEq ι] [DecidableEq κ]
    {S : Finset ι} {T : Finset κ} (e : S ≃ T) (g : (T → α) → ℝ) :
    ∑ f : T → α, g f = ∑ f : S → α, g (fun C => f (e.symm C)) :=
  (Fintype.sum_equiv (e.arrowCongr (Equiv.refl α)) _ _ fun _ => rfl).symm

/-- The multispecies coalescent below a cluster `A` with at most two lineages per taxon is the
multispecies coalescent below `s⁻¹(A)` in the extended species tree, with one lineage per leaf. -/
private lemma multi_forestDist_extend (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) (h2 : ∀ x, #(univ.filter fun l => s l = x) ≤ 2) {A : Finset X}
    (hA : A ∈ σ.clusters) (G : Finset (Finset L)) :
    forestDist σ.clusters σ.length s A G =
      forestDist (extendClusters σ.clusters s) (σ.extendLength s) id
        (univ.filter fun l => s l ∈ A) G := by
  have hE : IsHierarchy (extendClusters σ.clusters s) := (σ.extend s hs).isHierarchy
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  obtain ⟨x, hx⟩ := σ.nonempty_of_mem A hA
  rcases Nat.lt_or_ge 1 #A with hA2 | hA1
  · -- an internal node: the children of `s⁻¹(A)` are the preimages of the children of `A`
    have hpre2 : 2 ≤ #(univ.filter fun l => s l ∈ A) :=
      (show 2 ≤ #A from hA2).trans (multi_card_le_card_pre hs A)
    have hch := multi_childClusters_pre σ hs (show 2 ≤ #A from hA2)
    have hmem : ∀ B : childClusters σ.clusters A,
        (univ.filter fun l => s l ∈ (B : Finset X)) ∈
          childClusters (extendClusters σ.clusters s) (univ.filter fun l => s l ∈ A) :=
      fun B => hch ▸ mem_image_of_mem _ B.2
    let e : childClusters σ.clusters A ≃
        childClusters (extendClusters σ.clusters s) (univ.filter fun l => s l ∈ A) :=
      Equiv.ofBijective (fun B => ⟨_, hmem B⟩)
        ⟨fun B B' h => Subtype.ext ((multi_pre_inj hs).1 (congrArg Subtype.val h)), fun C => by
          have hC : (C : Finset L) ∈
              (childClusters σ.clusters A).image fun B => univ.filter fun l => s l ∈ B := by
            rw [← hch]
            exact C.2
          obtain ⟨B, hB, hBC⟩ := mem_image.1 hC
          exact ⟨⟨B, hB⟩, Subtype.ext hBC⟩⟩
    have he : ∀ B, ((e B : Finset L)) = univ.filter fun l => s l ∈ (B : Finset X) := fun _ => rfl
    rw [forestDist.eq_1 σ.clusters σ.length, forestDist.eq_1 (extendClusters σ.clusters s),
      multi_sum_pi_equiv e]
    refine Finset.sum_congr rfl fun g _ => ?_
    congr 1
    · refine Fintype.prod_equiv e _ _ fun B => ?_
      dsimp only
      rw [e.symm_apply_apply, he,
        ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1]
    · rw [multi_populationKernel_pre σ hs hA hpre2, multi_sampledForest_pre s A]
      congr 2
      refine le_antisymm (Finset.sup_le fun B _ => ?_) (Finset.sup_le fun C _ => ?_)
      · have := Finset.le_sup (f := fun C => g (e.symm C)) (mem_univ (e B))
        simpa using this
      · exact Finset.le_sup (mem_univ _)
  · -- a leaf `{x}` from which one or two lineages are sampled
    have hAx : A = {x} :=
      eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => card_le_one.1 hA1 y hy x hx⟩
    subst hAx
    have hx1 : 1 ≤ #(univ.filter fun l => s l = x) := by
      obtain ⟨l, hl⟩ := hs x
      exact card_pos.2 ⟨l, mem_filter.2 ⟨mem_univ l, hl⟩⟩
    rcases (show #(univ.filter fun l => s l = x) = 1 ∨ #(univ.filter fun l => s l = x) = 2 by
      have := h2 x; omega) with h1 | h2'
    · obtain ⟨l, hl⟩ := card_eq_one.1 h1
      rw [forestDist_singleton_of_card_le_one σ.isHierarchy σ.length h1.le,
        multi_pre_singleton, hl, forestDist_id_singleton hE, multi_sampledForest_pre s {x},
        multi_pre_singleton, hl]
      congr 2
      ext C
      simp [sampledForest, eq_comm]
    · obtain ⟨l₁, l₂, hne, hl⟩ := card_eq_two.1 h2'
      rw [forestDist_of_childClusters_eq_empty (σ.isHierarchy.childClusters_singleton x),
        multi_populationKernel_pre σ hs hA (by rw [multi_pre_singleton]; omega),
        multi_sampledForest_pre s {x}, multi_pre_singleton, hl]
      have hch : childClusters (extendClusters σ.clusters s) {l₁, l₂} = {{l₁}, {l₂}} :=
        hE.childClusters_eq_pair (σ.extend_singleton_mem s l₁) (σ.extend_singleton_mem s l₂)
          (disjoint_singleton.2 hne) (insert_eq l₁ {l₂}).symm
      rw [forestDist_of_childClusters_eq_pair hch (by simpa using hne)]
      simp only [forestDist_id_singleton hE, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
        Finset.sum_const_zero, Finset.sum_ite_eq', mem_univ, ite_true]
      have hsub : {{l₁}} ∪ {{l₂}} ⊆ sampledForest id ({l₁, l₂} : Finset L) := by
        intro C hC
        rcases mem_union.1 hC with hC | hC <;> rw [mem_singleton] at hC <;> subst hC <;>
          simp [singleton_mem_sampledForest]
      rw [union_eq_right.2 hsub]

/-- With at most two lineages per taxon, sampling through `s` is sampling one lineage per leaf of
the extended species tree. -/
theorem SpeciesTree.rootedDist_extend (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) (h2 : ∀ x, #(univ.filter fun l => s l = x) ≤ 2)
    (G : Finset (Finset L)) :
    σ.rootedDist s G = (σ.extend s hs).rootedDist id G := by
  unfold SpeciesTree.rootedDist
  rw [multi_forestDist_extend σ hs h2 σ.univ_mem G, multi_pre_univ]
  rfl

theorem SpeciesTree.extend_isBinary {σ : SpeciesTree X} (hσ : σ.IsBinary) {s : L → X}
    (hs : Function.Surjective s) (h2 : ∀ x, #(univ.filter fun l => s l = x) ≤ 2) :
    (σ.extend s hs).IsBinary := by
  intro B hB hB2
  change B ∈ extendClusters σ.clusters s at hB
  change ∃ C ∈ extendClusters σ.clusters s, ∃ D ∈ extendClusters σ.clusters s,
    Disjoint C D ∧ C ∪ D = B
  rcases mem_union.1 hB with hB | hB
  · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    obtain ⟨x, hx⟩ := σ.nonempty_of_mem A hA
    rcases Nat.lt_or_ge 1 #A with hA2 | hA1
    · obtain ⟨C, hC, D, hD, hCD, hCDA⟩ := hσ A hA hA2
      refine ⟨_, multi_mem_extendClusters s hC, _, multi_mem_extendClusters s hD,
        multi_pre_disjoint s hCD, ?_⟩
      rw [← hCDA, ← filter_or]
      simp only [mem_union]
    · have hAx : A = {x} :=
        eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => card_le_one.1 hA1 y hy x hx⟩
      subst hAx
      rw [multi_pre_singleton] at hB2 ⊢
      obtain ⟨l₁, l₂, hne, hl⟩ := card_eq_two.1 (le_antisymm (h2 x) hB2)
      rw [hl]
      exact ⟨{l₁}, σ.extend_singleton_mem s l₁, {l₂}, σ.extend_singleton_mem s l₂,
        disjoint_singleton.2 hne, (insert_eq l₁ {l₂}).symm⟩
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hB
    simp at hB2

/-- The extended tree determines the species tree, its internal edge lengths, and the pendant
edge lengths of the taxa sampled twice. -/
theorem SpeciesTree.sameRootedMetricTree_of_extend (hX : 2 ≤ Fintype.card X)
    (σ σ' : SpeciesTree X) {s : L → X} (hs : Function.Surjective s)
    (h : (σ.extend s hs).SameRootedMetricTree (σ'.extend s hs)) :
    σ.SameRootedMetricTree σ' ∧
      ∀ x, 2 ≤ #(univ.filter fun l => s l = x) → σ.length {x} = σ'.length {x} := by
  obtain ⟨hcl, hlen⟩ := h
  change extendClusters σ.clusters s = extendClusters σ'.clusters s at hcl
  have hmem : ∀ {τ τ' : SpeciesTree X}, extendClusters τ.clusters s = extendClusters τ'.clusters s →
      ∀ A ∈ τ.clusters, A ∈ τ'.clusters := by
    intro τ τ' hcl A hA
    have hA' : (univ.filter fun l => s l ∈ A) ∈ extendClusters τ'.clusters s :=
      hcl ▸ multi_mem_extendClusters s hA
    rcases mem_union.1 hA' with h | h
    · obtain ⟨A', hA', hA'A⟩ := mem_image.1 h
      rwa [(multi_pre_inj hs).1 hA'A] at hA'
    · obtain ⟨l, -, hl⟩ := mem_image.1 h
      rw [multi_eq_singleton_of_pre_eq hs hl]
      exact τ'.singleton_mem _
  have hcl' : σ.clusters = σ'.clusters :=
    subset_antisymm (fun A hA => hmem hcl A hA) (fun A hA => hmem hcl.symm A hA)
  have key : ∀ A ∈ σ.clusters, 2 ≤ #(univ.filter fun l => s l ∈ A) → A ≠ univ →
      σ.length A = σ'.length A := by
    intro A hA h2 hAu
    have hA' : A ∈ σ'.clusters := hcl' ▸ hA
    have := hlen _ (multi_mem_extendClusters s hA) h2 (multi_pre_ne_univ hs hAu)
    change σ.extendLength s _ = σ'.extendLength s _ at this
    rwa [multi_extendLength_pre σ hs hA h2, multi_extendLength_pre σ' hs hA' h2] at this
  refine ⟨⟨hcl', fun A hA hA2 hAu => key A hA (hA2.trans (multi_card_le_card_pre hs A)) hAu⟩,
    fun x hx => key {x} (σ.singleton_mem x) (by rwa [multi_pre_singleton]) fun hxu => ?_⟩
  have := congrArg card hxu
  rw [card_singleton, card_univ] at this
  omega

end ADR11
