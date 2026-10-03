module

public import ADR11.Coalescent.Outcome

/-!
# Basic properties of the multispecies coalescent

The recursion `ADR11.forestDist` is defined for any family of clusters `H` and any lengths; most
results here assume `H` is a hierarchy (`IsHierarchy H`) and the lengths are nonnegative.

* `enteringDist H len s A`: the distribution of the forest entering the population above `A`.
* `unrootedDistOf H len s`: the distribution of unrooted gene trees, for raw data; it is
  `SpeciesTree.unrootedDist` for a species tree.

## Main results

* `forestDist_eq_sum_entering`: `forestDist` is the entering distribution pushed through the
  population kernel.
* `forestDist_of_childClusters_eq_empty`, `forestDist_of_childClusters_eq_pair`,
  `forestDist_of_childClusters_eq_triple`: unfolding at a leaf, at a node with two children and
  at a node with three children (and the same for `enteringDist`).
* `forestDist_singleton_of_card_le_one`, `forestDist_id_singleton`: at a leaf from which at most
  one lineage is sampled, the leaving forest is the sampled forest.
* `IsHierarchy.disjoint_of_mem_childClusters`, `IsHierarchy.sup_childClusters`,
  `IsHierarchy.two_le_card_childClusters`: the children of a cluster with at least two elements
  partition it; `IsHierarchy.childClusters_eq`, `IsHierarchy.childClusters_eq_pair`,
  `IsHierarchy.childClusters_eq_triple`: recognizing the children;
  `SpeciesTree.isBinary_iff_card_childClusters`: a species tree is binary if and only if every
  such cluster has exactly two children.
* `forestDist_support`: the forest leaving the population above `A` is a forest on exactly the
  lineages sampled from `A`, containing their singletons (`enteringDist_support`: the same for the
  entering forest; `forestDist_univ_support`: above the root, it has at most one root).
* `forestDist_nonneg`, `forestDist_nonneg_of_ne_univ`, `forestDist_sum`, `forestDist_le_one`,
  `enteringDist_nonneg_of_ne_univ`, `enteringDist_sum`,
  `unrootedDistOf_nonneg`, `unrootedDistOf_sum`: probability distributions.
* `forestDist_congr_len`: only the lengths of the edges below the root matter.
* `unrootedDistOf_eq_sum_entering`: the unrooted distribution is obtained from the forest entering
  the population above the root through `unrootedOutcome`.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

/-- A hierarchy of clusters on `X`. -/
def IsHierarchy (H : Finset (Finset X)) : Prop :=
  univ ∈ H ∧ (∀ x : X, {x} ∈ H) ∧ (∀ A ∈ H, A.Nonempty) ∧
    ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

theorem SpeciesTree.isHierarchy (σ : SpeciesTree X) : IsHierarchy σ.clusters :=
  ⟨σ.univ_mem, σ.singleton_mem, σ.nonempty_of_mem, σ.laminar⟩

/-- The distribution of the forest entering the population above `A`: the union of the
independent forests leaving the populations of the children of `A`, together with the singletons
of the lineages sampled at `A`. -/
noncomputable def enteringDist (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (F : Finset (Finset L)) : ℝ :=
  ∑ f : childClusters H A → Finset (Finset L),
    if univ.sup f ∪ sampledForest s A = F then ∏ B : childClusters H A, forestDist H len s B (f B)
    else 0

/-- The distribution of unrooted gene trees for raw data `H`, `len`. -/
noncomputable def unrootedDistOf (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (T : Finset (Finset L)) : ℝ :=
  ∑ G, if unroot G = T then forestDist H len s univ G else 0

theorem SpeciesTree.unrootedDist_eq_unrootedDistOf (σ : SpeciesTree X) (s : L → X) :
    σ.unrootedDist s = unrootedDistOf σ.clusters σ.length s := rfl

theorem forestDist_eq_sum_entering (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (G : Finset (Finset L)) :
    forestDist H len s A G = ∑ F, enteringDist H len s A F * populationKernel len A F G := by
  rw [forestDist]
  unfold enteringDist
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem forestDist_of_childClusters_eq_empty {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A : Finset X} (h : childClusters H A = ∅) (G : Finset (Finset L)) :
    forestDist H len s A G = populationKernel len A (sampledForest s A) G := by
  rw [forestDist]
  have : IsEmpty (childClusters H A) := by rw [h]; infer_instance
  rw [Fintype.sum_unique]
  simp

/-- A sum over the functions on a two-element finset is a double sum. -/
private lemma msc_sum_pi_pair {ι α β : Type*} [DecidableEq ι] [Fintype α] [AddCommMonoid β]
    {T : Finset ι} {B C : ι} (h : T = {B, C}) (hBC : B ≠ C) (g : (T → α) → β) :
    ∑ f : T → α, g f = ∑ a, ∑ b, g (fun D => if D.1 = B then a else b) := by
  subst h
  let e : (({B, C} : Finset ι) → α) ≃ α × α :=
    { toFun := fun f => (f ⟨B, by simp⟩, f ⟨C, by simp⟩)
      invFun := fun p D => if D.1 = B then p.1 else p.2
      left_inv := by
        intro f
        funext ⟨D, hD⟩
        rcases mem_insert.1 hD with rfl | hD
        · simp
        · rw [mem_singleton] at hD
          subst hD
          simp [hBC.symm]
      right_inv := by
        intro p
        simp [hBC.symm] }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- A sum over the functions on a three-element finset is a triple sum. -/
private lemma msc_sum_pi_triple {ι α β : Type*} [DecidableEq ι] [Fintype α] [AddCommMonoid β]
    {T : Finset ι} {B C D : ι} (h : T = {B, C, D}) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (g : (T → α) → β) :
    ∑ f : T → α, g f =
      ∑ a, ∑ b, ∑ c, g (fun E => if E.1 = B then a else if E.1 = C then b else c) := by
  subst h
  let e : (({B, C, D} : Finset ι) → α) ≃ α × α × α :=
    { toFun := fun f => (f ⟨B, by simp⟩, f ⟨C, by simp⟩, f ⟨D, by simp⟩)
      invFun := fun p E => if E.1 = B then p.1 else if E.1 = C then p.2.1 else p.2.2
      left_inv := by
        intro f
        funext ⟨E, hE⟩
        simp only [mem_insert, mem_singleton] at hE
        rcases hE with rfl | rfl | rfl
        · simp
        · simp [hBC.symm]
        · simp [hBD.symm, hCD.symm]
      right_inv := by
        intro p
        simp [hBC.symm, hBD.symm, hCD.symm] }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rfl

theorem forestDist_of_childClusters_eq_pair {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A B C : Finset X} (h : childClusters H A = {B, C}) (hBC : B ≠ C)
    (G : Finset (Finset L)) :
    forestDist H len s A G =
      ∑ F₁, ∑ F₂, forestDist H len s B F₁ * forestDist H len s C F₂ *
        populationKernel len A (F₁ ∪ F₂ ∪ sampledForest s A) G := by
  rw [forestDist, msc_sum_pi_pair h hBC]
  refine Finset.sum_congr rfl fun F₁ _ => Finset.sum_congr rfl fun F₂ _ => ?_
  congr 1
  · rw [Finset.prod_coe_sort (childClusters H A)
      (fun D => forestDist H len s D (if D = B then F₁ else F₂)), h, prod_pair hBC]
    simp [hBC.symm]
  · congr 2
    rw [univ_eq_attach, sup_attach (childClusters H A) (fun D => if D = B then F₁ else F₂), h,
      sup_insert, sup_singleton]
    simp [hBC.symm]

/-- Unfolding at a node with three children (a polytomy). -/
theorem forestDist_of_childClusters_eq_triple {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A B C D : Finset X} (h : childClusters H A = {B, C, D}) (hBC : B ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D) (G : Finset (Finset L)) :
    forestDist H len s A G =
      ∑ F₁, ∑ F₂, ∑ F₃, forestDist H len s B F₁ * forestDist H len s C F₂ *
        forestDist H len s D F₃ * populationKernel len A (F₁ ∪ F₂ ∪ F₃ ∪ sampledForest s A) G := by
  rw [forestDist, msc_sum_pi_triple h hBC hBD hCD]
  refine Finset.sum_congr rfl fun F₁ _ => Finset.sum_congr rfl fun F₂ _ =>
    Finset.sum_congr rfl fun F₃ _ => ?_
  congr 1
  · rw [Finset.prod_coe_sort (childClusters H A)
      (fun E => forestDist H len s E (if E = B then F₁ else if E = C then F₂ else F₃)), h,
      prod_insert (by simp [hBC, hBD]), prod_pair hCD]
    simp [hBC.symm, hBD.symm, hCD.symm, mul_assoc]
  · congr 2
    rw [univ_eq_attach, sup_attach (childClusters H A)
      (fun E => if E = B then F₁ else if E = C then F₂ else F₃), h,
      sup_insert, sup_insert, sup_singleton]
    simp [hBC.symm, hBD.symm, hCD.symm, union_assoc]

theorem enteringDist_of_childClusters_eq_empty {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A : Finset X} (h : childClusters H A = ∅) (F : Finset (Finset L)) :
    enteringDist H len s A F = if F = sampledForest s A then 1 else 0 := by
  unfold enteringDist
  have : IsEmpty (childClusters H A) := by rw [h]; infer_instance
  rw [Fintype.sum_unique]
  simp [eq_comm]

theorem enteringDist_of_childClusters_eq_pair {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A B C : Finset X} (h : childClusters H A = {B, C}) (hBC : B ≠ C)
    (F : Finset (Finset L)) :
    enteringDist H len s A F =
      ∑ F₁, ∑ F₂, if F₁ ∪ F₂ ∪ sampledForest s A = F then
        forestDist H len s B F₁ * forestDist H len s C F₂ else 0 := by
  unfold enteringDist
  rw [msc_sum_pi_pair h hBC]
  refine Finset.sum_congr rfl fun F₁ _ => Finset.sum_congr rfl fun F₂ _ => ?_
  dsimp only
  rw [Finset.prod_coe_sort (childClusters H A)
      (fun D => forestDist H len s D (if D = B then F₁ else F₂)),
    univ_eq_attach, sup_attach (childClusters H A) (fun D => if D = B then F₁ else F₂),
    h, prod_pair hBC, sup_insert, sup_singleton]
  simp [hBC.symm]

theorem enteringDist_of_childClusters_eq_triple {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A B C D : Finset X} (h : childClusters H A = {B, C, D}) (hBC : B ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D) (F : Finset (Finset L)) :
    enteringDist H len s A F =
      ∑ F₁, ∑ F₂, ∑ F₃, if F₁ ∪ F₂ ∪ F₃ ∪ sampledForest s A = F then
        forestDist H len s B F₁ * forestDist H len s C F₂ * forestDist H len s D F₃ else 0 := by
  unfold enteringDist
  rw [msc_sum_pi_triple h hBC hBD hCD]
  refine Finset.sum_congr rfl fun F₁ _ => Finset.sum_congr rfl fun F₂ _ =>
    Finset.sum_congr rfl fun F₃ _ => ?_
  dsimp only
  rw [Finset.prod_coe_sort (childClusters H A)
      (fun E => forestDist H len s E (if E = B then F₁ else if E = C then F₂ else F₃)),
    univ_eq_attach, sup_attach (childClusters H A)
      (fun E => if E = B then F₁ else if E = C then F₂ else F₃), h,
    prod_insert (by simp [hBC, hBD]), prod_pair hCD, sup_insert, sup_insert, sup_singleton]
  simp [hBC.symm, hBD.symm, hCD.symm, mul_assoc, union_assoc]

theorem mem_childClusters {H : Finset (Finset X)} {A B : Finset X} :
    B ∈ childClusters H A ↔ B ∈ H ∧ B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A :=
  mem_filter

theorem childClusters_subset (H : Finset (Finset X)) (A : Finset X) : childClusters H A ⊆ H :=
  filter_subset _ _

/-- In a hierarchy, the children of a cluster with at least two elements partition it, and a
singleton has no children. -/
theorem IsHierarchy.childClusters_singleton {H : Finset (Finset X)} (hH : IsHierarchy H) (x : X) :
    childClusters H {x} = ∅ := by
  unfold childClusters
  rw [Finset.filter_eq_empty_iff]
  rintro B hB ⟨hBx, -⟩
  rw [Finset.ssubset_singleton_iff] at hBx
  subst hBx
  exact Finset.not_nonempty_empty (hH.2.2.1 _ hB)

/-- Two distinct children of a cluster of a hierarchy are disjoint. -/
theorem IsHierarchy.disjoint_of_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C : Finset X} (hB : B ∈ childClusters H A) (hC : C ∈ childClusters H A) (hBC : B ≠ C) :
    Disjoint B C := by
  rw [mem_childClusters] at hB hC
  rcases hH.2.2.2 B hB.1 C hC.1 with h | h | h
  · exact absurd hC.2.1 (hB.2.2 C hC.1 (lt_of_le_of_ne h hBC))
  · exact absurd hB.2.1 (hC.2.2 B hB.1 (lt_of_le_of_ne h hBC.symm))
  · exact h

omit [Fintype X] in
theorem mem_sampledForest {s : L → X} {A : Finset X} {C : Finset L} :
    C ∈ sampledForest s A ↔ ∃ l, s l ∈ A ∧ {l} = C := by
  simp [sampledForest]

omit [Fintype X] in
theorem singleton_mem_sampledForest {s : L → X} {A : Finset X} {l : L} :
    {l} ∈ sampledForest s A ↔ s l ∈ A := by
  rw [mem_sampledForest]
  constructor
  · rintro ⟨l', hl', h⟩
    rw [singleton_inj] at h
    exact h ▸ hl'
  · exact fun h => ⟨l, h, rfl⟩

omit [Fintype L] in
private lemma msc_singleton_laminar {C D : Finset L} {l : L} (hC : C = {l}) :
    C ⊆ D ∨ D ⊆ C ∨ Disjoint C D := by
  subst hC
  by_cases h : l ∈ D
  · exact Or.inl (singleton_subset_iff.2 h)
  · exact Or.inr (Or.inr (disjoint_singleton_left.2 h))

/-- The forest entering the population above a cluster `A` of a hierarchy, when the forests
leaving the children are forests on the lineages sampled from the children, is a forest on the
lineages sampled from `A`, containing their singletons. -/
theorem IsHierarchy.isForest_entering {H : Finset (Finset X)} (hH : IsHierarchy H) {s : L → X}
    {A : Finset X} (f : childClusters H A → Finset (Finset L))
    (hf : ∀ B, IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X))) :
    IsForest (univ.sup f ∪ sampledForest s A) ∧
      sampledForest s A ⊆ univ.sup f ∪ sampledForest s A ∧
      lineages (univ.sup f ∪ sampledForest s A) = univ.filter (fun l => s l ∈ A) := by
  have hsub : ∀ (B : childClusters H A) (C : Finset L), C ∈ f B → ∀ l ∈ C,
      s l ∈ (B : Finset X) := by
    intro B C hC l hl
    have : l ∈ lineages (f B) := mem_lineages.2 ⟨C, hC, hl⟩
    rw [(hf B).2, mem_filter] at this
    exact this.2
  have hBA : ∀ B : childClusters H A, (B : Finset X) ⊆ A :=
    fun B => (mem_childClusters.1 B.2).2.1.1
  refine ⟨⟨fun C hC => ?_, fun C hC D hD => ?_⟩, subset_union_right, ?_⟩
  · rcases mem_union.1 hC with hC | hC
    · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC
      exact (hf B).1.1 C hCB
    · exact (isForest_sampledForest s A).1 C hC
  · rcases mem_union.1 hD with hD' | hD'
    · rcases mem_union.1 hC with hC' | hC'
      · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC'
        obtain ⟨B', -, hDB'⟩ := Finset.mem_sup.1 hD'
        by_cases hBB' : B = B'
        · subst hBB'
          exact (hf B).1.2 C hCB D hDB'
        · refine Or.inr (Or.inr (Finset.disjoint_left.2 fun l hlC hlD => ?_))
          have hdis := hH.disjoint_of_mem_childClusters B.2 B'.2
            (fun h => hBB' (Subtype.ext h))
          exact Finset.disjoint_left.1 hdis (hsub B C hCB l hlC) (hsub B' D hDB' l hlD)
      · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hC'
        exact msc_singleton_laminar rfl
    · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hD'
      rcases msc_singleton_laminar (D := C) (rfl : ({l} : Finset L) = {l}) with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h.symm)
  · ext l
    rw [mem_lineages, mem_filter]
    constructor
    · rintro ⟨C, hC, hlC⟩
      refine ⟨mem_univ _, ?_⟩
      rcases mem_union.1 hC with hC | hC
      · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC
        exact hBA B (hsub B C hCB l hlC)
      · obtain ⟨l', hl', rfl⟩ := mem_sampledForest.1 hC
        rw [mem_singleton] at hlC
        exact hlC ▸ hl'
    · rintro ⟨-, h⟩
      exact ⟨{l}, mem_union_right _ (singleton_mem_sampledForest.2 h), mem_singleton_self l⟩

/-- The population kernels only add clusters to a forest and keep its lineages. -/
theorem populationKernel_support {len : Finset X → ℝ} {A : Finset X} {F G : Finset (Finset L)}
    (hF : IsForest F) (h : populationKernel len A F G ≠ 0) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F := by
  unfold populationKernel at h
  split_ifs at h with hA
  · rw [kingmanAbsorption_apply hF] at h
    split_ifs at h with h0 h1 h2
    · subst h1
      exact ⟨hF, subset_rfl, rfl⟩
    · exact absurd rfl h
    · obtain ⟨h1, h2, h3, -⟩ := jumpMatrix_pow_support hF h
      exact ⟨h1, h2, h3⟩
    · exact absurd rfl h
  · rw [kingmanTransition_apply hF] at h
    obtain ⟨h1, h2, h3, -⟩ := jumpMatrix_pow_support hF (right_ne_zero_of_mul h)
    exact ⟨h1, h2, h3⟩

theorem populationKernel_nonneg {len : Finset X → ℝ} {A : Finset X} (hlen : A ≠ univ → 0 ≤ len A)
    {F : Finset (Finset L)} (hF : IsForest F) (G : Finset (Finset L)) :
    0 ≤ populationKernel len A F G := by
  unfold populationKernel
  split_ifs with hA
  · exact kingmanAbsorption_nonneg hF G
  · exact kingmanTransition_nonneg (hlen hA) F G

theorem populationKernel_sum (len : Finset X → ℝ) (A : Finset X) {F : Finset (Finset L)}
    (hF : IsForest F) : ∑ G, populationKernel len A F G = 1 := by
  unfold populationKernel
  split_ifs with hA
  · exact kingmanAbsorption_sum hF
  · exact kingmanTransition_sum hF (len A)

/-- The forest leaving the population above a cluster `A` of a hierarchy is a forest on exactly
the lineages sampled from `A`, containing the singletons of all of them. -/
theorem forestDist_support {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hA : A ∈ H) {G : Finset (Finset L)}
    (hG : forestDist H len s A G ≠ 0) :
    IsForest G ∧ sampledForest s A ⊆ G ∧ lineages G = univ.filter (fun l => s l ∈ A) := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist] at hG
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hG
  have hprod := left_ne_zero_of_mul hf
  have hfB : ∀ B : childClusters H A,
      IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X)) := by
    intro B
    have hBmem := mem_childClusters.1 B.2
    obtain ⟨h1, -, h3⟩ := ih B hBmem.2.1 hBmem.1 (Finset.prod_ne_zero_iff.1 hprod B (mem_univ _))
    exact ⟨h1, h3⟩
  obtain ⟨hF, hSF, hLF⟩ := hH.isForest_entering f hfB
  obtain ⟨hG1, hG2, hG3⟩ := populationKernel_support hF (right_ne_zero_of_mul hf)
  exact ⟨hG1, hSF.trans hG2, hG3.trans hLF⟩

/-- Nonnegativity, assuming only that the lengths of the edges below the root are nonnegative
(the length at `univ` is irrelevant). -/
theorem forestDist_nonneg_of_ne_univ {H : Finset (Finset X)} (hH : IsHierarchy H)
    {len : Finset X → ℝ} (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X) {A : Finset X}
    (hA : A ∈ H) (G : Finset (Finset L)) : 0 ≤ forestDist H len s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist]
  refine Finset.sum_nonneg fun f _ => ?_
  by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
  · rw [hprod, zero_mul]
  · refine mul_nonneg (Finset.prod_nonneg fun B _ => ?_) ?_
    · exact ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 _
    · have hfB : ∀ B : childClusters H A,
          IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X)) := by
        intro B
        obtain ⟨h1, -, h3⟩ := forestDist_support hH len s (mem_childClusters.1 B.2).1
          (Finset.prod_ne_zero_iff.1 hprod B (mem_univ _))
        exact ⟨h1, h3⟩
      exact populationKernel_nonneg (hlen A hA) (hH.isForest_entering f hfB).1 G

theorem forestDist_nonneg {H : Finset (Finset X)} (hH : IsHierarchy H) {len : Finset X → ℝ}
    (hlen : ∀ A ∈ H, 0 ≤ len A) (s : L → X) {A : Finset X} (hA : A ∈ H)
    (G : Finset (Finset L)) : 0 ≤ forestDist H len s A G :=
  forestDist_nonneg_of_ne_univ hH (fun B hB _ => hlen B hB) s hA G

theorem forestDist_sum {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hA : A ∈ H) : ∑ G, forestDist H len s A G = 1 := by
  induction A using Finset.strongInduction with
  | H A ih =>
  have hunf : ∀ G, forestDist H len s A G = ∑ f : childClusters H A → Finset (Finset L),
      (∏ B : childClusters H A, forestDist H len s B (f B)) *
        populationKernel len A (univ.sup f ∪ sampledForest s A) G := fun G => by
    rw [forestDist]
  simp_rw [hunf]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hterm : ∀ f : childClusters H A → Finset (Finset L),
      (∏ B : childClusters H A, forestDist H len s B (f B)) *
        ∑ G, populationKernel len A (univ.sup f ∪ sampledForest s A) G =
      ∏ B : childClusters H A, forestDist H len s B (f B) := by
    intro f
    by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
    · rw [hprod, zero_mul]
    · have hfB : ∀ B : childClusters H A,
          IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X)) := by
        intro B
        obtain ⟨h1, -, h3⟩ := forestDist_support hH len s (mem_childClusters.1 B.2).1
          (Finset.prod_ne_zero_iff.1 hprod B (mem_univ _))
        exact ⟨h1, h3⟩
      rw [populationKernel_sum len A (hH.isForest_entering f hfB).1, mul_one]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (B : childClusters H A) (F : Finset (Finset L)) =>
    forestDist H len s B F)]
  exact Finset.prod_eq_one fun B _ =>
    ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1

/-- The unrooted gene tree distribution, from the forest entering the population above the root. -/
theorem unrootedDistOf_eq_sum_entering (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (T : Finset (Finset L)) :
    unrootedDistOf H len s T = ∑ F, enteringDist H len s univ F * unrootedOutcome F T := by
  unfold unrootedDistOf unrootedOutcome
  have hK : populationKernel (L := L) len (univ : Finset X) = kingmanAbsorption :=
    ite_eq_left rfl
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [forestDist_eq_sum_entering, hK]
  split_ifs <;> simp

/-! ### The entering distribution -/

/-- The forest entering the population above a cluster `A` of a hierarchy is a forest on exactly
the lineages sampled from `A`, containing the singletons of all of them. -/
theorem enteringDist_support {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} {F : Finset (Finset L)} (hF : enteringDist H len s A F ≠ 0) :
    IsForest F ∧ sampledForest s A ⊆ F ∧ lineages F = univ.filter (fun l => s l ∈ A) := by
  unfold enteringDist at hF
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hF
  split_ifs at hf with hfF
  · subst hfF
    refine hH.isForest_entering f fun B => ?_
    have hBmem := mem_childClusters.1 B.2
    obtain ⟨h1, -, h3⟩ := forestDist_support hH len s hBmem.1
      (Finset.prod_ne_zero_iff.1 hf B (mem_univ _))
    exact ⟨h1, h3⟩
  · exact absurd rfl hf

/-- The forest leaving the population above the root is a forest on all the lineages with at
most one root (a single rooted gene tree, when some lineage is sampled). -/
theorem forestDist_univ_support {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (s : L → X) {G : Finset (Finset L)}
    (hG : forestDist H len s univ G ≠ 0) :
    IsForest G ∧ sampledForest s univ ⊆ G ∧ lineages G = univ ∧ #(roots G) ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := forestDist_support hH len s hH.1 hG
  refine ⟨h1, h2, by simpa using h3, ?_⟩
  rw [forestDist_eq_sum_entering] at hG
  obtain ⟨F, -, hF⟩ := exists_ne_zero_of_sum_ne_zero hG
  have hFf := (enteringDist_support hH len s (left_ne_zero_of_mul hF)).1
  have hK := right_ne_zero_of_mul hF
  rw [populationKernel, ite_eq_left rfl, kingmanAbsorption_apply hFf] at hK
  split_ifs at hK with h0 hGF h1
  · rw [hGF, h0]
    exact Nat.zero_le 1
  · exact absurd rfl hK
  · rw [h1]
  · exact absurd rfl hK

theorem enteringDist_nonneg_of_ne_univ {H : Finset (Finset X)} (hH : IsHierarchy H)
    {len : Finset X → ℝ} (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X) (A : Finset X)
    (F : Finset (Finset L)) : 0 ≤ enteringDist H len s A F := by
  unfold enteringDist
  refine Finset.sum_nonneg fun f _ => ?_
  split_ifs
  · exact Finset.prod_nonneg fun B _ =>
      forestDist_nonneg_of_ne_univ hH hlen s (mem_childClusters.1 B.2).1 _
  · exact le_rfl

theorem enteringDist_sum {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) (A : Finset X) : ∑ F, enteringDist H len s A F = 1 := by
  unfold enteringDist
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq, mem_univ, ite_true]
  rw [← Fintype.prod_sum (fun (B : childClusters H A) (F : Finset (Finset L)) =>
    forestDist H len s B F)]
  exact Finset.prod_eq_one fun B _ => forestDist_sum hH len s (mem_childClusters.1 B.2).1

/-! ### The children of a cluster of a hierarchy -/

/-- Every element of a cluster `A` with at least two elements lies in a child of `A`. -/
theorem IsHierarchy.exists_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) {x : X} (hx : x ∈ A) : ∃ B ∈ childClusters H A, x ∈ B := by
  have hxA : ({x} : Finset X) ⊂ A := by
    refine (singleton_subset_iff.2 hx).ssubset_of_ne ?_
    rintro rfl
    simp at hA
  obtain ⟨B, hB, hmax⟩ := (H.filter fun C => x ∈ C ∧ C ⊂ A).exists_max_image card
    ⟨{x}, mem_filter.2 ⟨hH.2.1 x, mem_singleton_self x, hxA⟩⟩
  rw [mem_filter] at hB
  refine ⟨B, mem_childClusters.2 ⟨hB.1, hB.2.2, fun C hC hBC hCA => ?_⟩, hB.2.1⟩
  have := hmax C (mem_filter.2 ⟨hC, hBC.subset hB.2.1, hCA⟩)
  exact absurd (card_lt_card hBC) (not_lt.2 this)

/-- The children of a cluster `A` with at least two elements cover it. -/
theorem IsHierarchy.sup_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) : (childClusters H A).sup id = A := by
  refine le_antisymm (Finset.sup_le fun B hB => (mem_childClusters.1 hB).2.1.subset) ?_
  intro x hx
  obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters hA hx
  exact Finset.mem_sup.2 ⟨B, hB, hxB⟩

/-- The children of a cluster are pairwise disjoint. -/
theorem IsHierarchy.pairwiseDisjoint_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    (A : Finset X) : (childClusters H A : Set (Finset X)).PairwiseDisjoint id :=
  fun _ hB _ hC hBC => hH.disjoint_of_mem_childClusters hB hC hBC

/-- A cluster with at least two elements has at least two children. -/
theorem IsHierarchy.two_le_card_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) : 2 ≤ #(childClusters H A) := by
  by_contra hlt
  have hle : #(childClusters H A) ≤ 1 := by omega
  obtain ⟨x, hx⟩ : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨B, hB, -⟩ := hH.exists_mem_childClusters hA hx
  rw [Finset.card_le_one_iff] at hle
  have hAB : A ⊆ B := fun y hy => by
    obtain ⟨C, hC, hyC⟩ := hH.exists_mem_childClusters hA hy
    exact hle hC hB ▸ hyC
  exact not_subset_of_ssubset (mem_childClusters.1 hB).2.1 hAB

/-- A characterization of the children: a family `T ⊆ H` of at least two pairwise disjoint
clusters covering `A`, such that every cluster of `H` strictly inside `A` lies inside one of
them, is the family of children of `A`. -/
theorem IsHierarchy.childClusters_eq {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} {T : Finset (Finset X)} (hT : T ⊆ H)
    (hdisj : (T : Set (Finset X)).PairwiseDisjoint id) (hsup : T.sup id = A) (h2 : 2 ≤ #T)
    (hcov : ∀ E ∈ H, E ⊂ A → ∃ B ∈ T, E ⊆ B) : childClusters H A = T := by
  have hsubA : ∀ B ∈ T, B ⊆ A := fun B hB => hsup ▸ le_sup (f := id) hB
  have hssubA : ∀ B ∈ T, B ⊂ A := by
    intro B hB
    refine (hsubA B hB).ssubset_of_ne ?_
    rintro rfl
    obtain ⟨C, hC, hCB⟩ := exists_mem_ne (by omega : 1 < #T) B
    have hdis : Disjoint C B := hdisj hC hB hCB
    obtain ⟨y, hy⟩ := hH.2.2.1 C (hT hC)
    exact Finset.disjoint_left.1 hdis hy (hsubA C hC hy)
  have heq : ∀ B ∈ T, ∀ B' ∈ T, ∀ E ∈ H, B ⊆ E → E ⊆ B' → B = B' := by
    intro B hB B' hB' E hE hBE hEB'
    by_contra hne
    obtain ⟨y, hy⟩ := hH.2.2.1 B (hT hB)
    exact Finset.disjoint_left.1 (hdisj hB hB' hne) hy (hEB' (hBE hy))
  ext B
  constructor
  · intro hB
    obtain ⟨hBH, hBA, hmax⟩ := mem_childClusters.1 hB
    obtain ⟨B', hB', hBB'⟩ := hcov B hBH hBA
    rcases hBB'.eq_or_ssubset with h | h
    · exact h ▸ hB'
    · exact absurd (hssubA B' hB') (hmax B' (hT hB') h)
  · intro hB
    refine mem_childClusters.2 ⟨hT hB, hssubA B hB, fun C hC hBC hCA => ?_⟩
    obtain ⟨B', hB', hCB'⟩ := hcov C hC hCA
    have := heq B hB B' hB' C hC hBC.subset hCB'
    subst this
    exact absurd (hBC.trans_le hCB') (lt_irrefl _)

/-- Two disjoint clusters whose union is `A` are the children of `A`. -/
theorem IsHierarchy.childClusters_eq_pair {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C : Finset X} (hB : B ∈ H) (hC : C ∈ H) (hBC : Disjoint B C) (hA : B ∪ C = A) :
    childClusters H A = {B, C} := by
  obtain ⟨b, hb⟩ := hH.2.2.1 B hB
  have hne : B ≠ C := by
    rintro rfl
    exact Finset.disjoint_left.1 hBC hb hb
  refine hH.childClusters_eq (by simp [insert_subset_iff, hB, hC]) ?_ (by simp [hA]) ?_ ?_
  · intro P hP Q hQ hPQ
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hP hQ
    rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
    · exact absurd rfl hPQ
    · exact hBC
    · exact hBC.symm
    · exact absurd rfl hPQ
  · rw [card_pair hne]
  · intro E hE hEA
    simp only [mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left]
    by_cases hEC : Disjoint E C
    · left
      intro y hy
      have := hEA.subset hy
      rw [← hA, mem_union] at this
      exact this.resolve_right (Finset.disjoint_left.1 hEC hy)
    by_cases hEB : Disjoint E B
    · right
      intro y hy
      have := hEA.subset hy
      rw [← hA, mem_union] at this
      exact this.resolve_left (Finset.disjoint_left.1 hEB hy)
    exfalso
    obtain ⟨y, hyE, hyB⟩ := Finset.not_disjoint_iff.1 hEB
    obtain ⟨z, hzE, hzC⟩ := Finset.not_disjoint_iff.1 hEC
    have hBE : B ⊆ E := by
      rcases hH.2.2.2 E hE B hB with h | h | h
      · exact absurd (h hzE) (Finset.disjoint_right.1 hBC hzC)
      · exact h
      · exact absurd hyB (Finset.disjoint_left.1 h hyE)
    have hCE : C ⊆ E := by
      rcases hH.2.2.2 E hE C hC with h | h | h
      · exact absurd (h hyE) (Finset.disjoint_left.1 hBC hyB)
      · exact h
      · exact absurd hzC (Finset.disjoint_left.1 h hzE)
    exact not_subset_of_ssubset hEA (hA ▸ union_subset hBE hCE)

/-- Three pairwise disjoint clusters whose union is `A`, no two of which have a union in the
hierarchy, are the children of `A`. -/
theorem IsHierarchy.childClusters_eq_triple {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C D : Finset X} (hB : B ∈ H) (hC : C ∈ H) (hD : D ∈ H) (hBC : Disjoint B C)
    (hBD : Disjoint B D) (hCD : Disjoint C D) (hA : B ∪ C ∪ D = A) (hBC' : B ∪ C ∉ H)
    (hBD' : B ∪ D ∉ H) (hCD' : C ∪ D ∉ H) : childClusters H A = {B, C, D} := by
  have hne : ∀ {P Q : Finset X}, P ∈ H → Disjoint P Q → P ≠ Q := by
    intro P Q hP hPQ h
    subst h
    obtain ⟨y, hy⟩ := hH.2.2.1 P hP
    exact Finset.disjoint_left.1 hPQ hy hy
  have hBC0 := hne hB hBC
  have hBD0 := hne hB hBD
  have hCD0 := hne hC hCD
  refine hH.childClusters_eq (by simp [insert_subset_iff, hB, hC, hD]) ?_ ?_ ?_ ?_
  · intro P hP Q hQ hPQ
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hP hQ
    rcases hP with rfl | rfl | rfl <;> rcases hQ with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hPQ
      | exact hBC | exact hBC.symm | exact hBD | exact hBD.symm | exact hCD | exact hCD.symm
  · simp [← hA, union_assoc]
  · rw [card_insert_of_notMem (by simp [hBC0, hBD0]), card_pair hCD0]
    omega
  · intro E hE hEA
    simp only [mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left]
    by_contra hcon
    rw [not_or, not_or] at hcon
    have key : ∀ P ∈ H, ¬ E ⊆ P → P ⊆ E ∨ Disjoint E P := fun P hP h => by
      rcases hH.2.2.2 E hE P hP with h' | h' | h'
      · exact absurd h' h
      · exact Or.inl h'
      · exact Or.inr h'
    have hEsub : ∀ x ∈ E, x ∈ B ∨ x ∈ C ∨ x ∈ D := fun x hx => by
      have := hEA.subset hx
      rw [← hA] at this
      simpa [or_assoc] using this
    obtain ⟨y, hy⟩ := hH.2.2.1 E hE
    rcases key B hB hcon.1 with hB' | hB' <;> rcases key C hC hcon.2.1 with hC' | hC' <;>
      rcases key D hD hcon.2.2 with hD' | hD'
    · exact not_subset_of_ssubset hEA (hA ▸ union_subset (union_subset hB' hC') hD')
    · refine hBC' ?_
      have : E = B ∪ C := by
        ext x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · rcases hEsub x hx with h | h | h
          · exact mem_union_left _ h
          · exact mem_union_right _ h
          · exact absurd h (Finset.disjoint_left.1 hD' hx)
        · rcases mem_union.1 hx with h | h
          · exact hB' h
          · exact hC' h
      exact this ▸ hE
    · refine hBD' ?_
      have : E = B ∪ D := by
        ext x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · rcases hEsub x hx with h | h | h
          · exact mem_union_left _ h
          · exact absurd h (Finset.disjoint_left.1 hC' hx)
          · exact mem_union_right _ h
        · rcases mem_union.1 hx with h | h
          · exact hB' h
          · exact hD' h
      exact this ▸ hE
    · refine hcon.1 fun x hx => ?_
      rcases hEsub x hx with h | h | h
      · exact h
      · exact absurd h (Finset.disjoint_left.1 hC' hx)
      · exact absurd h (Finset.disjoint_left.1 hD' hx)
    · refine hCD' ?_
      have : E = C ∪ D := by
        ext x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · rcases hEsub x hx with h | h | h
          · exact absurd h (Finset.disjoint_left.1 hB' hx)
          · exact mem_union_left _ h
          · exact mem_union_right _ h
        · rcases mem_union.1 hx with h | h
          · exact hC' h
          · exact hD' h
      exact this ▸ hE
    · refine hcon.2.1 fun x hx => ?_
      rcases hEsub x hx with h | h | h
      · exact absurd h (Finset.disjoint_left.1 hB' hx)
      · exact h
      · exact absurd h (Finset.disjoint_left.1 hD' hx)
    · refine hcon.2.2 fun x hx => ?_
      rcases hEsub x hx with h | h | h
      · exact absurd h (Finset.disjoint_left.1 hB' hx)
      · exact absurd h (Finset.disjoint_left.1 hC' hx)
      · exact h
    · rcases hEsub y hy with h | h | h
      · exact Finset.disjoint_left.1 hB' hy h
      · exact Finset.disjoint_left.1 hC' hy h
      · exact Finset.disjoint_left.1 hD' hy h

/-- A species tree is binary if and only if every cluster with at least two taxa has exactly two
children. -/
theorem SpeciesTree.isBinary_iff_card_childClusters (σ : SpeciesTree X) :
    σ.IsBinary ↔ ∀ A ∈ σ.clusters, 2 ≤ #A → #(childClusters σ.clusters A) = 2 := by
  constructor
  · intro hb A hA hA2
    obtain ⟨B, hB, C, hC, hBC, hBCA⟩ := hb A hA hA2
    rw [σ.isHierarchy.childClusters_eq_pair hB hC hBC hBCA]
    refine card_pair fun h => ?_
    subst h
    obtain ⟨y, hy⟩ := σ.nonempty_of_mem B hB
    exact Finset.disjoint_left.1 hBC hy hy
  · intro h A hA hA2
    obtain ⟨B, C, hBC, hch⟩ := card_eq_two.1 (h A hA hA2)
    have hB : B ∈ childClusters σ.clusters A := hch ▸ mem_insert_self _ _
    have hC : C ∈ childClusters σ.clusters A := hch ▸ mem_insert_of_mem (mem_singleton_self _)
    refine ⟨B, (mem_childClusters.1 hB).1, C, (mem_childClusters.1 hC).1,
      σ.isHierarchy.disjoint_of_mem_childClusters hB hC hBC, ?_⟩
    have := σ.isHierarchy.sup_childClusters hA2
    rwa [hch, sup_insert, sup_singleton] at this

/-- In a binary species tree, a cluster with at least two taxa has two children. -/
theorem SpeciesTree.IsBinary.exists_childClusters_eq_pair {σ : SpeciesTree X} (hσ : σ.IsBinary)
    {A : Finset X} (hA : A ∈ σ.clusters) (hA2 : 2 ≤ #A) :
    ∃ B C, B ≠ C ∧ childClusters σ.clusters A = {B, C} :=
  card_eq_two.1 ((σ.isBinary_iff_card_childClusters.1 hσ) A hA hA2)

/-! ### Leaves -/

/-- At a leaf `{x}` from which at most one lineage is sampled, the forest leaving the population
is the sampled forest, whatever the length of the pendant edge. -/
theorem forestDist_singleton_of_card_le_one {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {s : L → X} {x : X} (hx : #(univ.filter fun l => s l = x) ≤ 1)
    (G : Finset (Finset L)) :
    forestDist H len s {x} G = if G = sampledForest s {x} then 1 else 0 := by
  rw [forestDist_of_childClusters_eq_empty (hH.childClusters_singleton x)]
  have hF := isForest_sampledForest s ({x} : Finset X)
  have hk : #(roots (sampledForest s {x})) ≤ 1 := by
    refine (card_le_card (roots_subset _)).trans (card_image_le.trans ?_)
    simpa using hx
  by_cases hxu : ({x} : Finset X) = univ
  · rw [populationKernel, ite_eq_left hxu, kingmanAbsorption_apply hF]
    by_cases h0 : #(roots (sampledForest s {x})) = 0
    · rw [ite_eq_left h0]
    · have h1 : #(roots (sampledForest s {x})) = 1 := by omega
      rw [ite_eq_right h0, h1, Nat.sub_self, pow_zero, Matrix.one_apply]
      by_cases hG : G = sampledForest s {x}
      · subst hG
        simp [h1]
      · simp [hG, Ne.symm hG]
  · rw [populationKernel, ite_eq_right hxu]
    exact kingmanTransition_of_card_roots_le_one hF hk _ G

theorem sampledForest_id (A : Finset X) :
    sampledForest (id : X → X) A = A.image fun x => {x} := by
  ext C
  simp [sampledForest]

/-- With one lineage per taxon, the forest leaving the population above a leaf `{x}` is the
single lineage `{x}`. -/
theorem forestDist_id_singleton {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (x : X) (G : Finset (Finset X)) :
    forestDist H len id {x} G = if G = {{x}} then 1 else 0 := by
  have hS : sampledForest (id : X → X) {x} = {{x}} := by
    ext C
    simp [sampledForest, eq_comm]
  rw [forestDist_singleton_of_card_le_one hH len (by simp [Finset.filter_eq']) G, hS]

/-! ### Dependence on the lengths -/

/-- `forestDist` depends on the lengths only through the edges below the root. -/
theorem forestDist_congr_len {H : Finset (Finset X)} {len len' : Finset X → ℝ}
    (hlen : ∀ A ∈ H, A ≠ univ → len A = len' A) (s : L → X) {A : Finset X} (hA : A ∈ H)
    (G : Finset (Finset L)) : forestDist H len s A G = forestDist H len' s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist.eq_1 H len, forestDist.eq_1 H len']
  have hK : populationKernel (L := L) len A = populationKernel len' A := by
    unfold populationKernel
    split_ifs with hAu
    · rfl
    · rw [hlen A hA hAu]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hK]
  congr 1
  exact Finset.prod_congr rfl fun B _ =>
    ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 _

/-! ### Species trees: probability distributions -/

theorem SpeciesTree.forestDist_nonneg_of_mem (σ : SpeciesTree X) (s : L → X) {A : Finset X}
    (hA : A ∈ σ.clusters) (G : Finset (Finset L)) :
    0 ≤ forestDist σ.clusters σ.length s A G :=
  forestDist_nonneg_of_ne_univ σ.isHierarchy (fun B hB hBu => (σ.length_pos B hB hBu).le) s hA G

theorem SpeciesTree.forestDist_sum_eq_one (σ : SpeciesTree X) (s : L → X) {A : Finset X}
    (hA : A ∈ σ.clusters) : ∑ G, forestDist σ.clusters σ.length s A G = 1 :=
  forestDist_sum σ.isHierarchy σ.length s hA

theorem forestDist_le_one {H : Finset (Finset X)} (hH : IsHierarchy H) {len : Finset X → ℝ}
    (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X) {A : Finset X} (hA : A ∈ H)
    (G : Finset (Finset L)) : forestDist H len s A G ≤ 1 := by
  rw [← forestDist_sum hH len s hA]
  exact Finset.single_le_sum (fun G _ => forestDist_nonneg_of_ne_univ hH hlen s hA G)
    (mem_univ G)

theorem unrootedDistOf_nonneg {H : Finset (Finset X)} (hH : IsHierarchy H) {len : Finset X → ℝ}
    (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X) (T : Finset (Finset L)) :
    0 ≤ unrootedDistOf H len s T := by
  unfold unrootedDistOf
  refine Finset.sum_nonneg fun G _ => ?_
  split_ifs
  · exact forestDist_nonneg_of_ne_univ hH hlen s hH.1 G
  · exact le_rfl

theorem unrootedDistOf_sum {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) : ∑ T, unrootedDistOf H len s T = 1 := by
  unfold unrootedDistOf
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq, mem_univ, ite_true]
  exact forestDist_sum hH len s hH.1

end ADR11
