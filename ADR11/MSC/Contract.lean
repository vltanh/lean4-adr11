module

public import ADR11.MSC.Basic

/-!
# Contracting edges of length zero, and continuity in the edge lengths

Section 5 of the paper obtains the probabilities of gene trees under a nonbinary species tree as
the limits of those under a binary resolution, as the lengths of the added edges tend to `0`. This
file provides the two ingredients, for the recursion `forestDist` on any hierarchy: an edge of
length `0` can be contracted, and the distributions are continuous in the edge lengths.

## Main results

* `childClusters_erase_of_notMem`, `IsHierarchy.childClusters_erase_of_mem`: the children of a
  cluster `A` after removing a cluster `D` from the family; if `D` is a child of `A`, the children
  of `D` replace it. `IsHierarchy.erase`: removing a cluster other than `univ` and the singletons
  from a hierarchy gives a hierarchy.
* `forestDist_erase_of_len_eq_zero`: **contraction.** Removing from a hierarchy a cluster
  `D ≠ univ` whose edge has length `0` does not change the multispecies coalescent.
* `forestDist_eq_of_subset_of_len_eq_zero`, `unrootedDistOf_eq_of_subset_of_len_eq_zero`: a
  hierarchy `H` refining a hierarchy `H₀`, with lengths `0` on the edges above the clusters of
  `H` not in `H₀`, gives the same distributions as `H₀`.
* `SpeciesTree.forestDist_eq_of_subset`, `SpeciesTree.rootedDist_eq_of_subset`,
  `SpeciesTree.unrootedDist_eq_of_subset`: the same for a species tree `σ` and a refinement `H`
  of its hierarchy (for example a binary resolution), with the lengths of `σ` on its edges.
* `continuous_kingmanTransition_apply`, `continuous_forestDist`, `continuous_unrootedDistOf`: the
  distributions depend continuously on the edge lengths.
* `SpeciesTree.tendsto_unrootedDistOf`: the unrooted gene tree distribution of `σ` is the limit of
  those of a refinement `H`, with lengths `ε → 0` on the added edges.

## Implementation notes

The sum over the functions on the children of a cluster in `forestDist` is handled through the
auxiliary `contract_sum T φ w`, the expectation of `w` of the union of independent random forests
indexed by `T`; a sum over the functions on a disjoint union is an iterated sum
(`Equiv.piFinsetUnion`). Continuity of `t ↦ exp (t • Q)` uses the `L∞` operator norm on matrices,
opened locally as in `ADR11.Coalescent.Factorization`.
-/

@[expose] public section

namespace ADR11

open Finset

/-! ### Sums over the functions on a family of clusters -/

section Sums

variable {ι : Type*} [DecidableEq ι] {L : Type*} [Fintype L] [DecidableEq L]

/-- The expectation of `w` of the union of independent random forests, one for each index `B` in
`T`, with distribution `φ B`. -/
private noncomputable def contract_sum (T : Finset ι) (φ : ι → Finset (Finset L) → ℝ)
    (w : Finset (Finset L) → ℝ) : ℝ :=
  ∑ f : T → Finset (Finset L), (∏ B : T, φ B (f B)) * w (univ.sup f)

private theorem contract_sum_congr {T : Finset ι} {φ φ' : ι → Finset (Finset L) → ℝ}
    {w w' : Finset (Finset L) → ℝ} (hφ : ∀ B ∈ T, φ B = φ' B) (hw : ∀ F, w F = w' F) :
    contract_sum T φ w = contract_sum T φ' w' := by
  unfold contract_sum
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hw]
  congr 1
  exact Finset.prod_congr rfl fun B _ => by rw [hφ B B.2]

private theorem contract_sum_mul (T : Finset ι) (φ : ι → Finset (Finset L) → ℝ)
    (w : Finset (Finset L) → ℝ) (c : ℝ) :
    contract_sum T φ w * c = contract_sum T φ (fun F => w F * c) := by
  unfold contract_sum
  rw [Finset.sum_mul]
  simp_rw [mul_assoc]

private theorem contract_sum_sum {κ : Type*} (S : Finset κ) (T : Finset ι)
    (φ : ι → Finset (Finset L) → ℝ) (w : κ → Finset (Finset L) → ℝ) :
    ∑ k ∈ S, contract_sum T φ (w k) = contract_sum T φ (fun F => ∑ k ∈ S, w k F) := by
  unfold contract_sum
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

private theorem contract_sum_singleton (D : ι) (φ : ι → Finset (Finset L) → ℝ)
    (w : Finset (Finset L) → ℝ) : contract_sum {D} φ w = ∑ x, φ D x * w x := by
  unfold contract_sum
  let e : Finset (Finset L) ≃ (({D} : Finset ι) → Finset (Finset L)) :=
    { toFun := fun x _ => x
      invFun := fun f => f ⟨D, mem_singleton_self D⟩
      left_inv := fun x => rfl
      right_inv := fun f => by
        funext ⟨B, hB⟩
        rw [mem_singleton] at hB
        subst hB
        rfl }
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : ∏ B : ({D} : Finset ι), φ B (e x B) = φ D x := by
    rw [Fintype.prod_unique]
    rfl
  have h2 : univ.sup (e x) = x := Finset.sup_const univ_nonempty x
  rw [h1, h2]

/-- A sum over the functions on a disjoint union is an iterated sum. -/
private theorem contract_sum_union {T₁ T₂ : Finset ι} (h : Disjoint T₁ T₂)
    (φ : ι → Finset (Finset L) → ℝ) (w : Finset (Finset L) → ℝ) :
    contract_sum (T₁ ∪ T₂) φ w =
      contract_sum T₁ φ (fun F₁ => contract_sum T₂ φ (fun F₂ => w (F₁ ∪ F₂))) := by
  unfold contract_sum
  rw [← (Equiv.piFinsetUnion (fun _ : ι => Finset (Finset L)) h).sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun f₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f₂ _ => ?_
  set g := Equiv.piFinsetUnion (fun _ : ι => Finset (Finset L)) h (f₁, f₂) with hg
  have hl : ∀ (B : ι) (hB : B ∈ T₁), g ⟨B, mem_union_left _ hB⟩ = f₁ ⟨B, hB⟩ :=
    fun B hB => Equiv.piFinsetUnion_left _ h hB _
  have hr : ∀ (B : ι) (hB : B ∈ T₂), g ⟨B, mem_union_right _ hB⟩ = f₂ ⟨B, hB⟩ :=
    fun B hB => Equiv.piFinsetUnion_right _ h hB _
  have hprod : ∏ B : ↥(T₁ ∪ T₂), φ B (g B) =
      (∏ B : T₁, φ B (f₁ B)) * ∏ B : T₂, φ B (f₂ B) := by
    rw [← Fintype.prod_equiv (Equiv.Finset.union T₁ T₂ h)
      (fun x => φ (Equiv.Finset.union T₁ T₂ h x) (g (Equiv.Finset.union T₁ T₂ h x))) _
      (fun _ => rfl), Fintype.prod_sum_type]
    congr 1
    · refine Finset.prod_congr rfl fun B _ => ?_
      rw [Equiv.Finset.union_inl, hl B B.2]
    · refine Finset.prod_congr rfl fun B _ => ?_
      rw [Equiv.Finset.union_inr, hr B B.2]
  have hsup : univ.sup g = univ.sup f₁ ∪ univ.sup f₂ := by
    ext C
    simp only [mem_union, Finset.mem_sup, mem_univ, true_and]
    constructor
    · rintro ⟨⟨B, hB⟩, hC⟩
      rcases mem_union.1 hB with hB1 | hB2
      · exact Or.inl ⟨⟨B, hB1⟩, by rwa [← hl B hB1]⟩
      · exact Or.inr ⟨⟨B, hB2⟩, by rwa [← hr B hB2]⟩
    · rintro (⟨⟨B, hB⟩, hC⟩ | ⟨⟨B, hB⟩, hC⟩)
      · exact ⟨⟨B, mem_union_left _ hB⟩, by rwa [hl B hB]⟩
      · exact ⟨⟨B, mem_union_right _ hB⟩, by rwa [hr B hB]⟩
  rw [hprod, hsup, mul_assoc]

end Sums

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

/-! ### Children after removing a cluster -/

/-- Removing a cluster `D` that is not a child of `A` does not change the children of `A`. -/
theorem childClusters_erase_of_notMem {H : Finset (Finset X)} {A D : Finset X}
    (hD : D ∉ childClusters H A) : childClusters (H.erase D) A = childClusters H A := by
  ext E
  rw [mem_childClusters, mem_childClusters]
  constructor
  · rintro ⟨hE, hEA, hmax⟩
    refine ⟨mem_of_mem_erase hE, hEA, fun C hC hEC hCA => ?_⟩
    by_cases hCD : C = D
    · subst hCD
      have hex : ∃ C' ∈ H, C ⊂ C' ∧ C' ⊂ A := by
        by_contra hno
        exact hD (mem_childClusters.2 ⟨hC, hCA, fun C' hC' h1 h2 => hno ⟨C', hC', h1, h2⟩⟩)
      obtain ⟨C', hC', h1, h2⟩ := hex
      exact hmax C' (mem_erase.2 ⟨(ne_of_ssubset h1).symm, hC'⟩) (hEC.trans h1) h2
    · exact hmax C (mem_erase.2 ⟨hCD, hC⟩) hEC hCA
  · rintro ⟨hE, hEA, hmax⟩
    refine ⟨mem_erase.2 ⟨?_, hE⟩, hEA, fun C hC => hmax C (mem_of_mem_erase hC)⟩
    rintro rfl
    exact hD (mem_childClusters.2 ⟨hE, hEA, hmax⟩)

/-- If `D` is a child of `A` in a hierarchy, removing `D` makes the children of `D` children of
`A`. -/
theorem IsHierarchy.childClusters_erase_of_mem {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A D : Finset X} (hD : D ∈ childClusters H A) :
    childClusters (H.erase D) A = childClusters H D ∪ (childClusters H A).erase D := by
  obtain ⟨hDH, hDA, hDmax⟩ := mem_childClusters.1 hD
  ext E
  rw [mem_union, mem_erase (s := childClusters H A), mem_childClusters, mem_childClusters,
    mem_childClusters]
  constructor
  · rintro ⟨hE, hEA, hmax⟩
    obtain ⟨hED, hEH⟩ := mem_erase.1 hE
    by_cases hc : ∃ C ∈ H, E ⊂ C ∧ C ⊂ A
    · obtain ⟨C, hC, hEC, hCA⟩ := hc
      have hCD : C = D := by
        by_contra hne
        exact hmax C (mem_erase.2 ⟨hne, hC⟩) hEC hCA
      refine Or.inl ⟨hEH, hCD ▸ hEC, fun C' hC' h1 h2 => ?_⟩
      exact hmax C' (mem_erase.2 ⟨ne_of_ssubset h2, hC'⟩) h1 (h2.trans hDA)
    · exact Or.inr ⟨hED, hEH, hEA, fun C hC hEC hCA => hc ⟨C, hC, hEC, hCA⟩⟩
  · rintro (⟨hEH, hED, hmax⟩ | ⟨hED, hEH, hEA, hmax⟩)
    · refine ⟨mem_erase.2 ⟨ne_of_ssubset hED, hEH⟩, hED.trans hDA, fun C hC hEC hCA => ?_⟩
      obtain ⟨hCD, hCH⟩ := mem_erase.1 hC
      obtain ⟨e, he⟩ := hH.2.2.1 E hEH
      rcases hH.2.2.2 C hCH D hDH with h | h | h
      · exact hmax C hCH hEC (lt_of_le_of_ne h hCD)
      · exact hDmax C hCH (lt_of_le_of_ne h (Ne.symm hCD)) hCA
      · exact Finset.disjoint_left.1 h (hEC.subset he) (hED.subset he)
    · exact ⟨mem_erase.2 ⟨hED, hEH⟩, hEA, fun C hC => hmax C (mem_of_mem_erase hC)⟩

/-- Removing a cluster other than `univ` and the singletons from a hierarchy gives a hierarchy. -/
theorem IsHierarchy.erase {H : Finset (Finset X)} (hH : IsHierarchy H) {D : Finset X}
    (hDu : D ≠ univ) (hDx : ∀ x, D ≠ {x}) : IsHierarchy (H.erase D) :=
  ⟨mem_erase.2 ⟨hDu.symm, hH.1⟩, fun x => mem_erase.2 ⟨(hDx x).symm, hH.2.1 x⟩,
    fun A hA => hH.2.2.1 A (mem_of_mem_erase hA),
    fun A hA B hB => hH.2.2.2 A (mem_of_mem_erase hA) B (mem_of_mem_erase hB)⟩

omit [Fintype X] in
/-- The sampled forest is monotone in the cluster. -/
theorem sampledForest_mono (s : L → X) {A B : Finset X} (h : A ⊆ B) :
    sampledForest s A ⊆ sampledForest s B := by
  intro C hC
  obtain ⟨l, hl, rfl⟩ := mem_sampledForest.1 hC
  exact mem_sampledForest.2 ⟨l, h hl, rfl⟩

/-! ### Contraction of an edge of length zero -/

private theorem contract_forestDist_eq (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (G : Finset (Finset L)) :
    forestDist H len s A G = contract_sum (childClusters H A) (forestDist H len s)
      (fun F => populationKernel len A (F ∪ sampledForest s A) G) := by
  rw [forestDist]
  rfl

/-- **Contraction of an edge of length `0`.** Removing from a hierarchy a cluster `D ≠ univ` whose
edge has length `0` does not change the multispecies coalescent: the population above `D` lets the
union of the forests leaving the children of `D` pass unchanged into the population above the
parent of `D`. (If `D` is a singleton, `H.erase D` is no longer a hierarchy, but the identity still
holds.) -/
theorem forestDist_erase_of_len_eq_zero {H : Finset (Finset X)} (hH : IsHierarchy H)
    {len : Finset X → ℝ} {D : Finset X} (hDu : D ≠ univ) (hlen : len D = 0) (s : L → X)
    (A : Finset X) (G : Finset (Finset L)) :
    forestDist (H.erase D) len s A G = forestDist H len s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  have ih' : ∀ B ∈ childClusters (H.erase D) A,
      forestDist (H.erase D) len s B = forestDist H len s B :=
    fun B hB => funext fun G => ih B (mem_childClusters.1 hB).2.1 G
  rw [contract_forestDist_eq, contract_forestDist_eq H]
  refine (contract_sum_congr ih' fun _ => rfl).trans ?_
  by_cases hD : D ∈ childClusters H A
  · -- `D` is a child of `A`: the children of `D` replace it
    have hDA : D ⊆ A := (mem_childClusters.1 hD).2.1.subset
    have hdisj : Disjoint (childClusters H D) ((childClusters H A).erase D) := by
      refine Finset.disjoint_left.2 fun E hE hE' => ?_
      exact (mem_childClusters.1 (mem_of_mem_erase hE')).2.2 D (mem_childClusters.1 hD).1
        (mem_childClusters.1 hE).2.1 (mem_childClusters.1 hD).2.1
    have hK : ∀ F x, populationKernel (L := L) len D F x = if F = x then 1 else 0 := by
      intro F x
      rw [populationKernel, ite_eq_right hDu, hlen, kingmanTransition_zero, Matrix.one_apply]
    have hφD : ∀ x, forestDist H len s D x = contract_sum (childClusters H D)
        (forestDist H len s) (fun F => if F ∪ sampledForest s D = x then 1 else 0) := by
      intro x
      rw [contract_forestDist_eq]
      exact contract_sum_congr (fun _ _ => rfl) fun F => hK _ x
    have hw : ∀ F F₂ : Finset (Finset L),
        populationKernel len A (F ∪ sampledForest s D ∪ F₂ ∪ sampledForest s A) G =
          populationKernel len A (F ∪ F₂ ∪ sampledForest s A) G := by
      intro F F₂
      rw [union_right_comm F, union_assoc (F ∪ F₂),
        union_eq_right.2 (sampledForest_mono s hDA)]
    calc contract_sum (childClusters (H.erase D) A) (forestDist H len s)
          (fun F => populationKernel len A (F ∪ sampledForest s A) G)
        = contract_sum (childClusters H D ∪ (childClusters H A).erase D) (forestDist H len s)
          (fun F => populationKernel len A (F ∪ sampledForest s A) G) := by
          rw [hH.childClusters_erase_of_mem hD]
      _ = contract_sum (childClusters H D) (forestDist H len s) (fun F₁ =>
            contract_sum ((childClusters H A).erase D) (forestDist H len s)
              (fun F₂ => populationKernel len A (F₁ ∪ F₂ ∪ sampledForest s A) G)) :=
          contract_sum_union hdisj _ _
      _ = contract_sum (childClusters H D) (forestDist H len s) (fun F =>
            ∑ x, (if F ∪ sampledForest s D = x then 1 else 0) *
              contract_sum ((childClusters H A).erase D) (forestDist H len s)
                (fun F₂ => populationKernel len A (x ∪ F₂ ∪ sampledForest s A) G)) := by
          refine contract_sum_congr (fun _ _ => rfl) fun F => ?_
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, mem_univ, ite_true]
          exact contract_sum_congr (fun _ _ => rfl) fun F₂ => (hw F F₂).symm
      _ = ∑ x, contract_sum (childClusters H D) (forestDist H len s)
            (fun F => if F ∪ sampledForest s D = x then 1 else 0) *
              contract_sum ((childClusters H A).erase D) (forestDist H len s)
                (fun F₂ => populationKernel len A (x ∪ F₂ ∪ sampledForest s A) G) := by
          rw [← contract_sum_sum]
          exact Finset.sum_congr rfl fun x _ => (contract_sum_mul _ _ _ _).symm
      _ = ∑ x, forestDist H len s D x *
              contract_sum ((childClusters H A).erase D) (forestDist H len s)
                (fun F₂ => populationKernel len A (x ∪ F₂ ∪ sampledForest s A) G) := by
          simp only [hφD]
      _ = contract_sum (childClusters H A) (forestDist H len s)
            (fun F => populationKernel len A (F ∪ sampledForest s A) G) := by
          rw [← contract_sum_singleton]
          conv_rhs => rw [← insert_erase hD, insert_eq]
          exact (contract_sum_union (disjoint_singleton_left.2 (notMem_erase D _)) _
            (fun F => populationKernel len A (F ∪ sampledForest s A) G)).symm
  · rw [childClusters_erase_of_notMem hD]

/-- A hierarchy `H` refining a hierarchy `H₀`, with lengths `0` on the edges above the clusters of
`H` that are not clusters of `H₀`, gives the same multispecies coalescent as `H₀`. -/
theorem forestDist_eq_of_subset_of_len_eq_zero {H₀ H : Finset (Finset X)} (hH₀ : IsHierarchy H₀)
    (hH : IsHierarchy H) (hsub : H₀ ⊆ H) {len : Finset X → ℝ}
    (hlen : ∀ D ∈ H, D ∉ H₀ → len D = 0) (s : L → X) (A : Finset X) (G : Finset (Finset L)) :
    forestDist H len s A G = forestDist H₀ len s A G := by
  obtain ⟨n, hn⟩ : ∃ n, #(H \ H₀) = n := ⟨_, rfl⟩
  induction n generalizing H with
  | zero =>
    rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hn
    rw [Subset.antisymm hn hsub]
  | succ n ih =>
    obtain ⟨D, hD⟩ : (H \ H₀).Nonempty := card_pos.1 (by omega)
    obtain ⟨hDH, hDH₀⟩ := mem_sdiff.1 hD
    have hDu : D ≠ univ := fun e => hDH₀ (e ▸ hH₀.1)
    have hDx : ∀ x, D ≠ {x} := fun x e => hDH₀ (e ▸ hH₀.2.1 x)
    rw [← forestDist_erase_of_len_eq_zero hH hDu (hlen D hDH hDH₀) s A G]
    refine ih (hH.erase hDu hDx)
      (fun B hB => mem_erase.2 ⟨fun e => hDH₀ (e ▸ hB), hsub hB⟩)
      (fun B hB hB₀ => hlen B (mem_of_mem_erase hB) hB₀) ?_
    rw [erase_sdiff_comm, card_erase_of_mem hD, hn, Nat.add_sub_cancel]

/-- The unrooted gene tree distributions in `forestDist_eq_of_subset_of_len_eq_zero`. -/
theorem unrootedDistOf_eq_of_subset_of_len_eq_zero {H₀ H : Finset (Finset X)}
    (hH₀ : IsHierarchy H₀) (hH : IsHierarchy H) (hsub : H₀ ⊆ H) {len : Finset X → ℝ}
    (hlen : ∀ D ∈ H, D ∉ H₀ → len D = 0) (s : L → X) (T : Finset (Finset L)) :
    unrootedDistOf H len s T = unrootedDistOf H₀ len s T := by
  unfold unrootedDistOf
  simp_rw [forestDist_eq_of_subset_of_len_eq_zero hH₀ hH hsub hlen s univ]

/-- A species tree `σ` and a hierarchy `H` refining its hierarchy (for example a binary resolution
of `σ`), with the lengths of `σ` on its edges and lengths `0` on the added edges, give the same
multispecies coalescent. -/
theorem SpeciesTree.forestDist_eq_of_subset (σ : SpeciesTree X) {H : Finset (Finset X)}
    (hH : IsHierarchy H) (hsub : σ.clusters ⊆ H) {len : Finset X → ℝ}
    (hσ : ∀ A ∈ σ.clusters, A ≠ univ → len A = σ.length A)
    (hlen : ∀ D ∈ H, D ∉ σ.clusters → len D = 0) (s : L → X) {A : Finset X}
    (hA : A ∈ σ.clusters) (G : Finset (Finset L)) :
    forestDist H len s A G = forestDist σ.clusters σ.length s A G := by
  rw [forestDist_eq_of_subset_of_len_eq_zero σ.isHierarchy hH hsub hlen s A G]
  exact forestDist_congr_len hσ s hA G

/-- The rooted gene tree distributions in `SpeciesTree.forestDist_eq_of_subset`. -/
theorem SpeciesTree.rootedDist_eq_of_subset (σ : SpeciesTree X) {H : Finset (Finset X)}
    (hH : IsHierarchy H) (hsub : σ.clusters ⊆ H) {len : Finset X → ℝ}
    (hσ : ∀ A ∈ σ.clusters, A ≠ univ → len A = σ.length A)
    (hlen : ∀ D ∈ H, D ∉ σ.clusters → len D = 0) (s : L → X) (G : Finset (Finset L)) :
    forestDist H len s univ G = σ.rootedDist s G :=
  σ.forestDist_eq_of_subset hH hsub hσ hlen s σ.univ_mem G

/-- The unrooted gene tree distributions in `SpeciesTree.forestDist_eq_of_subset`. -/
theorem SpeciesTree.unrootedDist_eq_of_subset (σ : SpeciesTree X) {H : Finset (Finset X)}
    (hH : IsHierarchy H) (hsub : σ.clusters ⊆ H) {len : Finset X → ℝ}
    (hσ : ∀ A ∈ σ.clusters, A ≠ univ → len A = σ.length A)
    (hlen : ∀ D ∈ H, D ∉ σ.clusters → len D = 0) (s : L → X) (T : Finset (Finset L)) :
    unrootedDistOf H len s T = σ.unrootedDist s T := by
  unfold unrootedDistOf SpeciesTree.unrootedDist
  simp_rw [σ.rootedDist_eq_of_subset hH hsub hσ hlen s]

/-! ### Continuity in the edge lengths -/

set_option backward.isDefEq.respectTransparency false in
/-- The transition probabilities of Kingman's coalescent are continuous in time. -/
theorem continuous_kingmanTransition_apply (F G : Finset (Finset L)) :
    Continuous fun t : ℝ => kingmanTransition t F G := by
  open scoped Matrix.Norms.Operator in
  have h : Continuous fun t : ℝ => NormedSpace.exp (t • (kingmanGenerator (L := L))) :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  exact (continuous_apply G).comp ((continuous_apply F).comp h)

/-- The multispecies coalescent depends continuously on the edge lengths. -/
theorem continuous_forestDist (H : Finset (Finset X)) {len : ℝ → Finset X → ℝ}
    (hlen : ∀ A, Continuous fun ε => len ε A) (s : L → X) (A : Finset X)
    (G : Finset (Finset L)) : Continuous fun ε => forestDist H (len ε) s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  have h : (fun ε => forestDist H (len ε) s A G) = fun ε =>
      ∑ f : childClusters H A → Finset (Finset L),
        (∏ B : childClusters H A, forestDist H (len ε) s B (f B)) *
          populationKernel (len ε) A (univ.sup f ∪ sampledForest s A) G := by
    funext ε
    rw [forestDist]
  rw [h]
  refine continuous_finsetSum _ fun f _ => Continuous.mul ?_ ?_
  · exact continuous_finsetProd _ fun B _ => ih B (mem_childClusters.1 B.2).2.1 (f B)
  · by_cases hA : A = univ
    · simp only [populationKernel, hA, ↓reduceIte]
      exact continuous_const
    · simp only [populationKernel, hA, ↓reduceIte]
      exact (continuous_kingmanTransition_apply _ G).comp (hlen A)

/-- The unrooted gene tree distribution depends continuously on the edge lengths. -/
theorem continuous_unrootedDistOf (H : Finset (Finset X)) {len : ℝ → Finset X → ℝ}
    (hlen : ∀ A, Continuous fun ε => len ε A) (s : L → X) (T : Finset (Finset L)) :
    Continuous fun ε => unrootedDistOf H (len ε) s T := by
  unfold unrootedDistOf
  exact continuous_finsetSum _ fun G _ =>
    continuous_if_const _ (fun _ => continuous_forestDist H hlen s univ G) fun _ =>
      continuous_const

/-- **Section 5, limits.** The unrooted gene tree distribution of a hierarchy `H` refining the
hierarchy of a species tree `σ`, with the lengths of `σ` on its edges and the length `ε` on the
added edges, tends to that of `σ` as `ε → 0`. -/
theorem SpeciesTree.tendsto_unrootedDistOf (σ : SpeciesTree X) {H : Finset (Finset X)}
    (hH : IsHierarchy H) (hsub : σ.clusters ⊆ H) (s : L → X) (T : Finset (Finset L)) :
    Filter.Tendsto
      (fun ε : ℝ => unrootedDistOf H (fun A => if A ∈ σ.clusters then σ.length A else ε) s T)
      (nhds 0) (nhds (σ.unrootedDist s T)) := by
  have hcont : Continuous fun ε : ℝ =>
      unrootedDistOf H (fun A => if A ∈ σ.clusters then σ.length A else ε) s T :=
    continuous_unrootedDistOf H
      (fun A => continuous_if_const _ (fun _ => continuous_const) fun _ => continuous_id) s T
  have h0 : unrootedDistOf H (fun A => if A ∈ σ.clusters then σ.length A else (0 : ℝ)) s T =
      σ.unrootedDist s T :=
    σ.unrootedDist_eq_of_subset hH hsub (fun A hA _ => ite_eq_left hA)
      (fun D _ hD => ite_eq_right hD) s T
  rw [← h0]
  exact hcont.tendsto 0

end ADR11
