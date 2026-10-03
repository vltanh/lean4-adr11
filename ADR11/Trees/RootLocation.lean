module

public import ADR11.Introduction.Counts
public import ADR11.External.Quartets.Steel

/-!
# The root of a species tree on its unrooted tree

Helpers for the paper's proof of Theorem 9 and of its extension to nonbinary species trees
(Proposition 11): locating the root `ρ` of a rooted species tree `σ⁺` on its unrooted tree `σ⁻`,
and recovering `σ⁺` from `σ⁻`, the location of the root, and induced five-taxon trees.

In the representation by clusters, the location of the root is given by the children of the root
(`childClusters σ.clusters univ`). The root lies on the edge `A | Aᶜ` of `σ⁻` (a root of degree
two) exactly when `A` and `Aᶜ` are clusters, and these are then the two children of the root. A
root of degree at least three is a vertex of `σ⁻`, at which the edges `R | Rᶜ` of the children `R`
of the root meet.

## Main results

* `rl_childClusters_univ_eq_pair`, `rl_eq_or_eq_compl`: two complementary clusters are the two
  children of the root, so a hierarchy has at most one pair of complementary clusters.
* `rl_exists_compl_mem`: the root of a binary species tree lies on an edge of `σ⁻`.
* `rl_mem_iff`, `rl_eq_of_unroot_eq`: the clusters other than the root are the sides of the splits
  of `σ⁻` contained in a child of the root, so a hierarchy is determined by its unrooted tree and
  the children of its root (it is the rooting of `σ⁻` at the location of the root).
* `rl_restrict_compl_mem`: if the root lies on the edge `A | Aᶜ` and `S` meets `A` and `Aᶜ`, the
  root of the induced tree `σ(S)` lies on the induced edge.
* `rl_mem_childClusters_restrict_iff`: if the most recent common ancestor of `S` is the root (`S`
  lies in no child of the root), the children of the root of `σ(S)` are the traces on `S` of the
  children of the root of `σ`.
* `rl_exists_five`, `rl_exists_insert_meets`: completing a set of taxa to a set of five taxa, and
  a set `Q` of four taxa by a taxon `x ∉ Q` such that `Q ∪ {x}` meets both sides of a split.
* `rl_sameRootedMetricTree_of_clusters_eq`: the last step of the proof of Theorem 9. Two species
  trees with the same clusters, the same unrooted metric tree and the same induced metric trees on
  five taxa have the same metric tree: the length of an edge not at a root of degree two is the
  length of its split in `σ⁻` (`rl_unrootedLength_eq_length`), and the lengths of the two edges at
  a root of degree two are read off an induced tree `σ(S)` on five taxa that has both edges
  (`rl_length_rootEdges`).
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### The children of the root -/

/-- The complement of a set other than `univ` is nonempty. -/
theorem rl_compl_nonempty {A : Finset X} (hAu : A ≠ univ) : Aᶜ.Nonempty := by
  obtain ⟨x, hx⟩ := not_forall.1 fun h => hAu (eq_univ_iff_forall.2 h)
  exact ⟨x, mem_compl.2 hx⟩

/-- Two complementary clusters `A`, `Aᶜ` of a hierarchy are the children of its root. -/
theorem rl_childClusters_univ_eq_pair {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : A ∈ H) (hAc : Aᶜ ∈ H) : childClusters H univ = {A, Aᶜ} :=
  hH.childClusters_eq_pair hA hAc disjoint_compl_right (union_compl A)

/-- A hierarchy has at most one pair of complementary clusters: if `A`, `Aᶜ`, `B`, `Bᶜ` are
clusters, then `B = A` or `B = Aᶜ` (both pairs are the children of the root). -/
theorem rl_eq_or_eq_compl {H : Finset (Finset X)} (hH : IsHierarchy H) {A B : Finset X}
    (hA : A ∈ H) (hAc : Aᶜ ∈ H) (hB : B ∈ H) (hBc : Bᶜ ∈ H) : B = A ∨ B = Aᶜ := by
  have hmem : B ∈ childClusters H univ := by
    rw [rl_childClusters_univ_eq_pair hH hB hBc]
    exact mem_insert_self _ _
  rw [rl_childClusters_univ_eq_pair hH hA hAc, mem_insert, mem_singleton] at hmem
  exact hmem

/-- The root of a binary species tree on at least two taxa lies on an edge of `σ⁻`: the two
children of the root are complementary clusters `A`, `Aᶜ`. -/
theorem rl_exists_compl_mem {σ : SpeciesTree X} (hσ : σ.IsBinary) (hX : 2 ≤ Fintype.card X) :
    ∃ A ∈ σ.clusters, Aᶜ ∈ σ.clusters := by
  obtain ⟨B, hB, C, hC, hBC, hBCu⟩ := hσ univ σ.univ_mem (by rwa [card_univ])
  have hCB : C = Bᶜ := by
    ext x
    rw [mem_compl]
    constructor
    · intro hxC hxB
      exact disjoint_left.1 hBC hxB hxC
    · intro hxB
      have : x ∈ B ∪ C := hBCu ▸ mem_univ x
      exact (mem_union.1 this).resolve_left hxB
  exact ⟨B, hB, hCB ▸ hC⟩

/-- Every taxon lies in a child of the root (on at least two taxa). -/
theorem rl_exists_mem_childClusters_univ {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hX : 2 ≤ Fintype.card X) (x : X) : ∃ R ∈ childClusters H univ, x ∈ R :=
  hH.exists_mem_childClusters (by rwa [card_univ]) (mem_univ x)

/-- Two children of the root with a common taxon are equal. -/
theorem rl_eq_of_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {R R' : Finset X} (hR : R ∈ childClusters H univ) (hR' : R' ∈ childClusters H univ) {x : X}
    (hx : x ∈ R) (hx' : x ∈ R') : R = R' := by
  by_contra hne
  exact disjoint_left.1 (hH.disjoint_of_mem_childClusters hR hR' hne) hx hx'

/-- A child of the root is a cluster other than the root. -/
theorem rl_ne_univ_of_mem_childClusters {H : Finset (Finset X)} {R : Finset X}
    (hR : R ∈ childClusters H univ) : R ≠ univ :=
  ssubset_univ_iff.1 (mem_childClusters.1 hR).2.1

/-! ### Rooting the unrooted tree at the location of the root -/

/-- The clusters of a hierarchy other than the root are the sides of the splits of its unrooted
tree that are contained in a child of the root. -/
theorem rl_mem_iff {H : Finset (Finset X)} (hH : IsHierarchy H) {C : Finset X} :
    C ∈ H ↔ C = univ ∨ (C ∈ unroot H ∧ ∃ R ∈ childClusters H univ, C ⊆ R) := by
  constructor
  · intro hC
    by_cases hCu : C = univ
    · exact Or.inl hCu
    · exact Or.inr ⟨mem_unroot.2 (Or.inl ⟨hC, hCu⟩),
        hH.exists_mem_childClusters_superset hC (ssubset_univ_iff.2 hCu)⟩
  · rintro (rfl | ⟨hC, R, hR, hCR⟩)
    · exact hH.1
    · exact counts_mem_of_mem_unroot_of_subset hH (mem_childClusters.1 hR).1
        (rl_ne_univ_of_mem_childClusters hR) hC hCR

/-- A hierarchy is determined by its unrooted tree and the children of its root: it is the
rooting of its unrooted tree at the location of the root. -/
theorem rl_eq_of_unroot_eq {H H' : Finset (Finset X)} (hH : IsHierarchy H)
    (hH' : IsHierarchy H') (hU : unroot H = unroot H')
    (hR : childClusters H univ = childClusters H' univ) : H = H' := by
  ext C
  rw [rl_mem_iff hH, rl_mem_iff hH', hU, hR]

/-! ### The root of an induced subtree -/

omit [Fintype X] in
/-- Two sets with the same trace on `S` contain the same taxa of `S`. -/
theorem rl_mem_iff_of_subtype_eq {S A B : Finset X}
    (h : A.subtype (· ∈ S) = B.subtype (· ∈ S)) {x : X} (hx : x ∈ S) : x ∈ A ↔ x ∈ B := by
  have h1 : (⟨x, hx⟩ : S) ∈ A.subtype (· ∈ S) ↔ (⟨x, hx⟩ : S) ∈ B.subtype (· ∈ S) := by
    rw [h]
  simpa only [mem_subtype] using h1

/-- If the root of `σ` lies on the edge `A | Aᶜ` of `σ⁻` (`A` and `Aᶜ` are clusters) and `S` meets
both `A` and `Aᶜ`, then the root of the induced tree `σ(S)` is the root of `σ` and lies on the
induced edge: the traces of `A` and `Aᶜ` on `S` are clusters of `σ(S)`. -/
theorem rl_restrict_compl_mem (σ : SpeciesTree X) {A S : Finset X} (hA : A ∈ σ.clusters)
    (hAc : Aᶜ ∈ σ.clusters) (hAS : (A ∩ S).Nonempty) (hAcS : (Aᶜ ∩ S).Nonempty)
    (hS : S.Nonempty) :
    A.subtype (· ∈ S) ∈ (σ.restrict S hS).clusters ∧
      (A.subtype (· ∈ S))ᶜ ∈ (σ.restrict S hS).clusters := by
  refine ⟨subtype_mem_restrictClusters hA hAS, ?_⟩
  rw [← subtype_compl]
  exact subtype_mem_restrictClusters hAc hAcS

/-- If `S` lies in no child of the root of `σ` (the most recent common ancestor of `S` is the
root), the children of the root of the induced tree `σ(S)` are the traces on `S` of the children
of the root of `σ` that meet `S`. -/
theorem rl_mem_childClusters_restrict_iff (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty)
    (hmrca : ∀ R ∈ childClusters σ.clusters univ, ¬ S ⊆ R) {C : Finset S} :
    C ∈ childClusters (σ.restrict S hS).clusters univ ↔
      ∃ R ∈ childClusters σ.clusters univ, (R ∩ S).Nonempty ∧ R.subtype (· ∈ S) = C := by
  have hH := σ.isHierarchy
  -- the trace of a child of the root that meets `S` is a cluster of `σ(S)` other than its root
  have htr : ∀ R ∈ childClusters σ.clusters univ, (R ∩ S).Nonempty →
      R.subtype (· ∈ S) ∈ (σ.restrict S hS).clusters ∧ R.subtype (· ∈ S) ⊂ univ := by
    intro R hR hRS
    refine ⟨subtype_mem_restrictClusters (mem_childClusters.1 hR).1 hRS,
      ssubset_univ_iff.2 (subtype_ne_univ_iff.2 ?_)⟩
    obtain ⟨y, hyS, hyR⟩ := not_subset.1 (hmrca R hR)
    exact ⟨y, mem_inter.2 ⟨mem_compl.2 hyR, hyS⟩⟩
  -- a cluster of `σ` other than the root lies in a child of the root
  have hsup : ∀ B ∈ σ.clusters, B ≠ univ → ∃ R ∈ childClusters σ.clusters univ, B ⊆ R :=
    fun B hB hBu => hH.exists_mem_childClusters_superset hB (ssubset_univ_iff.2 hBu)
  constructor
  · intro hC
    obtain ⟨hCcl, hCu, hmax⟩ := mem_childClusters.1 hC
    obtain ⟨B, hB, hBS, rfl⟩ := mem_restrictClusters.1 hCcl
    have hBu : B ≠ univ := by
      rintro rfl
      exact (ssubset_univ_iff.1 hCu) (subtype_univ _)
    obtain ⟨R, hR, hBR⟩ := hsup B hB hBu
    have hRS : (R ∩ S).Nonempty := by
      obtain ⟨y, hy⟩ := hBS
      exact ⟨y, mem_inter.2 ⟨hBR (mem_inter.1 hy).1, (mem_inter.1 hy).2⟩⟩
    refine ⟨R, hR, hRS, ?_⟩
    obtain ⟨hRcl, hRu⟩ := htr R hR hRS
    rcases (subtype_mono hBR : B.subtype (· ∈ S) ⊆ R.subtype (· ∈ S)).eq_or_ssubset with h | h
    · exact h.symm
    · exact absurd hRu (hmax _ hRcl h)
  · rintro ⟨R, hR, hRS, rfl⟩
    obtain ⟨hRcl, hRu⟩ := htr R hR hRS
    refine mem_childClusters.2 ⟨hRcl, hRu, fun D hD hRD hDu => ?_⟩
    obtain ⟨B, hB, -, rfl⟩ := mem_restrictClusters.1 hD
    have hBu : B ≠ univ := by
      rintro rfl
      exact (ssubset_univ_iff.1 hDu) (subtype_univ _)
    -- `B` lies in a child of the root, which shares with `R` a taxon of `R ∩ S`, so `B ⊆ R`
    obtain ⟨R', hR', hBR'⟩ := hsup B hB hBu
    obtain ⟨y, hy⟩ := hRS
    have hyB : y ∈ B := mem_subtype.1
      (hRD.subset (mem_subtype.2 (mem_inter.1 hy).1 : (⟨y, (mem_inter.1 hy).2⟩ : S) ∈ _))
    have := rl_eq_of_mem_childClusters hH hR hR' (mem_inter.1 hy).1 (hBR' hyB)
    subst this
    exact not_subset_of_ssubset hRD (subtype_mono hBR')

/-! ### Sets of five taxa -/

omit [DecidableEq X] in
/-- A set of at most five taxa is contained in a set of exactly five taxa. -/
theorem rl_exists_five (hX : 5 ≤ Fintype.card X) {T : Finset X} (hT : #T ≤ 5) :
    ∃ S, T ⊆ S ∧ #S = 5 := by
  obtain ⟨S, hTS, -, hS⟩ := exists_subsuperset_card_eq (subset_univ T) hT (by rwa [card_univ])
  exact ⟨S, hTS, hS⟩

/-- A set `Q` of four taxa can be completed by a taxon `x ∉ Q` such that `Q ∪ {x}` meets both
sides of a split `R | Rᶜ`. -/
theorem rl_exists_insert_meets (hX : 5 ≤ Fintype.card X) {Q R : Finset X} (hQ : #Q = 4)
    (hR : R.Nonempty) (hRc : Rᶜ.Nonempty) :
    ∃ x ∉ Q, (R ∩ insert x Q).Nonempty ∧ (Rᶜ ∩ insert x Q).Nonempty := by
  have hins : ∀ {P : Finset X} {x : X}, (P ∩ Q).Nonempty → (P ∩ insert x Q).Nonempty :=
    fun ⟨y, hy⟩ => ⟨y, mem_inter.2 ⟨(mem_inter.1 hy).1, mem_insert_of_mem (mem_inter.1 hy).2⟩⟩
  have hnew : ∀ {P : Finset X} {x : X}, x ∈ P → (P ∩ insert x Q).Nonempty :=
    fun hx => ⟨_, mem_inter.2 ⟨hx, mem_insert_self _ _⟩⟩
  by_cases h1 : (R ∩ Q).Nonempty
  · by_cases h2 : (Rᶜ ∩ Q).Nonempty
    · -- `Q` meets both sides: any taxon `x ∉ Q`
      obtain ⟨x, hx⟩ : Qᶜ.Nonempty := by
        rw [← card_pos, card_compl]
        omega
      exact ⟨x, mem_compl.1 hx, hins h1, hins h2⟩
    · -- `Q ⊆ R`: a taxon `x ∈ Rᶜ`
      obtain ⟨x, hx⟩ := hRc
      exact ⟨x, fun hxQ => h2 ⟨x, mem_inter.2 ⟨hx, hxQ⟩⟩, hins h1, hnew hx⟩
  · -- `Q ⊆ Rᶜ`: a taxon `x ∈ R`
    obtain ⟨x, hx⟩ := hR
    obtain ⟨q, hq⟩ : Q.Nonempty := card_pos.1 (by omega)
    have hqR : q ∈ Rᶜ := mem_compl.2 fun hqR => h1 ⟨q, mem_inter.2 ⟨hqR, hq⟩⟩
    exact ⟨x, fun hxQ => h1 ⟨x, mem_inter.2 ⟨hx, hxQ⟩⟩, hnew hx,
      hins ⟨q, mem_inter.2 ⟨hqR, hq⟩⟩⟩

/-! ### Edge lengths -/

/-- The unrooted length of the split `A | Aᶜ` of a cluster `A ≠ univ` whose complement is not a
cluster (an edge not at a root of degree two) is the length of the edge above `A`. -/
theorem rl_unrootedLength_eq_length (σ : SpeciesTree X) {A : Finset X} (hA : A ∈ σ.clusters)
    (hAu : A ≠ univ) (hAc : Aᶜ ∉ σ.clusters) : σ.unrootedLength A = σ.length A := by
  unfold SpeciesTree.unrootedLength
  rw [Finset.sum_eq_single_of_mem A (mem_filter.2 ⟨hA, hAu, Or.inl rfl⟩)]
  intro C hC hCA
  obtain ⟨hC1, -, hC3⟩ := mem_filter.1 hC
  rcases hC3 with rfl | rfl
  · exact absurd rfl hCA
  · exact absurd hC1 hAc

/-- Taxa witnessing an edge at the root: a child `B` of the root contains a nonempty set `W` of at
most two taxa such that, if `B` has at least two taxa, then `W` has two taxa (from different
children of `B`) and `B` is the only cluster other than the root that contains `W`. -/
theorem rl_exists_witness {H : Finset (Finset X)} (hH : IsHierarchy H) {B : Finset X}
    (hB : B ∈ childClusters H univ) :
    ∃ W ⊆ B, W.Nonempty ∧ #W ≤ 2 ∧
      (2 ≤ #B → 2 ≤ #W ∧ ∀ C ∈ H, C ≠ univ → W ⊆ C → C = B) := by
  have hBH := (mem_childClusters.1 hB).1
  by_cases hB2 : 2 ≤ #B
  · -- two taxa `a₁`, `a₂` in different children of `B`
    obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := one_lt_card.1 (hH.two_le_card_childClusters hB2)
    obtain ⟨a₁, ha₁⟩ := hH.2.2.1 B₁ (mem_childClusters.1 hB₁).1
    obtain ⟨a₂, ha₂⟩ := hH.2.2.1 B₂ (mem_childClusters.1 hB₂).1
    have ha12 : a₁ ≠ a₂ := fun e =>
      disjoint_left.1 (hH.disjoint_of_mem_childClusters hB₁ hB₂ hne) ha₁ (e ▸ ha₂)
    refine ⟨{a₁, a₂}, ?_, insert_nonempty _ _, card_le_two, fun _ => ⟨by rw [card_pair ha12], ?_⟩⟩
    · rw [insert_subset_iff, singleton_subset_iff]
      exact ⟨(mem_childClusters.1 hB₁).2.1.subset ha₁, (mem_childClusters.1 hB₂).2.1.subset ha₂⟩
    · intro C hC hCu hWC
      -- `B` is the smallest cluster containing `a₁` and `a₂`, and only the root strictly
      -- contains `B`
      have hBC : B ⊆ C := by
        rw [← hH.lca_pair_eq_of_mem_childClusters hBH hB₁ hB₂ hne ha₁ ha₂]
        exact lca_subset hC hWC
      obtain ⟨R, hR, hCR⟩ := hH.exists_mem_childClusters_superset hC (ssubset_univ_iff.2 hCu)
      obtain ⟨b, hb⟩ := hH.2.2.1 B hBH
      have := rl_eq_of_mem_childClusters hH hB hR hb (hCR (hBC hb))
      subst this
      exact Subset.antisymm hCR hBC
  · obtain ⟨b, hb⟩ := hH.2.2.1 B hBH
    exact ⟨{b}, singleton_subset_iff.2 hb, singleton_nonempty b, by simp,
      fun h => absurd h hB2⟩

/-- The edges at a root of degree two (proof of Theorem 9). Let `A` and `Aᶜ` be clusters of `σ`,
the two children of its root, and let `σ'` have the same clusters and the same induced metric
trees on all sets of five taxa. Then the internal ones of the two edges at the root have the same
lengths in `σ` and `σ'`: they are the edges above `A ∩ S` and `Aᶜ ∩ S` in the induced tree
`σ(S)`, for a set `S` of five taxa containing, for each of `A` and `Aᶜ` with at least two taxa,
two taxa in different children of it. -/
theorem rl_length_rootEdges (hX : 5 ≤ Fintype.card X) {σ σ' : SpeciesTree X}
    (hcl : σ.clusters = σ'.clusters)
    (h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS))
    {A : Finset X} (hA : A ∈ σ.clusters) (hAc : Aᶜ ∈ σ.clusters) :
    (2 ≤ #A → σ.length A = σ'.length A) ∧ (2 ≤ #Aᶜ → σ.length Aᶜ = σ'.length Aᶜ) := by
  have hH := σ.isHierarchy
  have hch := rl_childClusters_univ_eq_pair hH hA hAc
  have hAR : A ∈ childClusters σ.clusters univ := hch ▸ mem_insert_self _ _
  have hAcR : Aᶜ ∈ childClusters σ.clusters univ :=
    hch ▸ mem_insert_of_mem (mem_singleton_self _)
  -- the set `S`: witnesses for both edges at the root, completed to five taxa
  obtain ⟨W, hWA, hWne, hW2, hW⟩ := rl_exists_witness hH hAR
  obtain ⟨W', hW'A, hW'ne, hW'2, hW'⟩ := rl_exists_witness hH hAcR
  obtain ⟨S, hWS, hS5⟩ := rl_exists_five hX (T := W ∪ W') ((card_union_le _ _).trans (by omega))
  have hS : S.Nonempty := hWne.mono (subset_union_left.trans hWS)
  -- the edge above a child `B` of the root, witnessed by `V ⊆ B ∩ S`, when `S` meets `Bᶜ`
  have key : ∀ B ∈ σ.clusters, B ≠ univ → ∀ V ⊆ B, V ⊆ S →
      (∀ C ∈ σ.clusters, C ≠ univ → V ⊆ C → C = B) → 2 ≤ #V → (Bᶜ ∩ S).Nonempty →
        σ.length B = σ'.length B := by
    intro B hB hBu V hVB hVS hV hV2 hBcS
    -- `B` is the only cluster of `σ` (and of `σ'`) whose trace on `S` is `B ∩ S`
    have huniq : ∀ C ∈ σ.clusters, C.subtype (· ∈ S) = B.subtype (· ∈ S) → C = B := by
      intro C hC hCB
      have hmem : ∀ x ∈ S, x ∈ C ↔ x ∈ B := fun x hx => rl_mem_iff_of_subtype_eq hCB hx
      have hCu : C ≠ univ := by
        rintro rfl
        obtain ⟨y, hy⟩ := hBcS
        exact mem_compl.1 (mem_inter.1 hy).1 ((hmem y (mem_inter.1 hy).2).1 (mem_univ y))
      exact hV C hC hCu fun x hx => (hmem x (hVS hx)).2 (hVB hx)
    have hBS : (B ∩ S).Nonempty := by
      obtain ⟨v, hv⟩ : V.Nonempty := card_pos.1 (by omega)
      exact ⟨v, mem_inter.2 ⟨hVB hv, hVS hv⟩⟩
    have hmem : B.subtype (· ∈ S) ∈ (σ.restrict S hS).clusters :=
      subtype_mem_restrictClusters hB hBS
    have h2 : 2 ≤ #(B.subtype (· ∈ S)) := by
      rw [card_subtype]
      exact hV2.trans (card_le_card fun v hv => mem_filter.2 ⟨hVB hv, hVS hv⟩)
    have hu : B.subtype (· ∈ S) ≠ univ := subtype_ne_univ_iff.2 hBcS
    -- Proposition 8 for `σ(S)` gives the length of the edge above `B ∩ S`
    have := (h5 S hS hS5).2 _ hmem h2 hu
    rw [SpeciesTree.restrict_length, SpeciesTree.restrict_length,
      σ.restrictLength_subtype_eq hB hBu huniq,
      σ'.restrictLength_subtype_eq (hcl ▸ hB) hBu fun C hC => huniq C (hcl ▸ hC)] at this
    exact this
  refine ⟨fun hA2 => ?_, fun hAc2 => ?_⟩
  · obtain ⟨hW2', hWu⟩ := hW hA2
    obtain ⟨w', hw'⟩ := hW'ne
    exact key A hA (rl_ne_univ_of_mem_childClusters hAR) W hWA
      (subset_union_left.trans hWS) hWu hW2'
      ⟨w', mem_inter.2 ⟨hW'A hw', hWS (mem_union_right _ hw')⟩⟩
  · obtain ⟨hW'2', hW'u⟩ := hW' hAc2
    obtain ⟨w, hw⟩ := hWne
    refine key Aᶜ hAc (rl_ne_univ_of_mem_childClusters hAcR) W' hW'A
      (subset_union_right.trans hWS) hW'u hW'2' ⟨w, ?_⟩
    rw [compl_compl]
    exact mem_inter.2 ⟨hWA hw, hWS (mem_union_left _ hw)⟩

/-- The edge lengths (last step of the proof of Theorem 9). Two species trees on at least five
taxa with the same clusters, the same unrooted metric tree, and the same induced metric trees on
all sets of five taxa have the same metric tree. The length of an edge not at a root of degree
two is the length of its split in `σ⁻`; the lengths of the edges at a root of degree two are read
off an induced tree on five taxa that has these edges (`rl_length_rootEdges`). -/
theorem rl_sameRootedMetricTree_of_clusters_eq (hX : 5 ≤ Fintype.card X) {σ σ' : SpeciesTree X}
    (hcl : σ.clusters = σ'.clusters) (hU : σ.SameUnrootedMetricTree σ')
    (h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS)) :
    σ.SameRootedMetricTree σ' := by
  refine ⟨hcl, fun A hA hA2 hAu => ?_⟩
  by_cases hAc : Aᶜ ∈ σ.clusters
  · -- an edge at a root of degree two
    exact (rl_length_rootEdges hX hcl h5 hA hAc).1 hA2
  · -- an edge not at the root: its length is the length of its split in `σ⁻`
    have hAc2 : 2 ≤ #Aᶜ := by
      by_contra hlt
      obtain ⟨x, hx⟩ := card_eq_one.1
        (le_antisymm (by omega) (card_pos.2 (rl_compl_nonempty hAu)))
      exact hAc (hx ▸ σ.singleton_mem x)
    have hAc' : Aᶜ ∉ σ'.clusters := by rwa [← hcl]
    rw [← rl_unrootedLength_eq_length σ hA hAu hAc,
      ← rl_unrootedLength_eq_length σ' (hcl ▸ hA) hAu hAc']
    exact hU.2 A (mem_unroot.2 (Or.inl ⟨hA, hAu⟩)) hA2 hAc2

end ADR11
