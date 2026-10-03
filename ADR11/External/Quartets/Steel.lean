module

public import ADR11.Trees.Hierarchy

/-!
# Unrooted trees are determined by their quartets

[M. Steel, *The complexity of reconstructing trees from qualitative characters and subtrees*,
J. Classification 9 (1992) 91–116], used in the proofs of Corollary 6 (binary trees) and of
Theorem 9 (Proposition 6 there: every internal edge is distinguished by a quartet); for trees
that need not be binary, [H.-J. Bandelt, A. Dress, *Reconstructing the shape of a tree from
observed dissimilarity data*, Adv. Appl. Math. 7 (1986) 309–343] and [C. Semple, M. Steel,
*Phylogenetics*, Oxford University Press, 2003, Theorem 6.3.5], used in the proof of
Proposition 11.

In the representation of `ADR11.unroot`, these are statements about the sets of splits of the
unrooted trees `σ⁻` of species trees:

* `mem_unroot_iff_quartets`: a bipartition `A | Aᶜ` with `|A|, |Aᶜ| ≥ 2` is a split of `σ⁻` if and
  only if every quartet `aa'|bb'` with `a, a' ∈ A` and `b, b' ∈ Aᶜ` is displayed by `σ⁻`.
* `exists_distinguishing_quartet`: every internal edge of `σ⁻` is the only edge of `σ⁻` separating
  some quartet `aa'|bb'` (Steel's Proposition 6, for trees that need not be binary).
* `SpeciesTree.sameUnrootedMetricTree_of_restrict`: two species trees whose induced unrooted
  metric trees agree on every set of four taxa have the same unrooted metric tree.

## Proofs

* `mem_unroot_iff_quartets`: rerooting `σ⁻` at a taxon `b₀ ∉ A`, the sides of the splits of `σ⁻`
  not containing `b₀`, together with `univ` and `{b₀}`, form a hierarchy, in which `A` is a
  cluster by the rooted-triple criterion `SpeciesTree.mem_clusters_of_triples`.
* `exists_distinguishing_quartet`: for a cluster `A` of `σ`, take `a, a'` in different children
  of `A`; if the parent `P` of `A` is not the root, take `b ∈ P \ A` and `b' ∉ P`, and otherwise
  take `b, b' ∈ Aᶜ` such that no cluster strictly contained in `Aᶜ` contains both.
* `SpeciesTree.sameUnrootedMetricTree_of_restrict`: the splits of `σ⁻` are compared through their
  quartets (`SpeciesTree.restrict_unroot`), and the length of a split through a distinguishing
  quartet, whose induced split is induced by no other split (`SpeciesTree.restrict_unrootedLength`).
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Membership in `unroot`: a non-root cluster or the complement of one. -/
private theorem steel_mem_unroot {G : Finset (Finset X)} {A : Finset X} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := by
  unfold unroot
  rw [mem_union, mem_erase, mem_image]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨B, hB, rfl⟩)
    · exact Or.inl ⟨h2, h1⟩
    · rw [mem_erase] at hB
      right
      rw [compl_compl]
      exact ⟨hB.2, hB.1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨Aᶜ, mem_erase.2 ⟨h2, h1⟩, compl_compl A⟩

/-- `unroot` is closed under complements. -/
private theorem steel_compl_mem_unroot {G : Finset (Finset X)} {A : Finset X}
    (h : A ∈ unroot G) : Aᶜ ∈ unroot G := by
  rw [steel_mem_unroot] at h ⊢
  rw [compl_compl]
  exact h.symm

/-- The sides of the splits of `σ⁻` are nonempty. -/
private theorem steel_nonempty_of_mem_unroot (σ : SpeciesTree X) {A : Finset X}
    (h : A ∈ unroot σ.clusters) : A.Nonempty := by
  rcases steel_mem_unroot.1 h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact σ.nonempty_of_mem A h1
  · rw [nonempty_iff_ne_empty]
    rintro rfl
    exact h2 compl_empty

/-- The sides of the splits of `σ⁻` not containing a fixed taxon `b₀` are nested or disjoint. -/
private theorem steel_laminar_avoid (σ : SpeciesTree X) {b₀ : X} {C D : Finset X}
    (hC : C ∈ unroot σ.clusters) (hD : D ∈ unroot σ.clusters) (hC₀ : b₀ ∉ C)
    (hD₀ : b₀ ∉ D) : C ⊆ D ∨ D ⊆ C ∨ Disjoint C D := by
  rcases steel_mem_unroot.1 hC with ⟨hC1, -⟩ | ⟨hC1, -⟩ <;>
    rcases steel_mem_unroot.1 hD with ⟨hD1, -⟩ | ⟨hD1, -⟩
  · exact σ.laminar C hC1 D hD1
  · rcases σ.laminar C hC1 Dᶜ hD1 with h | h | h
    · exact Or.inr (Or.inr (subset_compl_iff_disjoint_right.1 h))
    · exact absurd (h (mem_compl.2 hD₀)) hC₀
    · left
      intro x hx
      by_contra hxD
      exact disjoint_left.1 h hx (mem_compl.2 hxD)
  · rcases σ.laminar Cᶜ hC1 D hD1 with h | h | h
    · exact absurd (h (mem_compl.2 hC₀)) hD₀
    · exact Or.inr (Or.inr (subset_compl_iff_disjoint_right.1 h).symm)
    · right; left
      intro x hx
      by_contra hxC
      exact disjoint_left.1 h (mem_compl.2 hxC) hx
  · rcases σ.laminar Cᶜ hC1 Dᶜ hD1 with h | h | h
    · exact Or.inr (Or.inl (compl_subset_compl.1 h))
    · exact Or.inl (compl_subset_compl.1 h)
    · exact absurd (mem_compl.2 hD₀) (disjoint_left.1 h (mem_compl.2 hC₀))

/-- A split `A | Aᶜ` (with both sides of size at least 2) is a split of `σ⁻` if and only if every
quartet `aa'|bb'` (`a ≠ a'` in `A`, `b ≠ b'` in `Aᶜ`) is displayed by `σ⁻`, that is, separated by
some split of `σ⁻`. -/
theorem mem_unroot_iff_quartets (σ : SpeciesTree X) {A : Finset X} (hA : 2 ≤ #A)
    (hA' : 2 ≤ #Aᶜ) :
    A ∈ unroot σ.clusters ↔
      ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ Aᶜ, ∀ b' ∈ Aᶜ, a ≠ a' → b ≠ b' →
        ∃ C ∈ unroot σ.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C ∧ b' ∉ C := by
  constructor
  · intro h a ha a' ha' b hb b' hb' _ _
    exact ⟨A, h, ha, ha', mem_compl.1 hb, mem_compl.1 hb'⟩
  intro hq
  obtain ⟨b₀, hb₀⟩ : Aᶜ.Nonempty := card_pos.1 (by omega)
  have hb₀A : b₀ ∉ A := mem_compl.1 hb₀
  obtain ⟨b₁, hb₁, hb₁₀⟩ := exists_mem_ne (show 1 < #Aᶜ by omega) b₀
  have hAne : A.Nonempty := card_pos.1 (by omega)
  -- the clusters of `σ⁻` rerooted at the leaf `b₀`
  set F := (unroot σ.clusters).filter fun C => b₀ ∉ C
  set H := insert univ (insert {b₀} F)
  have hsing : ∀ x : X, {x} ∈ H := by
    intro x
    by_cases hx : x = b₀
    · subst hx
      exact mem_insert_of_mem (mem_insert_self _ _)
    · by_cases hu : ({x} : Finset X) = univ
      · rw [hu]
        exact mem_insert_self _ _
      · refine mem_insert_of_mem (mem_insert_of_mem (mem_filter.2 ⟨?_, ?_⟩))
        · exact steel_mem_unroot.2 (Or.inl ⟨σ.singleton_mem x, hu⟩)
        · rw [mem_singleton]
          exact Ne.symm hx
  have hne : ∀ C ∈ H, C.Nonempty := by
    intro C hC
    rcases mem_insert.1 hC with rfl | hC
    · exact ⟨b₀, mem_univ _⟩
    rcases mem_insert.1 hC with rfl | hC
    · exact singleton_nonempty _
    exact steel_nonempty_of_mem_unroot σ (mem_filter.1 hC).1
  have hlam : ∀ C ∈ H, ∀ D ∈ H, C ⊆ D ∨ D ⊆ C ∨ Disjoint C D := by
    intro C hC D hD
    rcases mem_insert.1 hC with rfl | hC
    · exact Or.inr (Or.inl (subset_univ _))
    rcases mem_insert.1 hD with rfl | hD
    · exact Or.inl (subset_univ _)
    rcases mem_insert.1 hC with rfl | hC <;> rcases mem_insert.1 hD with rfl | hD
    · exact Or.inl (subset_refl _)
    · exact Or.inr (Or.inr (disjoint_singleton_left.2 (mem_filter.1 hD).2))
    · exact Or.inr (Or.inr (disjoint_singleton_right.2 (mem_filter.1 hC).2))
    · exact steel_laminar_avoid σ (mem_filter.1 hC).1 (mem_filter.1 hD).1 (mem_filter.1 hC).2
        (mem_filter.1 hD).2
  let τ : SpeciesTree X :=
    { clusters := H
      univ_mem := mem_insert_self _ _
      singleton_mem := hsing
      nonempty_of_mem := hne
      laminar := hlam
      length := fun _ => 1
      length_pos := fun _ _ _ => one_pos }
  have key : A ∈ H := by
    refine τ.mem_clusters_of_triples hAne ?_
    intro a ha a' ha' b hb
    by_cases haa : a = a'
    · subst haa
      refine ⟨{a}, hsing a, mem_singleton_self a, mem_singleton_self a, ?_⟩
      rw [mem_singleton]
      rintro rfl
      exact hb ha
    · by_cases hbb : b = b₀
      · subst hbb
        obtain ⟨C, hC, h1, h2, -, h4⟩ := hq a ha a' ha' b₁ hb₁ b hb₀ haa hb₁₀
        exact ⟨C, mem_insert_of_mem (mem_insert_of_mem (mem_filter.2 ⟨hC, h4⟩)), h1, h2, h4⟩
      · obtain ⟨C, hC, h1, h2, h3, h4⟩ := hq a ha a' ha' b (mem_compl.2 hb) b₀ hb₀ haa hbb
        exact ⟨C, mem_insert_of_mem (mem_insert_of_mem (mem_filter.2 ⟨hC, h4⟩)), h1, h2, h3⟩
  rcases mem_insert.1 key with h | h
  · exact absurd (h ▸ mem_univ b₀) hb₀A
  rcases mem_insert.1 h with h | h
  · exact absurd (h ▸ mem_singleton_self b₀) hb₀A
  exact (mem_filter.1 h).1

/-- Two taxa `x ≠ y` of a set `N` with at least two elements such that no cluster strictly
contained in `N` contains both. -/
private theorem steel_exists_pair (σ : SpeciesTree X) {N : Finset X} (hN : 2 ≤ #N) :
    ∃ x ∈ N, ∃ y ∈ N, x ≠ y ∧ ∀ C ∈ σ.clusters, x ∈ C → y ∈ C → ¬ C ⊂ N := by
  obtain ⟨x, hx⟩ : N.Nonempty := card_pos.1 (by omega)
  have hxN : ({x} : Finset X) ⊂ N := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨singleton_subset_iff.2 hx, ?_⟩
    rintro h
    rw [← h, card_singleton] at hN
    omega
  obtain ⟨M, hM, hMmax⟩ := exists_max_image (σ.clusters.filter fun C => x ∈ C ∧ C ⊂ N) card
    ⟨{x}, mem_filter.2 ⟨σ.singleton_mem x, mem_singleton_self x, hxN⟩⟩
  obtain ⟨hMc, hxM, hMN⟩ := mem_filter.1 hM
  obtain ⟨y, hyN, hyM⟩ := exists_of_ssubset hMN
  refine ⟨x, hx, y, hyN, ?_, ?_⟩
  · rintro rfl
    exact hyM hxM
  · intro C hC hxC hyC hCN
    have hle := hMmax C (mem_filter.2 ⟨hC, hxC, hCN⟩)
    rcases σ.laminar C hC M hMc with h | h | h
    · exact hyM (h hyC)
    · rw [eq_of_subset_of_card_le h hle] at hyM
      exact hyM hyC
    · exact disjoint_left.1 h hxC hxM

/-- Steel's Proposition 6 for a split `A | Aᶜ` given by a cluster `A` of `σ`. -/
private theorem steel_distinguishing_of_mem_clusters (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ σ.clusters) (hAu : A ≠ univ) (hA₁ : 2 ≤ #A) (hA₂ : 2 ≤ #Aᶜ) :
    ∃ a ∈ A, ∃ a' ∈ A, ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, a ≠ a' ∧ b ≠ b' ∧
      ∀ C ∈ unroot σ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A := by
  obtain ⟨z, hz⟩ : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨a, ha, a', ha', haa, hpair⟩ := steel_exists_pair σ hA₁
  -- the clusters containing `a` and `a'` contain `A`
  have hup : ∀ C ∈ σ.clusters, a ∈ C → a' ∈ C → A ⊆ C := by
    intro C hC h1 h2
    rcases σ.laminar C hC A hA with h | h | h
    · have hCA : C = A := by
        by_contra hne
        exact hpair C hC h1 h2 (Finset.ssubset_iff_subset_ne.2 ⟨h, hne⟩)
      rw [hCA]
    · exact h
    · exact absurd ha (disjoint_left.1 h h1)
  -- the parent `P` of `A`
  obtain ⟨P, hP, hPmin⟩ := exists_min_image (σ.clusters.filter fun C => A ⊂ C) card
    ⟨univ, mem_filter.2 ⟨σ.univ_mem, ssubset_univ_iff.2 hAu⟩⟩
  obtain ⟨hPc, hAP⟩ := mem_filter.1 hP
  have hPle : ∀ C ∈ σ.clusters, A ⊂ C → P ⊆ C := by
    intro C hC hAC
    have hle := hPmin C (mem_filter.2 ⟨hC, hAC⟩)
    rcases σ.laminar C hC P hPc with h | h | h
    · rw [eq_of_subset_of_card_le h hle]
    · exact h
    · exact absurd (hAP.1 hz) (disjoint_left.1 h (hAC.1 hz))
  -- two taxa `b, b'` outside `A`
  obtain ⟨b, hb, b', hb', hbb, hP1, hP2⟩ : ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, b ≠ b' ∧
      (∀ C ∈ σ.clusters, A ⊂ C → b ∈ C ∨ b' ∈ C) ∧
      (∀ D ∈ σ.clusters, b ∈ D → b' ∈ D → ¬ D ⊂ Aᶜ) := by
    by_cases hPu : P = univ
    · obtain ⟨b, hb, b', hb', hbb, h⟩ := steel_exists_pair σ hA₂
      refine ⟨b, hb, b', hb', hbb, fun C hC hAC => Or.inl ?_, h⟩
      have := hPle C hC hAC
      rw [hPu] at this
      exact this (mem_univ b)
    · obtain ⟨b, hbP, hbA⟩ := exists_of_ssubset hAP
      obtain ⟨b', hb'⟩ : Pᶜ.Nonempty := by
        rw [nonempty_iff_ne_empty, Ne, compl_eq_empty_iff]
        exact hPu
      rw [mem_compl] at hb'
      refine ⟨b, mem_compl.2 hbA, b', mem_compl.2 (fun h => hb' (hAP.1 h)), ?_, ?_, ?_⟩
      · rintro rfl
        exact hb' hbP
      · intro C hC hAC
        exact Or.inl (hPle C hC hAC hbP)
      · intro D hD hbD hb'D hDA
        rcases σ.laminar D hD P hPc with h | h | h
        · exact hb' (h hb'D)
        · exact mem_compl.1 (hDA.1 (h (hAP.1 hz))) hz
        · exact disjoint_left.1 h hbD hbP
  refine ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, ?_⟩
  intro C hC haC ha'C hbC hb'C
  rcases steel_mem_unroot.1 hC with ⟨hC1, -⟩ | ⟨hC1, -⟩
  · have hAC := hup C hC1 haC ha'C
    by_contra hne
    rcases hP1 C hC1 (Finset.ssubset_iff_subset_ne.2 ⟨hAC, Ne.symm hne⟩) with h | h
    · exact hbC h
    · exact hb'C h
  · have hbD : b ∈ Cᶜ := mem_compl.2 hbC
    have hb'D : b' ∈ Cᶜ := mem_compl.2 hb'C
    have hDA : Cᶜ ⊆ Aᶜ := by
      rcases σ.laminar Cᶜ hC1 A hA with h | h | h
      · exact absurd (h hbD) (mem_compl.1 hb)
      · exact absurd haC (mem_compl.1 (h ha))
      · exact subset_compl_iff_disjoint_right.2 h
    have hEq : Cᶜ = Aᶜ := by
      by_contra hne
      exact hP2 Cᶜ hC1 hbD hb'D (Finset.ssubset_iff_subset_ne.2 ⟨hDA, hne⟩)
    exact compl_injective hEq

/-- Steel's Proposition 6: every internal edge `A | Aᶜ` of `σ⁻` is the only split of `σ⁻`
separating some quartet `aa'|bb'`. -/
theorem exists_distinguishing_quartet (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA₁ : 2 ≤ #A) (hA₂ : 2 ≤ #Aᶜ) :
    ∃ a ∈ A, ∃ a' ∈ A, ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, a ≠ a' ∧ b ≠ b' ∧
      ∀ C ∈ unroot σ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A := by
  rcases steel_mem_unroot.1 hA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩
  · exact steel_distinguishing_of_mem_clusters σ hA1 hA2 hA₁ hA₂
  · obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, h⟩ :=
      steel_distinguishing_of_mem_clusters σ hA1 hA2 hA₂ (by rwa [compl_compl])
    rw [compl_compl] at hb hb'
    refine ⟨b, hb, b', hb', a, ha, a', ha', hbb, haa, ?_⟩
    intro C hC hbC hb'C haC ha'C
    have := h Cᶜ (steel_compl_mem_unroot hC) (mem_compl.2 haC) (mem_compl.2 ha'C)
      (fun h' => mem_compl.1 h' hbC) (fun h' => mem_compl.1 h' hb'C)
    exact compl_injective this

omit [Fintype X] in
/-- Two sets with the same trace on `S` contain the same taxa of `S`. -/
private theorem steel_mem_iff_of_subtype_eq {S A C : Finset X}
    (h : C.subtype (· ∈ S) = A.subtype (· ∈ S)) {x : X} (hx : x ∈ S) : x ∈ C ↔ x ∈ A := by
  have h1 : (⟨x, hx⟩ : S) ∈ C.subtype (· ∈ S) ↔ (⟨x, hx⟩ : S) ∈ A.subtype (· ∈ S) := by
    rw [h]
  simpa only [mem_subtype] using h1

/-- The trace of a complement is the complement of the trace. -/
private theorem steel_subtype_compl (S A : Finset X) :
    Aᶜ.subtype (· ∈ S) = (A.subtype (· ∈ S))ᶜ := by
  ext ⟨x, hx⟩
  simp

/-- The two sides of a split have the same unrooted length. -/
private theorem steel_unrootedLength_compl (τ : SpeciesTree X) (A : Finset X) :
    τ.unrootedLength Aᶜ = τ.unrootedLength A := by
  unfold SpeciesTree.unrootedLength
  rw [compl_compl]
  refine sum_congr ?_ fun _ _ => rfl
  ext C
  simp only [mem_filter]
  tauto

omit [Fintype X] in
/-- Four distinct taxa form a set of four taxa. -/
private theorem steel_card_quartet {a a' b b' : X} (haa : a ≠ a') (hab : a ≠ b) (hab' : a ≠ b')
    (ha'b : a' ≠ b) (ha'b' : a' ≠ b') (hbb : b ≠ b') : #({a, a', b, b'} : Finset X) = 4 := by
  rw [card_insert_of_notMem, card_insert_of_notMem, card_pair hbb]
  · simp [ha'b, ha'b']
  · simp [haa, hab, hab']

/-- If a split `A` of `σ⁻` separates `aa'|bb'`, and `σ` and `σ'` induce the same unrooted tree on
a set `Q` containing `a, a', b, b'`, then some split of `σ'⁻` separates `aa'|bb'`. -/
private theorem steel_separating_of_restrict (σ σ' : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) {a a' b b' : X} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∉ A)
    (hb' : b' ∉ A) {Q : Finset X} (hQ : Q.Nonempty) (haQ : a ∈ Q) (ha'Q : a' ∈ Q)
    (hbQ : b ∈ Q) (hb'Q : b' ∈ Q)
    (hU : unroot (σ.restrict Q hQ).clusters = unroot (σ'.restrict Q hQ).clusters) :
    ∃ C ∈ unroot σ'.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C ∧ b' ∉ C := by
  have h1 : A.subtype (· ∈ Q) ∈ restrictSplits Q (unroot σ'.clusters) := by
    rw [← SpeciesTree.restrict_unroot σ' Q hQ, ← hU, SpeciesTree.restrict_unroot]
    exact mem_image.2 ⟨A, mem_filter.2 ⟨hA, ⟨a, mem_inter.2 ⟨ha, haQ⟩⟩,
      ⟨b, mem_inter.2 ⟨mem_compl.2 hb, hbQ⟩⟩⟩, rfl⟩
  unfold restrictSplits at h1
  obtain ⟨C, hC, hCA⟩ := mem_image.1 h1
  have key : ∀ x ∈ Q, x ∈ C ↔ x ∈ A := fun x hx => steel_mem_iff_of_subtype_eq hCA hx
  exact ⟨C, (mem_filter.1 hC).1, (key a haQ).2 ha, (key a' ha'Q).2 ha',
    fun h => hb ((key b hbQ).1 h), fun h => hb' ((key b' hb'Q).1 h)⟩

/-- If `σ` and `σ'` induce the same unrooted trees on all sets of four taxa, every split of `σ⁻`
is a split of `σ'⁻`. -/
private theorem steel_unroot_subset (σ σ' : SpeciesTree X)
    (h : ∀ Q : Finset X, ∀ hQ : Q.Nonempty, #Q = 4 →
      unroot (σ.restrict Q hQ).clusters = unroot (σ'.restrict Q hQ).clusters) :
    unroot σ.clusters ⊆ unroot σ'.clusters := by
  intro A hA
  have hAne := steel_nonempty_of_mem_unroot σ hA
  have hAcne := steel_nonempty_of_mem_unroot σ (steel_compl_mem_unroot hA)
  by_cases h1 : #A ≤ 1
  · obtain ⟨x, rfl⟩ := card_eq_one.1 (le_antisymm h1 (card_pos.2 hAne))
    refine steel_mem_unroot.2 (Or.inl ⟨σ'.singleton_mem x, ?_⟩)
    intro hu
    rw [hu, compl_univ] at hAcne
    exact not_nonempty_empty hAcne
  by_cases h2 : #Aᶜ ≤ 1
  · obtain ⟨x, hx⟩ := card_eq_one.1 (le_antisymm h2 (card_pos.2 hAcne))
    refine steel_mem_unroot.2 (Or.inr ⟨hx ▸ σ'.singleton_mem x, ?_⟩)
    intro hu
    have : A = ∅ := by rw [← compl_compl A, hu, compl_univ]
    exact hAne.ne_empty this
  rw [mem_unroot_iff_quartets σ' (by omega) (by omega)]
  intro a ha a' ha' b hb b' hb' haa hbb
  rw [mem_compl] at hb hb'
  have hQ : ({a, a', b, b'} : Finset X).Nonempty := insert_nonempty _ _
  have hab : a ≠ b := by rintro rfl; exact hb ha
  have hab' : a ≠ b' := by rintro rfl; exact hb' ha
  have ha'b : a' ≠ b := by rintro rfl; exact hb ha'
  have ha'b' : a' ≠ b' := by rintro rfl; exact hb' ha'
  exact steel_separating_of_restrict σ σ' hA ha ha' hb hb' hQ (by simp) (by simp) (by simp)
    (by simp) (h _ hQ (steel_card_quartet haa hab hab' ha'b ha'b' hbb))

/-- Unrooted metric trees are determined by their quartets. -/
theorem SpeciesTree.sameUnrootedMetricTree_of_restrict (σ σ' : SpeciesTree X)
    (h : ∀ Q : Finset X, ∀ hQ : Q.Nonempty, #Q = 4 →
      (σ.restrict Q hQ).SameUnrootedMetricTree (σ'.restrict Q hQ)) :
    σ.SameUnrootedMetricTree σ' := by
  have hU : unroot σ.clusters = unroot σ'.clusters :=
    Subset.antisymm (steel_unroot_subset σ σ' fun Q hQ hQ4 => (h Q hQ hQ4).1)
      (steel_unroot_subset σ' σ fun Q hQ hQ4 => (h Q hQ hQ4).1.symm)
  refine ⟨hU, ?_⟩
  intro A hA hA₁ hA₂
  have hAne := steel_nonempty_of_mem_unroot σ hA
  obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, huniq⟩ :=
    exists_distinguishing_quartet σ hA hA₁ hA₂
  rw [mem_compl] at hb hb'
  have hab : a ≠ b := by rintro rfl; exact hb ha
  have hab' : a ≠ b' := by rintro rfl; exact hb' ha
  have ha'b : a' ≠ b := by rintro rfl; exact hb ha'
  have ha'b' : a' ≠ b' := by rintro rfl; exact hb' ha'
  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset X, Q = {a, a', b, b'} := ⟨_, rfl⟩
  have hQ : Q.Nonempty := hQdef ▸ insert_nonempty _ _
  have haQ : a ∈ Q := by simp [hQdef]
  have ha'Q : a' ∈ Q := by simp [hQdef]
  have hbQ : b ∈ Q := by simp [hQdef]
  have hb'Q : b' ∈ Q := by simp [hQdef]
  obtain ⟨hUQ, hLQ⟩ := h Q hQ (hQdef ▸ steel_card_quartet haa hab hab' ha'b ha'b' hbb)
  -- the split of the induced quartet tree induced by `A`
  have hC₀ : A.subtype (· ∈ Q) ∈ unroot (σ.restrict Q hQ).clusters := by
    rw [SpeciesTree.restrict_unroot]
    exact mem_image.2 ⟨A, mem_filter.2 ⟨hA, ⟨a, mem_inter.2 ⟨ha, haQ⟩⟩,
      ⟨b, mem_inter.2 ⟨mem_compl.2 hb, hbQ⟩⟩⟩, rfl⟩
  have hC₀₁ : 2 ≤ #(A.subtype (· ∈ Q)) :=
    one_lt_card.2 ⟨⟨a, haQ⟩, mem_subtype.2 ha, ⟨a', ha'Q⟩, mem_subtype.2 ha',
      fun h => haa (congrArg Subtype.val h)⟩
  have hC₀₂ : 2 ≤ #(A.subtype (· ∈ Q))ᶜ :=
    one_lt_card.2 ⟨⟨b, hbQ⟩, by simp [hb], ⟨b', hb'Q⟩, by simp [hb'],
      fun h => hbb (congrArg Subtype.val h)⟩
  have hAA : A ≠ Aᶜ := by
    intro h
    obtain ⟨x, hx⟩ := hAne
    have hx' := hx
    rw [h] at hx'
    exact mem_compl.1 hx' hx
  -- the length of the split induced by `A` in an induced quartet tree is the length of `A`
  have hlen : ∀ τ : SpeciesTree X, A ∈ unroot τ.clusters →
      (∀ C ∈ unroot τ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A) →
      A.subtype (· ∈ Q) ∈ unroot (τ.restrict Q hQ).clusters →
      (τ.restrict Q hQ).unrootedLength (A.subtype (· ∈ Q)) = τ.unrootedLength A := by
    intro τ hAτ huniqτ hCτ
    rw [τ.restrict_unrootedLength Q hQ _ hCτ hC₀₁ hC₀₂]
    have hfilter : (unroot τ.clusters).filter (fun B => B.subtype (· ∈ Q) = A.subtype (· ∈ Q) ∨
        B.subtype (· ∈ Q) = (A.subtype (· ∈ Q))ᶜ) = {A, Aᶜ} := by
      ext B
      rw [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hB, hB1 | hB1⟩
        · left
          have key : ∀ x ∈ Q, x ∈ B ↔ x ∈ A := fun x hx => steel_mem_iff_of_subtype_eq hB1 hx
          exact huniqτ B hB ((key a haQ).2 ha) ((key a' ha'Q).2 ha')
            (fun h => hb ((key b hbQ).1 h)) (fun h => hb' ((key b' hb'Q).1 h))
        · right
          have hB2 : Bᶜ.subtype (· ∈ Q) = A.subtype (· ∈ Q) := by
            rw [steel_subtype_compl, hB1, compl_compl]
          have key : ∀ x ∈ Q, x ∈ Bᶜ ↔ x ∈ A := fun x hx => steel_mem_iff_of_subtype_eq hB2 hx
          have := huniqτ Bᶜ (steel_compl_mem_unroot hB) ((key a haQ).2 ha) ((key a' ha'Q).2 ha')
            (fun h => hb ((key b hbQ).1 h)) (fun h => hb' ((key b' hb'Q).1 h))
          rw [← this, compl_compl]
      · rintro (rfl | rfl)
        · exact ⟨hAτ, Or.inl rfl⟩
        · exact ⟨steel_compl_mem_unroot hAτ, Or.inr (steel_subtype_compl _ _)⟩
    rw [hfilter, sum_pair hAA, steel_unrootedLength_compl]
    ring
  have hA' : A ∈ unroot σ'.clusters := hU ▸ hA
  have huniq' : ∀ C ∈ unroot σ'.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A := by
    rw [← hU]
    exact huniq
  rw [← hlen σ hA huniq hC₀, ← hlen σ' hA' huniq' (hUQ ▸ hC₀)]
  exact hLQ _ hC₀ hC₀₁ hC₀₂

end ADR11
