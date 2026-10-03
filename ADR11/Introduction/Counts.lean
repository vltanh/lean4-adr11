module

public import ADR11.Trees.Hierarchy

/-!
# Section 1: counting rooted and unrooted gene trees

"For `n` species, there are `(2n-5)!!` unrooted gene trees, and each unrooted gene tree can be
realized by `2n-3` rooted gene trees, corresponding to choices of an edge on which to place the
root" (Section 1, with the count `(2n-3)!!` of rooted binary topologies cited from
[Felsenstein 2004]).

* `IsBinaryHierarchy G`: `G` is a rooted binary tree on the leaves `L`, given by its clusters.
* `section1_card_rooted`: there are `(2n-3)!!` rooted binary trees on `n ≥ 1` labelled leaves.
* `section1_card_rootings`: each unrooted binary tree on `n ≥ 2` leaves has `2n-3` rooted versions.
* `section1_card_unrooted`: there are `(2n-5)!!` unrooted binary trees on `n ≥ 3` leaves.

## Proof

* `counts_card_eq`: a binary hierarchy on `n ≥ 1` leaves has `2n - 1` clusters. Its two clusters
  below the root (`counts_rootChildren`) form the only complementary pair of clusters, so its
  unrooted tree has `2(2n - 3)` sides of splits (`counts_card_unroot`).
* `counts_reroot T A`: the rooting of the unrooted tree `T` on the edge of the split `A | Aᶜ`, the
  root together with the sides of splits contained in `A` or in `Aᶜ`. It is a rooted binary tree
  with unrooted tree `T` (`counts_reroot_spec`, using `counts_unroot_split`), and it is the only
  one in which `A` and `Aᶜ` are clusters (`counts_reroot_unroot`). Counting the pairs of a rooting
  and a cluster below its root in two ways gives `counts_card_rootings`.
* `counts_ext G`: adding the leaf `Fin.last n` as a child of the root; `counts_res`: removing it.
  Rooting on the pendant edge of the leaf `n + 1`, the unrooted binary trees on `n + 1` leaves
  correspond to the rooted binary trees on `n` leaves (`counts_card_unrooted_succ`).
* Hence the number of rooted binary trees on `n + 1` leaves is `2n - 1` times the number of
  unrooted ones (`counts_card_rooted_eq_mul`), that is, `2n - 1` times the number of rooted
  binary trees on `n` leaves.
-/

@[expose] public section

namespace ADR11

open Finset

/-- A rooted binary tree on the leaves `L`, given by its clusters: a hierarchy in which every
cluster with at least two leaves is the union of two disjoint clusters. -/
def IsBinaryHierarchy {L : Type*} [Fintype L] [DecidableEq L] (G : Finset (Finset L)) : Prop :=
  IsHierarchy G ∧ ∀ A ∈ G, 2 ≤ #A → ∃ B ∈ G, ∃ C ∈ G, Disjoint B C ∧ B ∪ C = A

section General

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- A cluster contained in the union of two disjoint clusters `B`, `C` of a hierarchy is the
union itself, or is contained in `B` or in `C`. -/
theorem counts_subset_union_cases {G : Finset (Finset L)} (hG : IsHierarchy G) {B C D : Finset L}
    (hB : B ∈ G) (hC : C ∈ G) (hBC : Disjoint B C) (hD : D ∈ G) (hDA : D ⊆ B ∪ C) :
    D = B ∪ C ∨ D ⊆ B ∨ D ⊆ C := by
  rcases hG.2.2.2 D hD B hB with h | h | h
  · exact Or.inr (Or.inl h)
  · rcases hG.2.2.2 D hD C hC with h' | h' | h'
    · exfalso
      obtain ⟨b, hb⟩ := hG.2.2.1 B hB
      exact disjoint_left.1 hBC hb (h' (h hb))
    · exact Or.inl (Subset.antisymm hDA (union_subset h h'))
    · refine Or.inr (Or.inl fun x hx => ?_)
      rcases mem_union.1 (hDA hx) with hxB | hxC
      · exact hxB
      · exact absurd hxC (disjoint_left.1 h' hx)
  · refine Or.inr (Or.inr fun x hx => ?_)
    rcases mem_union.1 (hDA hx) with hxB | hxC
    · exact absurd hxB (disjoint_left.1 h hx)
    · exact hxC

/-- A binary hierarchy has `2|A| - 1` clusters contained in a cluster `A`. -/
theorem counts_card_filter_subset {G : Finset (Finset L)} (hG : IsBinaryHierarchy G)
    {A : Finset L} (hA : A ∈ G) : #(G.filter (· ⊆ A)) = 2 * #A - 1 := by
  induction A using Finset.strongInduction with
  | H A ih =>
  have hne : A.Nonempty := hG.1.2.2.1 A hA
  by_cases h2 : 2 ≤ #A
  · obtain ⟨B, hB, C, hC, hBC, hBCA⟩ := hG.2 A hA h2
    have hBne := hG.1.2.2.1 B hB
    have hCne := hG.1.2.2.1 C hC
    have hBA : B ⊂ A := by
      refine ssubset_of_subset_not_subset (hBCA ▸ subset_union_left) fun h => ?_
      obtain ⟨c, hc⟩ := hCne
      exact disjoint_left.1 hBC (h (hBCA ▸ mem_union_right B hc)) hc
    have hCA : C ⊂ A := by
      refine ssubset_of_subset_not_subset (hBCA ▸ subset_union_right) fun h => ?_
      obtain ⟨b, hb⟩ := hBne
      exact disjoint_left.1 hBC hb (h (hBCA ▸ mem_union_left C hb))
    have hsplit : G.filter (· ⊆ A) = insert A (G.filter (· ⊆ B) ∪ G.filter (· ⊆ C)) := by
      ext D
      simp only [mem_filter, mem_insert, mem_union]
      constructor
      · rintro ⟨hD, hDA⟩
        rcases counts_subset_union_cases hG.1 hB hC hBC hD (hBCA ▸ hDA) with h | h | h
        · exact Or.inl (h.trans hBCA)
        · exact Or.inr (Or.inl ⟨hD, h⟩)
        · exact Or.inr (Or.inr ⟨hD, h⟩)
      · rintro (rfl | ⟨hD, h⟩ | ⟨hD, h⟩)
        · exact ⟨hA, Subset.rfl⟩
        · exact ⟨hD, h.trans hBA.subset⟩
        · exact ⟨hD, h.trans hCA.subset⟩
    have hdisj : Disjoint (G.filter (· ⊆ B)) (G.filter (· ⊆ C)) := by
      refine disjoint_left.2 fun D hDB hDC => ?_
      obtain ⟨d, hd⟩ := hG.1.2.2.1 D (mem_filter.1 hDB).1
      exact disjoint_left.1 hBC ((mem_filter.1 hDB).2 hd) ((mem_filter.1 hDC).2 hd)
    have hAnot : A ∉ G.filter (· ⊆ B) ∪ G.filter (· ⊆ C) := by
      rw [mem_union, mem_filter, mem_filter]
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact not_subset_of_ssubset hBA h
      · exact not_subset_of_ssubset hCA h
    rw [hsplit, card_insert_of_notMem hAnot, card_union_of_disjoint hdisj, ih B hBA hB,
      ih C hCA hC, ← hBCA, card_union_of_disjoint hBC]
    have := hBne.card_pos
    have := hCne.card_pos
    omega
  · have h1 : #A = 1 := by
      have := hne.card_pos
      omega
    obtain ⟨a, rfl⟩ := card_eq_one.1 h1
    have : G.filter (· ⊆ {a}) = {{a}} := by
      ext D
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hD, hDa⟩
        exact (subset_singleton_iff.1 hDa).resolve_left (hG.1.2.2.1 D hD).ne_empty
      · rintro rfl
        exact ⟨hA, Subset.rfl⟩
    rw [this, card_singleton, card_singleton]

/-- A binary hierarchy on `n` leaves has `2n - 1` clusters. -/
theorem counts_card_eq {G : Finset (Finset L)} (hG : IsBinaryHierarchy G) :
    #G = 2 * Fintype.card L - 1 := by
  have h := counts_card_filter_subset hG hG.1.1
  rwa [card_univ, filter_true_of_mem (fun D _ => subset_univ D)] at h

/-- The two clusters below the root: the clusters `A ≠ univ` whose complement is a cluster. -/
def counts_rootChildren (G : Finset (Finset L)) : Finset (Finset L) :=
  G.filter fun A => A ≠ univ ∧ Aᶜ ∈ G

/-- A binary hierarchy on at least two leaves has exactly two clusters below the root. -/
theorem counts_card_rootChildren {G : Finset (Finset L)} (hG : IsBinaryHierarchy G)
    (hL : 2 ≤ Fintype.card L) : #(counts_rootChildren G) = 2 := by
  obtain ⟨B, hB, C, hC, hBC, hBCu⟩ := hG.2 univ hG.1.1 (by rwa [card_univ])
  have hBne := hG.1.2.2.1 B hB
  have hCne := hG.1.2.2.1 C hC
  have hBu : B ≠ univ := by
    rintro rfl
    obtain ⟨c, hc⟩ := hCne
    exact disjoint_left.1 hBC (mem_univ c) hc
  have hCu : C ≠ univ := by
    rintro rfl
    obtain ⟨b, hb⟩ := hBne
    exact disjoint_left.1 hBC hb (mem_univ b)
  have hBc : Bᶜ = C := by
    ext x
    rw [mem_compl]
    constructor
    · intro hx
      have := hBCu ▸ mem_univ x
      exact (mem_union.1 this).resolve_left hx
    · intro hx hxB
      exact disjoint_left.1 hBC hxB hx
  have hCc : Cᶜ = B := by rw [← hBc, compl_compl]
  have hBC' : B ≠ C := by
    rintro rfl
    obtain ⟨b, hb⟩ := hBne
    exact disjoint_left.1 hBC hb hb
  suffices h : counts_rootChildren G = {B, C} by
    rw [h, card_pair hBC']
  ext A
  simp only [counts_rootChildren, mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hA, hAu, hAc⟩
    have hAne := hG.1.2.2.1 A hA
    have hAcu : Aᶜ ≠ univ := (compl_ne_univ_iff_nonempty A).2 hAne
    rcases counts_subset_union_cases hG.1 hB hC hBC hA (hBCu ▸ subset_univ A) with h | h | h
    · exact absurd (h.trans hBCu) hAu
    · rcases counts_subset_union_cases hG.1 hB hC hBC hAc (hBCu ▸ subset_univ _) with h' | h' | h'
      · exact absurd (h'.trans hBCu) hAcu
      · exfalso
        refine hBu (eq_univ_iff_forall.2 fun x => ?_)
        by_cases hx : x ∈ A
        · exact h hx
        · exact h' (mem_compl.2 hx)
      · left
        refine Subset.antisymm h fun x hxB => ?_
        by_contra hxA
        exact disjoint_left.1 hBC hxB (h' (mem_compl.2 hxA))
    · rcases counts_subset_union_cases hG.1 hB hC hBC hAc (hBCu ▸ subset_univ _) with h' | h' | h'
      · exact absurd (h'.trans hBCu) hAcu
      · right
        refine Subset.antisymm h fun x hxC => ?_
        by_contra hxA
        exact disjoint_left.1 hBC (h' (mem_compl.2 hxA)) hxC
      · exfalso
        refine hCu (eq_univ_iff_forall.2 fun x => ?_)
        by_cases hx : x ∈ A
        · exact h hx
        · exact h' (mem_compl.2 hx)
  · rintro (rfl | rfl)
    · exact ⟨hB, hBu, hBc ▸ hC⟩
    · exact ⟨hC, hCu, hCc ▸ hB⟩

/-- The sides of the splits of the unrooted tree of a hierarchy are nonempty proper subsets. -/
theorem counts_nonempty_of_mem_unroot {G : Finset (Finset L)} (hG : IsHierarchy G)
    {A : Finset L} (hA : A ∈ unroot G) : A.Nonempty ∧ A ≠ univ := by
  rcases mem_unroot.1 hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨hG.2.2.1 A h1, h2⟩
  · refine ⟨(compl_ne_univ_iff_nonempty A).1 h2, ?_⟩
    rintro rfl
    rw [compl_univ] at h1
    exact not_nonempty_empty (hG.2.2.1 _ h1)

/-- The unrooted tree of a binary hierarchy on `n ≥ 2` leaves has `2(2n - 3)` sides of splits. -/
theorem counts_card_unroot {G : Finset (Finset L)} (hG : IsBinaryHierarchy G)
    (hL : 2 ≤ Fintype.card L) : #(unroot G) = 2 * (2 * Fintype.card L - 3) := by
  have hE : #(G.erase univ) = 2 * Fintype.card L - 2 := by
    rw [card_erase_of_mem hG.1.1, counts_card_eq hG]
    omega
  have hI : #((G.erase univ).image compl) = 2 * Fintype.card L - 2 := by
    rw [card_image_of_injective _ compl_injective, hE]
  have hinter : G.erase univ ∩ (G.erase univ).image compl = counts_rootChildren G := by
    ext A
    simp only [mem_inter, mem_erase, mem_image, counts_rootChildren, mem_filter]
    constructor
    · rintro ⟨⟨hAu, hA⟩, D, ⟨-, hD⟩, rfl⟩
      exact ⟨hA, hAu, by rwa [compl_compl]⟩
    · rintro ⟨hA, hAu, hAc⟩
      refine ⟨⟨hAu, hA⟩, Aᶜ, ⟨?_, hAc⟩, compl_compl A⟩
      exact (compl_ne_univ_iff_nonempty A).2 (hG.1.2.2.1 A hA)
  have h := card_union_add_card_inter (G.erase univ) ((G.erase univ).image compl)
  rw [hinter, counts_card_rootChildren hG hL, hE, hI] at h
  unfold unroot
  omega

/-- Each side `D` with at least two elements of a split of the unrooted tree of a binary
hierarchy is the disjoint union of two sides of splits (the far sides of the two other edges at
the endpoint of the edge of `D` on the side of `D`). -/
theorem counts_unroot_split {G : Finset (Finset L)} (hG : IsBinaryHierarchy G) {D : Finset L}
    (hD : D ∈ unroot G) (h2 : 2 ≤ #D) :
    ∃ B ∈ unroot G, ∃ C ∈ unroot G, Disjoint B C ∧ B ∪ C = D := by
  have case1 : ∀ D, D ∈ G → D ≠ univ → 2 ≤ #D →
      ∃ B ∈ unroot G, ∃ C ∈ unroot G, Disjoint B C ∧ B ∪ C = D := by
    intro D hD hDu h2
    obtain ⟨B, hB, C, hC, hBC, hBCD⟩ := hG.2 D hD h2
    refine ⟨B, mem_unroot.2 (Or.inl ⟨hB, ?_⟩), C, mem_unroot.2 (Or.inl ⟨hC, ?_⟩), hBC, hBCD⟩
    · rintro rfl
      exact hDu (univ_subset_iff.1 (hBCD ▸ subset_union_left))
    · rintro rfl
      exact hDu (univ_subset_iff.1 (hBCD ▸ subset_union_right))
  rcases mem_unroot.1 hD with ⟨hD', hDu⟩ | ⟨hD', hDu⟩
  · exact case1 D hD' hDu h2
  · have hP := hG.1.parentCluster_mem hD' hDu
    have hDP := hG.1.ssubset_parentCluster hD' hDu
    have hP2 : 2 ≤ #(parentCluster G Dᶜ) := by
      have h1 := card_lt_card hDP
      have h2 := (hG.1.2.2.1 _ hD').card_pos
      omega
    obtain ⟨B, hB, C, hC, hBC, hBCP⟩ := hG.2 _ hP hP2
    have hmem := hG.1.mem_childClusters_parentCluster hD' hDu
    rw [hG.1.childClusters_eq_pair hB hC hBC hBCP] at hmem
    -- the cluster `Dᶜ` is a child `B'` of its parent, with sibling `C'`
    have key : ∀ B' C', B' ∈ G → C' ∈ G → Disjoint B' C' → B' ∪ C' = parentCluster G Dᶜ →
        Dᶜ = B' → ∃ B ∈ unroot G, ∃ C ∈ unroot G, Disjoint B C ∧ B ∪ C = D := by
      intro B' C' hB' hC' hB'C' hP' hDB'
      have hC'u : C' ≠ univ := by
        rintro rfl
        obtain ⟨b, hb⟩ := hG.1.2.2.1 B' hB'
        exact disjoint_left.1 hB'C' hb (mem_univ b)
      by_cases hPu : parentCluster G Dᶜ = univ
      · -- the parent is the root: `D` is the sibling `C'`
        have hDC' : D = C' := by
          ext x
          constructor
          · intro hx
            have : x ∈ B' ∪ C' := hP' ▸ hPu ▸ mem_univ x
            refine (mem_union.1 this).resolve_left fun hxB => ?_
            rw [← hDB', mem_compl] at hxB
            exact hxB hx
          · intro hx
            by_contra hxD
            rw [← mem_compl, hDB'] at hxD
            exact disjoint_left.1 hB'C' hxD hx
        subst hDC'
        exact case1 D hC' hC'u h2
      · refine ⟨(parentCluster G Dᶜ)ᶜ,
          compl_mem_unroot.2 (mem_unroot.2 (Or.inl ⟨hP, hPu⟩)), C',
          mem_unroot.2 (Or.inl ⟨hC', hC'u⟩), ?_, ?_⟩
        · rw [← hP']
          exact disjoint_left.2 fun x hx hxC => mem_compl.1 hx (mem_union_right _ hxC)
        · rw [← hP', show D = B'ᶜ by rw [← hDB', compl_compl]]
          ext x
          simp only [mem_union, mem_compl]
          constructor
          · rintro (hx | hx)
            · exact fun hxB => hx (Or.inl hxB)
            · exact fun hxB => disjoint_left.1 hB'C' hxB hx
          · intro hxB
            by_cases hxC : x ∈ C'
            · exact Or.inr hxC
            · exact Or.inl fun h => h.elim hxB hxC
    rcases mem_insert.1 hmem with h | h
    · exact key B C hB hC hBC hBCP h
    · rw [mem_singleton] at h
      exact key C B hC hB hBC.symm (union_comm B C ▸ hBCP) h

/-- The rooting of an unrooted tree `T` on the edge of the split `A | Aᶜ`: the root, together
with the sides of splits contained in `A` or in `Aᶜ`. -/
def counts_reroot (T : Finset (Finset L)) (A : Finset L) : Finset (Finset L) :=
  insert univ (T.filter fun C => C ⊆ A ∨ C ⊆ Aᶜ)

theorem counts_mem_reroot {T : Finset (Finset L)} {A C : Finset L} :
    C ∈ counts_reroot T A ↔ C = univ ∨ (C ∈ T ∧ (C ⊆ A ∨ C ⊆ Aᶜ)) := by
  rw [counts_reroot, mem_insert, mem_filter]

/-- The rooting of the unrooted tree of a binary hierarchy on the edge of any of its splits is a
binary hierarchy with the same unrooted tree. -/
theorem counts_reroot_spec {G : Finset (Finset L)} (hG : IsBinaryHierarchy G)
    (hL : 2 ≤ Fintype.card L) {A : Finset L} (hA : A ∈ unroot G) :
    IsBinaryHierarchy (counts_reroot (unroot G) A) ∧
      unroot (counts_reroot (unroot G) A) = unroot G := by
  obtain ⟨hAne, hAu⟩ := counts_nonempty_of_mem_unroot hG.1 hA
  have hAc : Aᶜ ∈ unroot G := compl_mem_unroot.2 hA
  have hAcu : Aᶜ ≠ univ := (compl_ne_univ_iff_nonempty A).2 hAne
  have hT : ∀ {C}, C ∈ unroot G → C.Nonempty ∧ C ≠ univ := fun hC =>
    counts_nonempty_of_mem_unroot hG.1 hC
  refine ⟨⟨⟨counts_mem_reroot.2 (Or.inl rfl), fun x => ?_, fun C hC => ?_, fun C hC D hD => ?_⟩,
    fun C hC h2 => ?_⟩, ?_⟩
  · -- singletons
    refine counts_mem_reroot.2 (Or.inr ⟨mem_unroot.2 (Or.inl ⟨hG.1.2.1 x, fun h => ?_⟩), ?_⟩)
    · have := congrArg card h
      rw [card_singleton, card_univ] at this
      omega
    · by_cases hx : x ∈ A
      · exact Or.inl (singleton_subset_iff.2 hx)
      · exact Or.inr (singleton_subset_iff.2 (mem_compl.2 hx))
  · -- nonempty
    rcases counts_mem_reroot.1 hC with rfl | ⟨hC, -⟩
    · exact card_pos.1 (by rw [card_univ]; omega)
    · exact (hT hC).1
  · -- laminar
    rcases counts_mem_reroot.1 hC with rfl | ⟨hC, hCs⟩
    · exact Or.inr (Or.inl (subset_univ D))
    rcases counts_mem_reroot.1 hD with rfl | ⟨hD, hDs⟩
    · exact Or.inl (subset_univ C)
    have hsame : ∀ S : Finset L, S ≠ univ → C ⊆ S → D ⊆ S →
        C ⊆ D ∨ D ⊆ C ∨ Disjoint C D := by
      intro S hS hCS hDS
      rcases hG.1.compatible_of_mem_unroot hC hD with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd (univ_subset_iff.1 (h ▸ union_subset hCS hDS)) hS
    rcases hCs with hCs | hCs <;> rcases hDs with hDs | hDs
    · exact hsame A hAu hCs hDs
    · exact Or.inr (Or.inr (Disjoint.mono hCs hDs disjoint_compl_right))
    · exact Or.inr (Or.inr (Disjoint.mono hCs hDs disjoint_compl_left))
    · exact hsame Aᶜ hAcu hCs hDs
  · -- binary
    rcases counts_mem_reroot.1 hC with rfl | ⟨hC, hCs⟩
    · exact ⟨A, counts_mem_reroot.2 (Or.inr ⟨hA, Or.inl Subset.rfl⟩), Aᶜ,
        counts_mem_reroot.2 (Or.inr ⟨hAc, Or.inr Subset.rfl⟩), disjoint_compl_right,
        union_compl A⟩
    · obtain ⟨B, hB, D, hD, hBD, hBDC⟩ := counts_unroot_split hG hC h2
      have hBC : B ⊆ C := hBDC ▸ subset_union_left
      have hDC : D ⊆ C := hBDC ▸ subset_union_right
      refine ⟨B, counts_mem_reroot.2 (Or.inr ⟨hB, ?_⟩), D,
        counts_mem_reroot.2 (Or.inr ⟨hD, ?_⟩), hBD, hBDC⟩
      · rcases hCs with h | h
        · exact Or.inl (hBC.trans h)
        · exact Or.inr (hBC.trans h)
      · rcases hCs with h | h
        · exact Or.inl (hDC.trans h)
        · exact Or.inr (hDC.trans h)
  · -- the unrooted tree
    ext X
    rw [mem_unroot, counts_mem_reroot, counts_mem_reroot]
    constructor
    · rintro (⟨h | ⟨hX, -⟩, hXu⟩ | ⟨h | ⟨hX, -⟩, hXu⟩)
      · exact absurd h hXu
      · exact hX
      · exact absurd h hXu
      · exact compl_mem_unroot.1 hX
    · intro hX
      obtain ⟨hXne, hXu⟩ := hT hX
      have hXcu : Xᶜ ≠ univ := (compl_ne_univ_iff_nonempty X).2 hXne
      have hXc : Xᶜ ∈ unroot G := compl_mem_unroot.2 hX
      rcases hG.1.compatible_of_mem_unroot hX hA with h | h | h | h
      · exact Or.inl ⟨Or.inr ⟨hX, Or.inl h⟩, hXu⟩
      · exact Or.inr ⟨Or.inr ⟨hXc, Or.inr (compl_subset_compl.2 h)⟩, hXcu⟩
      · exact Or.inl ⟨Or.inr ⟨hX, Or.inr (subset_compl_iff_disjoint_right.2 h)⟩, hXu⟩
      · refine Or.inr ⟨Or.inr ⟨hXc, Or.inl fun x hx => ?_⟩, hXcu⟩
        have : x ∈ X ∪ A := h ▸ mem_univ x
        exact (mem_union.1 this).resolve_left (mem_compl.1 hx)

/-- In a hierarchy, a side of a split contained in a cluster `A ≠ univ` is a cluster. -/
theorem counts_mem_of_mem_unroot_of_subset {G : Finset (Finset L)} (hG : IsHierarchy G)
    {A C : Finset L} (hA : A ∈ G) (hAu : A ≠ univ) (hC : C ∈ unroot G) (hCA : C ⊆ A) :
    C ∈ G := by
  rcases mem_unroot.1 hC with ⟨h, -⟩ | ⟨h, hu⟩
  · exact h
  · rcases hG.2.2.2 _ h A hA with h' | h' | h'
    · exfalso
      refine hAu (eq_univ_iff_forall.2 fun x => ?_)
      by_contra hx
      exact hx (h' (compl_subset_compl.2 hCA (mem_compl.2 hx)))
    · exfalso
      refine hu (eq_univ_iff_forall.2 fun x => ?_)
      rw [mem_compl]
      intro hx
      exact mem_compl.1 (h' (hCA hx)) hx
    · have : Cᶜ = Aᶜ := Subset.antisymm (subset_compl_iff_disjoint_right.2 h')
        (compl_subset_compl.2 hCA)
      rw [compl_inj_iff.1 this]
      exact hA

/-- A hierarchy with two complementary clusters `A`, `Aᶜ` is the rooting of its unrooted tree on
the edge of the split `A | Aᶜ`. -/
theorem counts_reroot_unroot {G : Finset (Finset L)} (hG : IsHierarchy G) {A : Finset L}
    (hA : A ∈ G) (hAu : A ≠ univ) (hAc : Aᶜ ∈ G) : counts_reroot (unroot G) A = G := by
  have hAne := hG.2.2.1 A hA
  have hAcu : Aᶜ ≠ univ := (compl_ne_univ_iff_nonempty A).2 hAne
  ext C
  rw [counts_mem_reroot]
  constructor
  · rintro (rfl | ⟨hC, hCA | hCA⟩)
    · exact hG.1
    · exact counts_mem_of_mem_unroot_of_subset hG hA hAu hC hCA
    · exact counts_mem_of_mem_unroot_of_subset hG hAc hAcu hC hCA
  · intro hC
    by_cases hCu : C = univ
    · exact Or.inl hCu
    refine Or.inr ⟨mem_unroot.2 (Or.inl ⟨hC, hCu⟩), ?_⟩
    rcases hG.2.2.2 C hC A hA with h | h | h
    · exact Or.inl h
    · rcases hG.2.2.2 C hC _ hAc with h' | h' | h'
      · exfalso
        obtain ⟨a, ha⟩ := hAne
        exact mem_compl.1 (h' (h ha)) ha
      · exfalso
        refine hCu (eq_univ_iff_forall.2 fun x => ?_)
        by_cases hx : x ∈ A
        · exact h hx
        · exact h' (mem_compl.2 hx)
      · exact Or.inl (disjoint_compl_right_iff.1 h')
    · exact Or.inr (subset_compl_iff_disjoint_right.2 h)

/-- An unrooted binary tree on `n ≥ 2` leaves has `2n - 3` rooted versions: the rootings are in
bijection with the splits, through the pair of clusters below the root. -/
theorem counts_card_rootings {G₀ : Finset (Finset L)} (hG₀ : IsBinaryHierarchy G₀)
    (hL : 2 ≤ Fintype.card L)
    [DecidablePred fun G : Finset (Finset L) => IsBinaryHierarchy G ∧ unroot G = unroot G₀] :
    #{G : Finset (Finset L) | IsBinaryHierarchy G ∧ unroot G = unroot G₀} =
      2 * Fintype.card L - 3 := by
  set S := ({G : Finset (Finset L) | IsBinaryHierarchy G ∧ unroot G = unroot G₀} :
    Finset (Finset (Finset L))) with hS
  -- double counting of the pairs `(G, A)` of a rooting `G` and a cluster `A` below its root
  have hcount := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun G A => A ∈ counts_rootChildren G) (s := S) (t := unroot G₀)
  have hleft : ∀ G ∈ S,
      #(bipartiteAbove (fun G A => A ∈ counts_rootChildren G) (unroot G₀) G) = 2 := by
    intro G hGS
    obtain ⟨hG, hGT⟩ := (mem_filter.1 hGS).2
    refine (congrArg card ?_).trans (counts_card_rootChildren hG hL)
    ext A
    rw [mem_bipartiteAbove, and_iff_right_iff_imp]
    intro hA
    obtain ⟨hA, hAu, -⟩ := mem_filter.1 hA
    exact hGT ▸ mem_unroot.2 (Or.inl ⟨hA, hAu⟩)
  have hright : ∀ A ∈ unroot G₀,
      #(bipartiteBelow (fun G A => A ∈ counts_rootChildren G) S A) = 1 := by
    intro A hA
    obtain ⟨hR, hRT⟩ := counts_reroot_spec hG₀ hL hA
    obtain ⟨-, hAu⟩ := counts_nonempty_of_mem_unroot hG₀.1 hA
    refine card_eq_one.2 ⟨counts_reroot (unroot G₀) A, ?_⟩
    ext G
    rw [mem_bipartiteBelow, mem_singleton, hS, mem_filter, counts_rootChildren, mem_filter]
    constructor
    · rintro ⟨⟨-, hG, hGT⟩, hAG, hAu, hAc⟩
      rw [← hGT, counts_reroot_unroot hG.1 hAG hAu hAc]
    · rintro rfl
      exact ⟨⟨mem_univ _, hR, hRT⟩, counts_mem_reroot.2 (Or.inr ⟨hA, Or.inl Subset.rfl⟩), hAu,
        counts_mem_reroot.2 (Or.inr ⟨compl_mem_unroot.2 hA, Or.inr Subset.rfl⟩)⟩
  rw [sum_const_nat hleft, sum_const_nat hright, counts_card_unroot hG₀ hL] at hcount
  omega

end General

section Fin

variable {n : ℕ}

/-- A set of leaves of `Fin n`, as a set of leaves of `Fin (n + 1)`. -/
def counts_lift (D : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  D.map Fin.castSuccEmb

theorem counts_castSucc_mem_lift {D : Finset (Fin n)} {i : Fin n} :
    i.castSucc ∈ counts_lift D ↔ i ∈ D := by
  simp [counts_lift]

theorem counts_last_notMem_lift (D : Finset (Fin n)) : Fin.last n ∉ counts_lift D := by
  simp [counts_lift, Fin.castSucc_ne_last]

theorem counts_lift_injective : Function.Injective (counts_lift (n := n)) :=
  map_injective _

theorem counts_lift_subset_lift {D E : Finset (Fin n)} :
    counts_lift D ⊆ counts_lift E ↔ D ⊆ E :=
  map_subset_map

theorem counts_disjoint_lift {D E : Finset (Fin n)} :
    Disjoint (counts_lift D) (counts_lift E) ↔ Disjoint D E :=
  disjoint_map _

theorem counts_lift_union (D E : Finset (Fin n)) :
    counts_lift (D ∪ E) = counts_lift D ∪ counts_lift E :=
  map_union _ _

theorem counts_card_lift (D : Finset (Fin n)) : #(counts_lift D) = #D :=
  card_map _

theorem counts_lift_univ : counts_lift (univ : Finset (Fin n)) = {Fin.last n}ᶜ := by
  ext x
  induction x using Fin.lastCases with
  | last => simp [counts_last_notMem_lift]
  | cast i => simp [counts_castSucc_mem_lift, Fin.castSucc_ne_last]

theorem counts_lift_singleton (i : Fin n) : counts_lift {i} = {i.castSucc} :=
  map_singleton _ _

theorem counts_exists_lift {C : Finset (Fin (n + 1))} (h : Fin.last n ∉ C) :
    ∃ D, counts_lift D = C := by
  refine ⟨univ.filter fun i => i.castSucc ∈ C, ?_⟩
  ext x
  induction x using Fin.lastCases with
  | last => simp [counts_last_notMem_lift, h]
  | cast i => simp [counts_castSucc_mem_lift]

theorem counts_lift_nonempty {D : Finset (Fin n)} : (counts_lift D).Nonempty ↔ D.Nonempty :=
  map_nonempty

/-- Adding the leaf `Fin.last n` as a child of the root. -/
def counts_ext (G : Finset (Finset (Fin n))) : Finset (Finset (Fin (n + 1))) :=
  insert univ (insert {Fin.last n} (G.image counts_lift))

theorem counts_mem_ext {G : Finset (Finset (Fin n))} {C : Finset (Fin (n + 1))} :
    C ∈ counts_ext G ↔ C = univ ∨ C = {Fin.last n} ∨ ∃ D ∈ G, counts_lift D = C := by
  rw [counts_ext, mem_insert, mem_insert, mem_image]

theorem counts_ext_isBinary {G : Finset (Finset (Fin n))} (hG : IsBinaryHierarchy G) :
    IsBinaryHierarchy (counts_ext G) := by
  refine ⟨⟨counts_mem_ext.2 (Or.inl rfl), fun x => ?_, fun C hC => ?_, fun C hC D hD => ?_⟩,
    fun C hC h2 => ?_⟩
  · induction x using Fin.lastCases with
    | last => exact counts_mem_ext.2 (Or.inr (Or.inl rfl))
    | cast i =>
      exact counts_mem_ext.2 (Or.inr (Or.inr ⟨{i}, hG.1.2.1 i, counts_lift_singleton i⟩))
  · rcases counts_mem_ext.1 hC with rfl | rfl | ⟨D, hD, rfl⟩
    · exact ⟨Fin.last n, mem_univ _⟩
    · exact singleton_nonempty _
    · exact counts_lift_nonempty.2 (hG.1.2.2.1 D hD)
  · rcases counts_mem_ext.1 hC with rfl | rfl | ⟨C', hC', rfl⟩
    · exact Or.inr (Or.inl (subset_univ D))
    · rcases counts_mem_ext.1 hD with rfl | rfl | ⟨D', hD', rfl⟩
      · exact Or.inl (subset_univ _)
      · exact Or.inl Subset.rfl
      · exact Or.inr (Or.inr (disjoint_singleton_left.2 (counts_last_notMem_lift D')))
    · rcases counts_mem_ext.1 hD with rfl | rfl | ⟨D', hD', rfl⟩
      · exact Or.inl (subset_univ _)
      · exact Or.inr (Or.inr (disjoint_singleton_right.2 (counts_last_notMem_lift C')))
      · rcases hG.1.2.2.2 C' hC' D' hD' with h | h | h
        · exact Or.inl (counts_lift_subset_lift.2 h)
        · exact Or.inr (Or.inl (counts_lift_subset_lift.2 h))
        · exact Or.inr (Or.inr (counts_disjoint_lift.2 h))
  · rcases counts_mem_ext.1 hC with rfl | rfl | ⟨D, hD, rfl⟩
    · refine ⟨{Fin.last n}, counts_mem_ext.2 (Or.inr (Or.inl rfl)), counts_lift univ,
        counts_mem_ext.2 (Or.inr (Or.inr ⟨univ, hG.1.1, rfl⟩)), ?_, ?_⟩
      · rw [counts_lift_univ]
        exact disjoint_compl_right
      · rw [counts_lift_univ]
        exact union_compl _
    · rw [card_singleton] at h2
      omega
    · rw [counts_card_lift] at h2
      obtain ⟨B, hB, E, hE, hBE, hBED⟩ := hG.2 D hD h2
      refine ⟨counts_lift B, counts_mem_ext.2 (Or.inr (Or.inr ⟨B, hB, rfl⟩)), counts_lift E,
        counts_mem_ext.2 (Or.inr (Or.inr ⟨E, hE, rfl⟩)), counts_disjoint_lift.2 hBE, ?_⟩
      rw [← counts_lift_union, hBED]

/-- Removing the leaf `Fin.last n`: the clusters not containing it. -/
def counts_res (G : Finset (Finset (Fin (n + 1)))) : Finset (Finset (Fin n)) :=
  univ.filter fun D => counts_lift D ∈ G

theorem counts_mem_res {G : Finset (Finset (Fin (n + 1)))} {D : Finset (Fin n)} :
    D ∈ counts_res G ↔ counts_lift D ∈ G := by
  rw [counts_res, mem_filter]
  exact and_iff_right (mem_univ D)

/-- A binary hierarchy on `Fin (n + 1)` in which `Fin.last n` is a child of the root is obtained
by adding this leaf to a binary hierarchy on `Fin n`. -/
theorem counts_res_spec {G : Finset (Finset (Fin (n + 1)))} (hG : IsBinaryHierarchy G)
    (hlast : ({Fin.last n}ᶜ : Finset (Fin (n + 1))) ∈ G) :
    IsBinaryHierarchy (counts_res G) ∧ counts_ext (counts_res G) = G := by
  refine ⟨⟨⟨?_, fun i => ?_, fun D hD => ?_, fun D hD E hE => ?_⟩, fun D hD h2 => ?_⟩, ?_⟩
  · rw [counts_mem_res, counts_lift_univ]
    exact hlast
  · rw [counts_mem_res, counts_lift_singleton]
    exact hG.1.2.1 _
  · exact counts_lift_nonempty.1 (hG.1.2.2.1 _ (counts_mem_res.1 hD))
  · rcases hG.1.2.2.2 _ (counts_mem_res.1 hD) _ (counts_mem_res.1 hE) with h | h | h
    · exact Or.inl (counts_lift_subset_lift.1 h)
    · exact Or.inr (Or.inl (counts_lift_subset_lift.1 h))
    · exact Or.inr (Or.inr (counts_disjoint_lift.1 h))
  · have hD' := counts_mem_res.1 hD
    obtain ⟨B, hB, C, hC, hBC, hBCD⟩ := hG.2 _ hD' (by rwa [counts_card_lift])
    obtain ⟨B', rfl⟩ := counts_exists_lift
      (fun h => counts_last_notMem_lift D (hBCD ▸ mem_union_left _ h))
    obtain ⟨C', rfl⟩ := counts_exists_lift
      (fun h => counts_last_notMem_lift D (hBCD ▸ mem_union_right _ h))
    refine ⟨B', counts_mem_res.2 hB, C', counts_mem_res.2 hC, counts_disjoint_lift.1 hBC, ?_⟩
    apply counts_lift_injective
    rw [counts_lift_union, hBCD]
  · ext C
    rw [counts_mem_ext]
    constructor
    · rintro (rfl | rfl | ⟨D, hD, rfl⟩)
      · exact hG.1.1
      · exact hG.1.2.1 _
      · exact counts_mem_res.1 hD
    · intro hC
      by_cases hl : Fin.last n ∈ C
      · rcases hG.1.2.2.2 C hC _ hlast with h | h | h
        · exact absurd (h hl) (by simp)
        · left
          refine eq_univ_iff_forall.2 fun x => ?_
          by_cases hx : x = Fin.last n
          · exact hx ▸ hl
          · exact h (by simpa using hx)
        · right
          left
          have hsub : C ⊆ {Fin.last n} := disjoint_compl_right_iff.1 h
          exact (subset_singleton_iff.1 hsub).resolve_left (ne_empty_of_mem hl)
      · obtain ⟨D, rfl⟩ := counts_exists_lift hl
        exact Or.inr (Or.inr ⟨D, counts_mem_res.2 hC, rfl⟩)

/-- The clusters of a hierarchy `G` are recovered from the unrooted tree of `counts_ext G`. -/
theorem counts_lift_mem_unroot_ext {G : Finset (Finset (Fin n))} (hG : IsHierarchy G)
    {D : Finset (Fin n)} : counts_lift D ∈ unroot (counts_ext G) ↔ D ∈ G := by
  rw [mem_unroot, counts_mem_ext, counts_mem_ext]
  constructor
  · rintro (⟨h | h | ⟨E, hE, h⟩, -⟩ | ⟨h | h | ⟨E, hE, h⟩, hu⟩)
    · exact absurd (h ▸ mem_univ (Fin.last n)) (counts_last_notMem_lift D)
    · exact absurd (h ▸ mem_singleton_self (Fin.last n)) (counts_last_notMem_lift D)
    · exact counts_lift_injective h ▸ hE
    · exact absurd h hu
    · have : counts_lift D = counts_lift univ := by
        rw [counts_lift_univ, ← h, compl_compl]
      rw [counts_lift_injective this]
      exact hG.1
    · exfalso
      have : Fin.last n ∈ (counts_lift D)ᶜ := mem_compl.2 (counts_last_notMem_lift D)
      rw [← h] at this
      exact counts_last_notMem_lift E this
  · intro hD
    exact Or.inl ⟨Or.inr (Or.inr ⟨D, hD, rfl⟩),
      fun h => counts_last_notMem_lift D (h ▸ mem_univ _)⟩

end Fin

/-! ### Counting -/

open scoped Classical in
/-- Each unrooted binary tree has `2n - 3` rooted versions, so the number of rooted binary trees
is `2n - 3` times the number of unrooted binary trees. -/
theorem counts_card_rooted_eq_mul (n : ℕ) (hn : 2 ≤ n) :
    #{G : Finset (Finset (Fin n)) | IsBinaryHierarchy G} =
      #(({G : Finset (Finset (Fin n)) | IsBinaryHierarchy G} : Finset _).image unroot) *
        (2 * n - 3) := by
  rw [card_eq_sum_card_image unroot ({G : Finset (Finset (Fin n)) | IsBinaryHierarchy G} :
    Finset _)]
  refine sum_const_nat fun T hT => ?_
  obtain ⟨G₀, hG₀, rfl⟩ := mem_image.1 hT
  rw [filter_filter]
  have := counts_card_rootings (L := Fin n) (mem_filter.1 hG₀).2 (by rwa [Fintype.card_fin])
  rwa [Fintype.card_fin] at this

open scoped Classical in
/-- The unrooted binary trees on `n + 1` leaves correspond to the rooted binary trees on `n`
leaves (root on the pendant edge of the leaf `n + 1`, and remove this leaf). -/
theorem counts_card_unrooted_succ (n : ℕ) (hn : 1 ≤ n) :
    #(({G : Finset (Finset (Fin (n + 1))) | IsBinaryHierarchy G} : Finset _).image unroot) =
      #{G : Finset (Finset (Fin n)) | IsBinaryHierarchy G} := by
  have himg : (({G : Finset (Finset (Fin (n + 1))) | IsBinaryHierarchy G} : Finset _).image
      unroot) = ({G : Finset (Finset (Fin n)) | IsBinaryHierarchy G} : Finset _).image
        (fun G => unroot (counts_ext G)) := by
    ext T
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨H, hH, rfl⟩
      have h2 : 2 ≤ Fintype.card (Fin (n + 1)) := by
        rw [Fintype.card_fin]
        omega
      have hl : ({Fin.last n} : Finset (Fin (n + 1))) ∈ unroot H := by
        refine mem_unroot.2 (Or.inl ⟨hH.1.2.1 _, fun h => ?_⟩)
        have := congrArg card h
        rw [card_singleton, card_univ, Fintype.card_fin] at this
        omega
      obtain ⟨hR, hRT⟩ := counts_reroot_spec hH h2 hl
      have hlc : ({Fin.last n}ᶜ : Finset (Fin (n + 1))) ∈ counts_reroot (unroot H) {Fin.last n} :=
        counts_mem_reroot.2 (Or.inr ⟨compl_mem_unroot.2 hl, Or.inr Subset.rfl⟩)
      obtain ⟨hres, hext⟩ := counts_res_spec hR hlc
      exact ⟨counts_res _, hres, by rw [hext, hRT]⟩
    · rintro ⟨G, hG, rfl⟩
      exact ⟨counts_ext G, counts_ext_isBinary hG, rfl⟩
  rw [himg, card_image_of_injOn]
  intro G hG G' hG' h
  have hG1 := (mem_filter.1 (mem_coe.1 hG)).2
  have hG1' := (mem_filter.1 (mem_coe.1 hG')).2
  ext D
  rw [← counts_lift_mem_unroot_ext hG1.1, ← counts_lift_mem_unroot_ext hG1'.1]
  simp only at h
  rw [h]

open scoped Classical in
theorem counts_card_rooted_one :
    #{G : Finset (Finset (Fin 1)) | IsBinaryHierarchy G} = 1 := by
  rw [card_eq_one]
  refine ⟨{univ}, ?_⟩
  ext G
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  have hsub : ∀ C : Finset (Fin 1), C.Nonempty → C = univ := fun C hC => by
    obtain ⟨x, hx⟩ := hC
    exact eq_univ_iff_forall.2 fun y => Subsingleton.elim x y ▸ hx
  constructor
  · intro hG
    ext C
    rw [mem_singleton]
    constructor
    · intro hC
      exact hsub C (hG.1.2.2.1 C hC)
    · rintro rfl
      exact hG.1.1
  · rintro rfl
    refine ⟨⟨mem_singleton_self _, fun x => ?_, fun C hC => ?_, fun C hC D hD => ?_⟩,
      fun C hC h2 => ?_⟩
    · rw [mem_singleton]
      exact hsub _ (singleton_nonempty x)
    · rw [mem_singleton.1 hC]
      exact univ_nonempty
    · rw [mem_singleton.1 hC, mem_singleton.1 hD]
      exact Or.inl Subset.rfl
    · rw [mem_singleton.1 hC, card_univ, Fintype.card_fin] at h2
      omega

open scoped Classical in
/-- Section 1 [Felsenstein 2004]: there are `(2n-3)!!` rooted binary trees on `n` labelled
leaves. -/
theorem section1_card_rooted (n : ℕ) (hn : 1 ≤ n) :
    #{G : Finset (Finset (Fin n)) | IsBinaryHierarchy G} = (2 * n - 3).doubleFactorial := by
  induction n, hn using Nat.le_induction with
  | base => rw [counts_card_rooted_one]; rfl
  | succ n hn ih =>
    rw [counts_card_rooted_eq_mul (n + 1) (by omega), counts_card_unrooted_succ n hn, ih]
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      rfl
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      rw [show 2 * (k + 2 + 1) - 3 = (2 * (k + 2) - 3) + 2 by omega, Nat.doubleFactorial_add_two,
        mul_comm]

open scoped Classical in
/-- Section 1: each unrooted binary tree on `n ≥ 2` leaves is the unrooted version of exactly
`2n-3` rooted binary trees. -/
theorem section1_card_rootings (n : ℕ) (hn : 2 ≤ n) (G₀ : Finset (Finset (Fin n)))
    (hG₀ : IsBinaryHierarchy G₀) :
    #{G : Finset (Finset (Fin n)) | IsBinaryHierarchy G ∧ unroot G = unroot G₀} = 2 * n - 3 := by
  have h := counts_card_rootings (L := Fin n) hG₀ (by rwa [Fintype.card_fin])
  rwa [Fintype.card_fin] at h

open scoped Classical in
/-- Section 1: there are `(2n-5)!!` unrooted binary trees on `n ≥ 3` labelled leaves. -/
theorem section1_card_unrooted (n : ℕ) (hn : 3 ≤ n) :
    #(({G : Finset (Finset (Fin n)) | IsBinaryHierarchy G} : Finset _).image unroot) =
      (2 * n - 5).doubleFactorial := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (m + 1) - 5 = 2 * m - 3 by omega, counts_card_unrooted_succ m (by omega)]
  exact section1_card_rooted m (by omega)

end ADR11
