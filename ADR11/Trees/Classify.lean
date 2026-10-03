module

public import ADR11.MSC.Relabel
public import ADR11.SmallTrees

/-!
# Unrooted trees on four and five taxa, and their rootings

Every species tree on four or five taxa is, after relabelling, a rooting of one of a few standard
unrooted trees, and the rootings of each standard unrooted tree are listed explicitly.

* Four taxa: `U4 1 = AB|CD` and the star `U4 0`; `rootings4 k` lists the hierarchies on `Fin 4`
  with unrooted tree `U4 k` (7 for `AB|CD`: four caterpillars, the balanced tree, and the two
  trees with one cherry and a trifurcating root; 5 for the star).
* Five taxa: `U5 2 = {AB|CDE, ABC|DE}`, `U5 1 = AB|CDE`, the star `U5 0`; `rootings5 k` lists the
  hierarchies on `Fin 5` with unrooted tree `U5 k` (10, 8 and 6 of them), and
  `binaryRootings5` the 7 binary ones with unrooted tree `U5 2`.

## Main results

* `exists_equiv_unroot_eq_U4`, `exists_equiv_unroot_eq_U5`: normal forms up to relabelling.
* `exists_equiv_unroot_eq_U5_two_of_isBinary`: a binary 5-taxon tree has unrooted shape `U5 2`.
* `mem_rootings4`, `mem_rootings5`, `mem_binaryRootings5`: the lists are complete.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The unrooted trees on `Fin 4`: `U4 1` has the split `AB|CD`, `U4 0` is the star. -/
def U4 : ℕ → Finset (Finset (Fin 4))
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

/-- The unrooted trees on `Fin 5`: `U5 2` has the splits `AB|CDE` and `ABC|DE`, `U5 1` the split
`AB|CDE`, and `U5 0` is the star. -/
def U5 : ℕ → Finset (Finset (Fin 5))
  | 2 => treeOfClusters {{0, 1}, {3, 4}}
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

/-- The hierarchies on `Fin 4` with unrooted tree `U4 k`. -/
def rootings4 : ℕ → Finset (Finset (Finset (Fin 4)))
  | 1 => {hierarchyOf {{0, 1}, {0, 1, 2}}, hierarchyOf {{0, 1}, {0, 1, 3}},
          hierarchyOf {{2, 3}, {0, 2, 3}}, hierarchyOf {{2, 3}, {1, 2, 3}},
          hierarchyOf {{0, 1}, {2, 3}}, hierarchyOf {{0, 1}}, hierarchyOf {{2, 3}}}
  | _ => {hierarchyOf ∅, hierarchyOf {{0, 1, 2}}, hierarchyOf {{0, 1, 3}},
          hierarchyOf {{0, 2, 3}}, hierarchyOf {{1, 2, 3}}}

/-- The hierarchies on `Fin 5` with unrooted tree `U5 k`. -/
def rootings5 : ℕ → Finset (Finset (Finset (Fin 5)))
  | 2 => {hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}, hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}},
          hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}, hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}},
          hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}},
          hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}},
          hierarchyOf {{0, 1}, {3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2}},
          hierarchyOf {{3, 4}, {2, 3, 4}}}
  | 1 => {hierarchyOf {{0, 1}}, hierarchyOf {{2, 3, 4}}, hierarchyOf {{0, 1}, {2, 3, 4}},
          hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}, hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}},
          hierarchyOf {{0, 1}, {0, 1, 3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2, 4}},
          hierarchyOf {{0, 1}, {0, 1, 2, 3}}}
  | _ => {hierarchyOf ∅, hierarchyOf {{1, 2, 3, 4}}, hierarchyOf {{0, 2, 3, 4}},
          hierarchyOf {{0, 1, 3, 4}}, hierarchyOf {{0, 1, 2, 4}}, hierarchyOf {{0, 1, 2, 3}}}

/-- The seven binary rootings of `U5 2` (roots on the pendant edges of `e`, `d`, `a`, `b`, `c`,
and on the internal edges `ABC|DE` and `AB|CDE`). -/
def binaryRootings5 : Finset (Finset (Finset (Fin 5))) :=
  {hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}, hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}},
   hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}, hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}},
   hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}},
   hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}}}

/-! ### Unrooting and relabelling -/

theorem classify_mem_unroot {G : Finset (Finset X)} {A : Finset X} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := by
  unfold unroot
  simp only [mem_union, mem_erase, mem_image]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨B, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨by simpa using h2, by simpa using h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨Aᶜ, ⟨h2, h1⟩, compl_compl A⟩

theorem classify_compl_mem_unroot {G : Finset (Finset X)} {A : Finset X} :
    Aᶜ ∈ unroot G ↔ A ∈ unroot G := by
  rw [classify_mem_unroot, classify_mem_unroot, compl_compl, or_comm]

omit [Fintype X] [DecidableEq X] in
theorem classify_mem_relabelFamily {Y : Type*} [DecidableEq Y] {e : X ≃ Y}
    {F : Finset (Finset X)} {B : Finset Y} :
    B ∈ relabelFamily e F ↔ B.map e.symm.toEmbedding ∈ F := by
  unfold relabelFamily
  rw [mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    convert hA using 1
    ext x
    simp [mem_map_equiv]
  · intro h
    refine ⟨_, h, ?_⟩
    ext y
    simp [mem_map_equiv]

omit [Fintype X] [DecidableEq X] in
theorem classify_relabelFamily_trans {Y Z : Type*} [DecidableEq Y] [DecidableEq Z] (e : X ≃ Y)
    (f : Y ≃ Z) (F : Finset (Finset X)) :
    relabelFamily f (relabelFamily e F) = relabelFamily (e.trans f) F := by
  unfold relabelFamily
  rw [image_image]
  congr 1
  funext A
  rw [Function.comp_apply, map_map, Equiv.trans_toEmbedding]

/-! ### The splits of a species tree on four or five taxa -/

theorem classify_card_of_mem_unroot (σ : SpeciesTree X) {A : Finset X}
    (h : A ∈ unroot σ.clusters) : 1 ≤ #A ∧ #A < Fintype.card X := by
  rcases classify_mem_unroot.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(σ.nonempty_of_mem A h1).card_pos, (card_lt_iff_ne_univ A).2 h2⟩
  · have h3 := (σ.nonempty_of_mem _ h1).card_pos
    have h4 := (card_lt_iff_ne_univ _).2 h2
    rw [card_compl] at h3 h4
    have := card_le_univ A
    omega

theorem classify_singleton_mem_unroot (hX : 2 ≤ Fintype.card X) (σ : SpeciesTree X) (x : X) :
    {x} ∈ unroot σ.clusters := by
  refine classify_mem_unroot.2 (Or.inl ⟨σ.singleton_mem x, ?_⟩)
  intro h
  have := congrArg card h
  rw [card_singleton, card_univ] at this
  omega

/-- On four or five taxa, the splits of a species tree are the trivial ones and those with a side
of two taxa. -/
theorem classify_mem_unroot_iff (hX : Fintype.card X = 4 ∨ Fintype.card X = 5)
    (σ : SpeciesTree X) (A : Finset X) :
    A ∈ unroot σ.clusters ↔ #A = 1 ∨ #A = Fintype.card X - 1 ∨
      A ∈ (unroot σ.clusters).filter (fun B => #B = 2) ∨
      Aᶜ ∈ (unroot σ.clusters).filter (fun B => #B = 2) := by
  have h2 : 2 ≤ Fintype.card X := by omega
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := classify_card_of_mem_unroot σ h
    have hc := card_compl A
    rcases (by omega : #A = 1 ∨ #A = Fintype.card X - 1 ∨ #A = 2 ∨ #Aᶜ = 2) with
      h3 | h3 | h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl (mem_filter.2 ⟨h, h3⟩)))
    · exact Or.inr (Or.inr (Or.inr (mem_filter.2 ⟨classify_compl_mem_unroot.2 h, h3⟩)))
  · rintro (h | h | h | h)
    · obtain ⟨x, rfl⟩ := card_eq_one.1 h
      exact classify_singleton_mem_unroot h2 σ x
    · have : #Aᶜ = 1 := by rw [card_compl]; omega
      obtain ⟨x, hx⟩ := card_eq_one.1 this
      rw [← classify_compl_mem_unroot, hx]
      exact classify_singleton_mem_unroot h2 σ x
    · exact (mem_filter.1 h).1
    · exact classify_compl_mem_unroot.1 (mem_filter.1 h).1

/-- Transport of the unrooted tree along a relabelling, given the sides with two taxa. -/
theorem classify_unroot_relabel_eq {Y : Type*} [Fintype Y] [DecidableEq Y] {n : ℕ}
    (hX : Fintype.card X = n) (hn : n = 4 ∨ n = 5) (σ : SpeciesTree X) (e : Y ≃ X)
    (U T : Finset (Finset Y))
    (hU : ∀ A ∈ (univ : Finset (Finset Y)), A ∈ U ↔ #A = 1 ∨ #A = n - 1 ∨ A ∈ T ∨ Aᶜ ∈ T)
    (hP : (unroot σ.clusters).filter (fun B => #B = 2) = relabelFamily e T) :
    unroot (σ.relabel e.symm).clusters = U := by
  show unroot (relabelFamily e.symm σ.clusters) = U
  rw [unroot_relabelFamily]
  ext A
  rw [classify_mem_relabelFamily, Equiv.symm_symm, classify_mem_unroot_iff (by omega) σ,
    hU A (mem_univ A), hP, card_map, hX, classify_mem_relabelFamily, classify_mem_relabelFamily]
  have h1 : (A.map e.toEmbedding).map e.symm.toEmbedding = A := by
    ext; simp [mem_map_equiv]
  have h2 : (A.map e.toEmbedding)ᶜ.map e.symm.toEmbedding = Aᶜ := by
    ext; simp [mem_map_equiv]
  rw [h1, h2]

/-- On five taxa, two distinct sides with two taxa of splits of a species tree are disjoint. -/
theorem classify_disjoint_of_card_two (hX : Fintype.card X = 5) (σ : SpeciesTree X)
    {A B : Finset X} (hA : A ∈ unroot σ.clusters) (hB : B ∈ unroot σ.clusters) (hA2 : #A = 2)
    (hB2 : #B = 2) (hAB : A ≠ B) : Disjoint A B := by
  by_contra hd
  have hAc : #Aᶜ = 3 := by rw [card_compl, hX, hA2]
  have hBc : #Bᶜ = 3 := by rw [card_compl, hX, hB2]
  have key : ∀ C D : Finset X, C ⊆ D → #D ≤ #C → C = D := fun C D h1 h2 =>
    eq_of_subset_of_card_le h1 h2
  rcases classify_mem_unroot.1 hA with ⟨hA', -⟩ | ⟨hA', -⟩ <;>
    rcases classify_mem_unroot.1 hB with ⟨hB', -⟩ | ⟨hB', -⟩
  · rcases σ.laminar _ hA' _ hB' with h | h | h
    · exact hAB (key _ _ h (by omega))
    · exact hAB (key _ _ h (by omega)).symm
    · exact hd h
  · rcases σ.laminar _ hA' _ hB' with h | h | h
    · exact hd (subset_compl_iff_disjoint_right.1 h)
    · have := card_le_card h; omega
    · exact hAB (key _ _ (disjoint_compl_right_iff.1 h) (by omega))
  · rcases σ.laminar _ hA' _ hB' with h | h | h
    · have := card_le_card h; omega
    · exact hd (subset_compl_iff_disjoint_left.1 h)
    · exact hAB (key _ _ (disjoint_compl_left_iff.1 h) (by omega)).symm
  · rcases σ.laminar _ hA' _ hB' with h | h | h
    · exact hAB (key _ _ (compl_subset_compl.1 h) (by omega)).symm
    · exact hAB (key _ _ (compl_subset_compl.1 h) (by omega))
    · have := card_le_card (disjoint_compl_left_iff.1 h)
      omega

/-- On five taxa, a species tree has at most two splits with a side of two taxa. -/
theorem classify_card_pairs_le (hX : Fintype.card X = 5) (σ : SpeciesTree X) :
    #((unroot σ.clusters).filter (fun A => #A = 2)) ≤ 2 := by
  by_contra h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.1 (not_le.1 h)
  rw [mem_filter] at ha hb hc
  have dab := classify_disjoint_of_card_two hX σ ha.1 hb.1 ha.2 hb.2 hab
  have dac := classify_disjoint_of_card_two hX σ ha.1 hc.1 ha.2 hc.2 hac
  have dbc := classify_disjoint_of_card_two hX σ hb.1 hc.1 hb.2 hc.2 hbc
  have h6 : #(a ∪ b ∪ c) = 6 := by
    rw [card_union_of_disjoint (disjoint_union_left.2 ⟨dac, dbc⟩), card_union_of_disjoint dab,
      ha.2, hb.2, hc.2]
  have := card_le_univ (a ∪ b ∪ c)
  omega

/-- On four taxa, two sides with two taxa of splits of a species tree are equal or
complementary. -/
theorem classify_eq_or_eq_compl_of_card_two (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    {A B : Finset X} (hA : A ∈ unroot σ.clusters) (hB : B ∈ unroot σ.clusters) (hA2 : #A = 2)
    (hB2 : #B = 2) : B = A ∨ B = Aᶜ := by
  by_contra hne
  obtain ⟨h1, h2⟩ := not_or.1 hne
  have hAc : #Aᶜ = 2 := by rw [card_compl, hX, hA2]
  have hBc : #Bᶜ = 2 := by rw [card_compl, hX, hB2]
  have key : ∀ C D : Finset X, C ⊆ D → #D ≤ #C → C = D := fun C D h1 h2 =>
    eq_of_subset_of_card_le h1 h2
  rcases classify_mem_unroot.1 hA with ⟨hA', -⟩ | ⟨hA', -⟩ <;>
    rcases classify_mem_unroot.1 hB with ⟨hB', -⟩ | ⟨hB', -⟩
  · rcases σ.laminar _ hA' _ hB' with h | h | h
    · exact h1 (key _ _ h (by omega)).symm
    · exact h1 (key _ _ h (by omega))
    · exact h2 (key _ _ (subset_compl_iff_disjoint_left.2 h) (by omega))
  · rcases σ.laminar _ hA' _ hB' with h | h | h
    · exact h2 (key _ _ (subset_compl_iff_disjoint_left.2
        (subset_compl_iff_disjoint_right.1 h)) (by omega))
    · have := key _ _ h (by omega)
      exact h2 (by rw [← this, compl_compl])
    · exact h1 (key _ _ (disjoint_compl_right_iff.1 h) (by omega)).symm
  · rcases σ.laminar _ hA' _ hB' with h | h | h
    · exact h2 (key _ _ h (by omega)).symm
    · exact h2 (key _ _ h (by omega))
    · exact h1 (key _ _ (disjoint_compl_left_iff.1 h) (by omega))
  · rcases σ.laminar _ hA' _ hB' with h | h | h
    · exact h1 (key _ _ (compl_subset_compl.1 h) (by omega))
    · exact h1 (key _ _ (compl_subset_compl.1 h) (by omega)).symm
    · have := key _ _ (disjoint_compl_left_iff.1 h) (by omega)
      exact h2 (by rw [← this, compl_compl])

omit [DecidableEq X] in
theorem classify_exists_equiv {n : ℕ} (hX : Fintype.card X = n) (f : Fin n → X)
    (hf : Function.Injective f) : ∃ e : Fin n ≃ X, ∀ i, e i = f i :=
  ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp [hX]⟩),
    fun _ => rfl⟩

/-! ### Hierarchies with prescribed splits -/

/-- A hierarchy consists of the root, the singletons and its other clusters. -/
theorem classify_eq_hierarchyOf {H : Finset (Finset X)} (hH : IsHierarchy H) :
    H = hierarchyOf (H.filter fun A => 2 ≤ #A ∧ A ≠ univ) := by
  ext A
  simp only [hierarchyOf, mem_insert, mem_union, mem_image, mem_univ, true_and, mem_filter]
  constructor
  · intro hA
    by_cases hu : A = univ
    · exact Or.inl hu
    · by_cases h2 : 2 ≤ #A
      · exact Or.inr (Or.inl ⟨hA, h2, hu⟩)
      · have : #A = 1 := by have := (hH.2.2.1 A hA).card_pos; omega
        obtain ⟨x, rfl⟩ := card_eq_one.1 this
        exact Or.inr (Or.inr ⟨x, rfl⟩)
  · rintro (rfl | ⟨hA, -⟩ | ⟨x, rfl⟩)
    · exact hH.1
    · exact hA
    · exact hH.2.1 x

/-- Reduction of the classification of the rootings of an unrooted tree `U` to a finite check:
the clusters of a rooting other than the root and the singletons are among the candidates `C`,
and they contain a side of each split listed in `S`. -/
theorem classify_mem_of_forall {τ : SpeciesTree X} {U C S : Finset (Finset X)}
    {R : Finset (Finset (Finset X))}
    (hdec : ∀ N ∈ C.powerset, (∀ A ∈ N, ∀ B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
      (∀ A ∈ S, A ∈ N ∨ Aᶜ ∈ N) → hierarchyOf N ∈ R)
    (hC : ∀ A ∈ U, 2 ≤ #A → A ∈ C) (hS : ∀ A ∈ S, A ∈ U ∧ 2 ≤ #A ∧ 2 ≤ #Aᶜ)
    (h : unroot τ.clusters = U) : τ.clusters ∈ R := by
  rw [classify_eq_hierarchyOf τ.isHierarchy]
  apply hdec
  · rw [mem_powerset]
    intro A hA
    rw [mem_filter] at hA
    exact hC A (h ▸ classify_mem_unroot.2 (Or.inl ⟨hA.1, hA.2.2⟩)) hA.2.1
  · intro A hA B hB
    exact τ.laminar A (mem_filter.1 hA).1 B (mem_filter.1 hB).1
  · intro A hA
    obtain ⟨hAU, h2, h2c⟩ := hS A hA
    rw [← h] at hAU
    rcases classify_mem_unroot.1 hAU with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
    · exact Or.inl (mem_filter.2 ⟨h1, h2, h1'⟩)
    · exact Or.inr (mem_filter.2 ⟨h1, h2c, h1'⟩)

/-! ### Finite checks on the standard trees

The `Fintype` instances deciding unbounded quantifiers are switched off, so that the bounded
quantifiers below are decided by running through the given finsets (otherwise instance search
may decide `∀ N ∈ s, p N` by enumerating all of `Finset (Finset (Fin 5))`, which happens
silently when the instance through `Finset.decidableDforallFinset` exceeds
`synthInstance.maxSize`; this size limit is raised locally for the larger checks). -/

section Decide

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

theorem classify_U5_two : ∀ A ∈ (univ : Finset (Finset (Fin 5))), A ∈ U5 2 ↔
    #A = 1 ∨ #A = 5 - 1 ∨ A ∈ ({{0, 1}, {3, 4}} : Finset (Finset (Fin 5))) ∨
      Aᶜ ∈ ({{0, 1}, {3, 4}} : Finset (Finset (Fin 5))) := by
  decide +kernel

theorem classify_U5_one : ∀ A ∈ (univ : Finset (Finset (Fin 5))), A ∈ U5 1 ↔
    #A = 1 ∨ #A = 5 - 1 ∨ A ∈ ({{0, 1}} : Finset (Finset (Fin 5))) ∨
      Aᶜ ∈ ({{0, 1}} : Finset (Finset (Fin 5))) := by
  decide +kernel

theorem classify_U5_zero : ∀ A ∈ (univ : Finset (Finset (Fin 5))), A ∈ U5 0 ↔
    #A = 1 ∨ #A = 5 - 1 ∨ A ∈ (∅ : Finset (Finset (Fin 5))) ∨
      Aᶜ ∈ (∅ : Finset (Finset (Fin 5))) := by
  decide +kernel

theorem classify_U4_one : ∀ A ∈ (univ : Finset (Finset (Fin 4))), A ∈ U4 1 ↔
    #A = 1 ∨ #A = 4 - 1 ∨ A ∈ ({{0, 1}, {2, 3}} : Finset (Finset (Fin 4))) ∨
      Aᶜ ∈ ({{0, 1}, {2, 3}} : Finset (Finset (Fin 4))) := by
  decide +kernel

theorem classify_U4_zero : ∀ A ∈ (univ : Finset (Finset (Fin 4))), A ∈ U4 0 ↔
    #A = 1 ∨ #A = 4 - 1 ∨ A ∈ (∅ : Finset (Finset (Fin 4))) ∨
      Aᶜ ∈ (∅ : Finset (Finset (Fin 4))) := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem classify_rootings5_two :
    ∀ N ∈ ({{0, 1}, {3, 4}, {2, 3, 4}, {0, 1, 2}, {1, 2, 3, 4}, {0, 2, 3, 4}, {0, 1, 3, 4},
      {0, 1, 2, 4}, {0, 1, 2, 3}} : Finset (Finset (Fin 5))).powerset,
    (∀ A ∈ N, ∀ B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
    (∀ A ∈ ({{0, 1}, {3, 4}} : Finset (Finset (Fin 5))), A ∈ N ∨ Aᶜ ∈ N) →
      hierarchyOf N ∈ rootings5 2 := by
  decide +kernel

theorem classify_cands5_two : ∀ A ∈ U5 2, 2 ≤ #A → A ∈ ({{0, 1}, {3, 4}, {2, 3, 4}, {0, 1, 2},
    {1, 2, 3, 4}, {0, 2, 3, 4}, {0, 1, 3, 4}, {0, 1, 2, 4}, {0, 1, 2, 3}} :
      Finset (Finset (Fin 5))) := by
  decide +kernel

theorem classify_splits5_two : ∀ A ∈ ({{0, 1}, {3, 4}} : Finset (Finset (Fin 5))),
    A ∈ U5 2 ∧ 2 ≤ #A ∧ 2 ≤ #Aᶜ := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem classify_rootings5_one :
    ∀ N ∈ ({{0, 1}, {2, 3, 4}, {1, 2, 3, 4}, {0, 2, 3, 4}, {0, 1, 3, 4}, {0, 1, 2, 4},
      {0, 1, 2, 3}} : Finset (Finset (Fin 5))).powerset,
    (∀ A ∈ N, ∀ B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
    (∀ A ∈ ({{0, 1}} : Finset (Finset (Fin 5))), A ∈ N ∨ Aᶜ ∈ N) →
      hierarchyOf N ∈ rootings5 1 := by
  decide +kernel

theorem classify_cands5_one : ∀ A ∈ U5 1, 2 ≤ #A → A ∈ ({{0, 1}, {2, 3, 4}, {1, 2, 3, 4},
    {0, 2, 3, 4}, {0, 1, 3, 4}, {0, 1, 2, 4}, {0, 1, 2, 3}} : Finset (Finset (Fin 5))) := by
  decide +kernel

theorem classify_splits5_one : ∀ A ∈ ({{0, 1}} : Finset (Finset (Fin 5))),
    A ∈ U5 1 ∧ 2 ≤ #A ∧ 2 ≤ #Aᶜ := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem classify_rootings5_zero :
    ∀ N ∈ ({{1, 2, 3, 4}, {0, 2, 3, 4}, {0, 1, 3, 4}, {0, 1, 2, 4}, {0, 1, 2, 3}} :
      Finset (Finset (Fin 5))).powerset,
    (∀ A ∈ N, ∀ B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
    (∀ A ∈ (∅ : Finset (Finset (Fin 5))), A ∈ N ∨ Aᶜ ∈ N) →
      hierarchyOf N ∈ rootings5 0 := by
  decide +kernel

theorem classify_cands5_zero : ∀ A ∈ U5 0, 2 ≤ #A → A ∈ ({{1, 2, 3, 4}, {0, 2, 3, 4},
    {0, 1, 3, 4}, {0, 1, 2, 4}, {0, 1, 2, 3}} : Finset (Finset (Fin 5))) := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem classify_rootings4_one :
    ∀ N ∈ ({{0, 1}, {2, 3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} :
      Finset (Finset (Fin 4))).powerset,
    (∀ A ∈ N, ∀ B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
    (∀ A ∈ ({{0, 1}} : Finset (Finset (Fin 4))), A ∈ N ∨ Aᶜ ∈ N) →
      hierarchyOf N ∈ rootings4 1 := by
  decide +kernel

theorem classify_cands4_one : ∀ A ∈ U4 1, 2 ≤ #A → A ∈ ({{0, 1}, {2, 3}, {1, 2, 3}, {0, 2, 3},
    {0, 1, 3}, {0, 1, 2}} : Finset (Finset (Fin 4))) := by
  decide +kernel

theorem classify_splits4_one : ∀ A ∈ ({{0, 1}} : Finset (Finset (Fin 4))),
    A ∈ U4 1 ∧ 2 ≤ #A ∧ 2 ≤ #Aᶜ := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem classify_rootings4_zero :
    ∀ N ∈ ({{1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} : Finset (Finset (Fin 4))).powerset,
    (∀ A ∈ N, ∀ B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
    (∀ A ∈ (∅ : Finset (Finset (Fin 4))), A ∈ N ∨ Aᶜ ∈ N) →
      hierarchyOf N ∈ rootings4 0 := by
  decide +kernel

theorem classify_cands4_zero : ∀ A ∈ U4 0, 2 ≤ #A → A ∈ ({{1, 2, 3}, {0, 2, 3}, {0, 1, 3},
    {0, 1, 2}} : Finset (Finset (Fin 4))) := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem classify_binary_of_mem_rootings5_two : ∀ H ∈ rootings5 2,
    (∀ A ∈ H, 2 ≤ #A → ∃ B ∈ H, ∃ C ∈ H, Disjoint B C ∧ B ∪ C = A) → H ∈ binaryRootings5 := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem classify_not_binary_of_mem_rootings5_one : ∀ H ∈ rootings5 1,
    ¬ ∀ A ∈ H, 2 ≤ #A → ∃ B ∈ H, ∃ C ∈ H, Disjoint B C ∧ B ∪ C = A := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem classify_not_binary_of_mem_rootings5_zero : ∀ H ∈ rootings5 0,
    ¬ ∀ A ∈ H, 2 ≤ #A → ∃ B ∈ H, ∃ C ∈ H, Disjoint B C ∧ B ∪ C = A := by
  decide +kernel

end Decide

/-! ### Main results -/

/-- Normal form on four taxa. -/
theorem exists_equiv_unroot_eq_U4 (hX : Fintype.card X = 4) (σ : SpeciesTree X) :
    ∃ e : Fin 4 ≃ X, ∃ k ∈ ({0, 1} : Finset ℕ), unroot (σ.relabel e.symm).clusters = U4 k := by
  obtain ⟨P, hPdef⟩ : ∃ P, P = (unroot σ.clusters).filter (fun A => #A = 2) := ⟨_, rfl⟩
  rcases P.eq_empty_or_nonempty with hP | ⟨A, hA⟩
  · refine ⟨(Fintype.equivFinOfCardEq hX).symm, 0, by simp, ?_⟩
    refine classify_unroot_relabel_eq hX (Or.inl rfl) σ _ _ ∅ classify_U4_zero ?_
    rw [← hPdef, hP]
    simp [relabelFamily]
  · rw [hPdef, mem_filter] at hA
    have hAc2 : #Aᶜ = 2 := by rw [card_compl, hX, hA.2]
    have hP : P = {A, Aᶜ} := by
      ext B
      rw [hPdef, mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hB, hB2⟩
        exact classify_eq_or_eq_compl_of_card_two hX σ hA.1 hB hA.2 hB2
      · rintro (rfl | rfl)
        · exact hA
        · exact ⟨classify_compl_mem_unroot.2 hA.1, hAc2⟩
    obtain ⟨p, q, hpq, hpqA⟩ := card_eq_two.1 hA.2
    obtain ⟨r, s, hrs, hrsA⟩ := card_eq_two.1 hAc2
    have hp : p ∈ A := by rw [hpqA]; simp
    have hq : q ∈ A := by rw [hpqA]; simp
    have hr : r ∉ A := by rw [← mem_compl, hrsA]; simp
    have hs : s ∉ A := by rw [← mem_compl, hrsA]; simp
    obtain ⟨e, he⟩ := classify_exists_equiv hX ![p, q, r, s] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    refine ⟨e, 1, by simp, ?_⟩
    refine classify_unroot_relabel_eq hX (Or.inl rfl) σ e _ {{0, 1}, {2, 3}} classify_U4_one ?_
    rw [← hPdef, hP, hrsA, hpqA]
    simp [relabelFamily, he]

/-- Normal form on five taxa. -/
theorem exists_equiv_unroot_eq_U5 (hX : Fintype.card X = 5) (σ : SpeciesTree X) :
    ∃ e : Fin 5 ≃ X, ∃ k ∈ ({0, 1, 2} : Finset ℕ),
      unroot (σ.relabel e.symm).clusters = U5 k := by
  have hle := classify_card_pairs_le hX σ
  obtain ⟨P, hPdef⟩ : ∃ P, P = (unroot σ.clusters).filter (fun A => #A = 2) := ⟨_, rfl⟩
  rw [← hPdef] at hle
  have hPmem : ∀ A ∈ P, A ∈ unroot σ.clusters ∧ #A = 2 := fun A hA => by
    rw [hPdef] at hA; exact mem_filter.1 hA
  rcases (by omega : #P = 0 ∨ #P = 1 ∨ #P = 2) with hc | hc | hc
  · refine ⟨(Fintype.equivFinOfCardEq hX).symm, 0, by simp, ?_⟩
    refine classify_unroot_relabel_eq hX (Or.inr rfl) σ _ _ ∅ classify_U5_zero ?_
    rw [← hPdef, card_eq_zero.1 hc]
    simp [relabelFamily]
  · obtain ⟨A, hA⟩ := card_eq_one.1 hc
    obtain ⟨-, hA2⟩ := hPmem A (by rw [hA]; exact mem_singleton_self A)
    obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.1 hA2
    have hc3 : #({p, q} : Finset X)ᶜ = 3 := by rw [card_compl, hX, hA2]
    obtain ⟨a, b, c, hab, hac, hbc, habc⟩ := card_eq_three.1 hc3
    have ha : a ∉ ({p, q} : Finset X) := by rw [← mem_compl, habc]; simp
    have hb : b ∉ ({p, q} : Finset X) := by rw [← mem_compl, habc]; simp
    have hc' : c ∉ ({p, q} : Finset X) := by rw [← mem_compl, habc]; simp
    simp only [mem_insert, mem_singleton, not_or] at ha hb hc'
    obtain ⟨e, he⟩ := classify_exists_equiv hX ![p, q, a, b, c] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    refine ⟨e, 1, by simp, ?_⟩
    refine classify_unroot_relabel_eq hX (Or.inr rfl) σ e _ {{0, 1}} classify_U5_one ?_
    rw [← hPdef, hA]
    simp [relabelFamily, he]
  · obtain ⟨A, B, hAB, hP⟩ := card_eq_two.1 hc
    have hA := hPmem A (by rw [hP]; simp)
    have hB := hPmem B (by rw [hP]; simp)
    have hd := classify_disjoint_of_card_two hX σ hA.1 hB.1 hA.2 hB.2 hAB
    obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.1 hA.2
    obtain ⟨r, s, hrs, rfl⟩ := card_eq_two.1 hB.2
    have h1 : #({p, q} ∪ {r, s} : Finset X)ᶜ = 1 := by
      rw [card_compl, card_union_of_disjoint hd, hA.2, hB.2, hX]
    obtain ⟨m, hm⟩ := card_eq_one.1 h1
    have hm' : m ∉ ({p, q} ∪ {r, s} : Finset X) := by rw [← mem_compl, hm]; simp
    simp only [mem_union, mem_insert, mem_singleton, not_or] at hm'
    simp only [disjoint_insert_left, disjoint_singleton_left, mem_insert, mem_singleton,
      not_or] at hd
    obtain ⟨e, he⟩ := classify_exists_equiv hX ![p, q, m, r, s] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    refine ⟨e, 2, by simp, ?_⟩
    refine classify_unroot_relabel_eq hX (Or.inr rfl) σ e _ {{0, 1}, {3, 4}} classify_U5_two ?_
    rw [← hPdef, hP]
    simp [relabelFamily, he]

theorem classify_mem_rootings5 (τ : SpeciesTree (Fin 5)) (k : ℕ)
    (hk : k ∈ ({0, 1, 2} : Finset ℕ)) (h : unroot τ.clusters = U5 k) :
    τ.clusters ∈ rootings5 k := by
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · exact classify_mem_of_forall classify_rootings5_zero classify_cands5_zero (by simp) h
  · exact classify_mem_of_forall classify_rootings5_one classify_cands5_one classify_splits5_one h
  · exact classify_mem_of_forall classify_rootings5_two classify_cands5_two classify_splits5_two h

/-- A binary 5-taxon species tree has unrooted shape `U5 2`. -/
theorem exists_equiv_unroot_eq_U5_two_of_isBinary (hX : Fintype.card X = 5) (σ : SpeciesTree X)
    (hσ : σ.IsBinary) :
    ∃ e : Fin 5 ≃ X, unroot (σ.relabel e.symm).clusters = U5 2 := by
  obtain ⟨e, k, hk, h⟩ := exists_equiv_unroot_eq_U5 hX σ
  refine ⟨e, ?_⟩
  have hb : (σ.relabel e.symm).IsBinary := (σ.isBinary_relabel_iff e.symm).2 hσ
  have hmem := classify_mem_rootings5 _ k hk h
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · exact absurd hb (classify_not_binary_of_mem_rootings5_zero _ hmem)
  · exact absurd hb (classify_not_binary_of_mem_rootings5_one _ hmem)
  · exact h

theorem mem_rootings4 (τ : SpeciesTree (Fin 4)) (k : ℕ) (hk : k ∈ ({0, 1} : Finset ℕ))
    (h : unroot τ.clusters = U4 k) : τ.clusters ∈ rootings4 k := by
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact classify_mem_of_forall classify_rootings4_zero classify_cands4_zero (by simp) h
  · exact classify_mem_of_forall classify_rootings4_one classify_cands4_one classify_splits4_one h

theorem mem_rootings5 (τ : SpeciesTree (Fin 5)) (k : ℕ) (hk : k ∈ ({0, 1, 2} : Finset ℕ))
    (h : unroot τ.clusters = U5 k) : τ.clusters ∈ rootings5 k :=
  classify_mem_rootings5 τ k hk h

theorem mem_binaryRootings5 (τ : SpeciesTree (Fin 5)) (hτ : τ.IsBinary)
    (h : unroot τ.clusters = U5 2) : τ.clusters ∈ binaryRootings5 :=
  classify_binary_of_mem_rootings5_two _ (classify_mem_rootings5 τ 2 (by simp) h) hτ

end ADR11
