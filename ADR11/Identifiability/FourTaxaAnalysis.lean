module

public import ADR11.Rootings.Statements
public import ADR11.Trees.Classify
public import ADR11.Trees.Hierarchy

/-!
# The four-taxon analysis

On four taxa, the unrooted gene tree distribution determines exactly the unrooted metric species
tree (Proposition 3, Theorem 9 for `|X| = 4`): after relabelling, a species tree is a rooting of
`U4 1` (one internal edge, of length `t`) or of the star `U4 0`; by the closed forms of
`ADR11.Rootings.Statements`, the gene tree with the split of the species tree has probability
`1 - (2/3) e^{-t}` and the two others `(1/3) e^{-t}`, or all three have probability `1/3`.

## Main results

* `four_unrootedDist_of_mem`, `four_unrootedDist_of_ne`, `four_unrootedDist_of_star`,
  `four_unrootedDist_eq_zero`: the gene tree distribution of any species tree on four taxa, in
  terms of its unrooted metric tree.
* `four_unrootedDist_ext`: two distributions on four taxa agree once they agree on the three
  quartet trees.
* `unrootedDist_eq_iff_four`: the distribution determines, and is determined by, `σ⁻`.
* `four_recovery`: the quartet tree with the split of `σ⁻` is strictly the most probable, and the
  internal edge length of `σ⁻` is `-log((3/2)(1 - ℙ(T)))` (Section 4.1).
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Relabelling quartet trees -/

private lemma four_map_compl {Y : Type*} [Fintype Y] [DecidableEq Y] (e : X ≃ Y)
    (A : Finset X) : (A.map e.toEmbedding)ᶜ = Aᶜ.map e.toEmbedding := by
  ext y
  simp [Finset.mem_map_equiv]

omit [Fintype X] [DecidableEq X] in
private lemma four_relabelFamily_singleton {Y : Type*} [DecidableEq Y] (e : X ≃ Y)
    (A : Finset X) : relabelFamily e {A} = {A.map e.toEmbedding} :=
  image_singleton _ _

/-- Relabelling the taxa of the unrooted tree with the nontrivial splits `A | Aᶜ`, `A ∈ C`. -/
private lemma four_relabelFamily_treeOfClusters {Y : Type*} [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (C : Finset (Finset X)) :
    relabelFamily e (treeOfClusters C) = treeOfClusters (relabelFamily e C) := by
  unfold treeOfClusters
  rw [← unroot_relabelFamily]
  congr 1
  unfold relabelFamily
  rw [image_insert, image_union, image_image, Finset.map_univ_equiv]
  congr 2
  ext D
  simp only [mem_image, mem_univ, true_and, Function.comp_apply, Finset.map_singleton]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨e.symm y, by simp⟩

/-- The probability of the quartet tree with the split `B | Bᶜ`, after relabelling the taxa along
`e.symm`. -/
private lemma four_dist_relabel (e : Fin 4 ≃ X) (σ : SpeciesTree X) (B : Finset X) :
    σ.unrootedDist id (treeOfClusters {B}) =
      (σ.relabel e.symm).unrootedDist id (treeOfClusters {B.map e.symm.toEmbedding}) := by
  rw [← SpeciesTree.unrootedDist_relabel σ e.symm (treeOfClusters {B}),
    four_relabelFamily_treeOfClusters, four_relabelFamily_singleton]

private lemma four_mem_unroot_relabel (e : Fin 4 ≃ X) (σ : SpeciesTree X) (B : Finset X) :
    B ∈ unroot σ.clusters ↔ B.map e.symm.toEmbedding ∈ unroot (σ.relabel e.symm).clusters := by
  rw [SpeciesTree.relabel_clusters, unroot_relabelFamily, map_mem_relabelFamily]

/-! ### Finite computations on `Fin 4` -/

private lemma four_U4_one_card_two :
    ∀ B : Finset (Fin 4), B ∈ U4 1 → #B = 2 → B = {0, 1} ∨ B = {2, 3} := by
  decide

private lemma four_U4_zero_card_two : ∀ B : Finset (Fin 4), B ∈ U4 0 → #B ≠ 2 := by
  decide

private lemma four_mem_U4_one : ({0, 1} : Finset (Fin 4)) ∈ U4 1 := by
  decide

private lemma four_compl_01 : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by
  decide

private lemma four_compl_23 : ({2, 3} : Finset (Fin 4))ᶜ = {0, 1} := by
  decide

private lemma four_treeOfClusters_23 :
    treeOfClusters {({2, 3} : Finset (Fin 4))} = treeOfClusters {{0, 1}} := by
  decide

/-- The three quartet trees on `Fin 4`. -/
private lemma four_treeOfClusters_cases : ∀ B : Finset (Fin 4), #B = 2 →
    treeOfClusters {B} = treeOfClusters {{0, 1}} ∨ treeOfClusters {B} = treeOfClusters {{0, 2}} ∨
      treeOfClusters {B} = treeOfClusters {{0, 3}} := by
  decide

private lemma four_treeOfClusters_cases' : ∀ B : Finset (Fin 4), #B = 2 → B ≠ {0, 1} →
    B ≠ {2, 3} →
      treeOfClusters {B} = treeOfClusters {{0, 2}} ∨
        treeOfClusters {B} = treeOfClusters {{0, 3}} := by
  decide

/-- The unrooted length of `A` as the sum of the lengths of the clusters among `A`, `Aᶜ`. -/
private lemma four_unrootedLength_eq_sum (τ : SpeciesTree X) (A : Finset X)
    {S : Finset (Finset X)}
    (hS : τ.clusters.filter (fun C => C ≠ univ ∧ (C = A ∨ C = Aᶜ)) = S) :
    τ.unrootedLength A = ∑ C ∈ S, τ.length C := by
  unfold SpeciesTree.unrootedLength
  rw [hS]

/-- The gene tree distribution of a rooting of `U4 1 = AB|CD`, with internal edge length
`t = τ.unrootedLength {0, 1}` (the length of the edge above `{0, 1}` or `{2, 3}`, or their sum for
the balanced rooting). -/
private lemma four_unrootedDist_U4_one (τ : SpeciesTree (Fin 4)) (h : unroot τ.clusters = U4 1) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * exp (-τ.unrootedLength {0, 1}) ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 * exp (-τ.unrootedLength {0, 1}) ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 * exp (-τ.unrootedLength {0, 1}) := by
  have hm := mem_rootings4 τ 1 (by decide) h
  simp only [rootings4, mem_insert, mem_singleton] at hm
  rcases hm with hc | hc | hc | hc | hc | hc | hc
  · obtain ⟨h1, h2, h3⟩ := rootingDist4_1_0 τ hc
    rw [four_unrootedLength_eq_sum τ {0, 1} (S := {{0, 1}}) (by rw [hc]; decide), sum_singleton]
    exact ⟨by rw [h1]; ring, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := rootingDist4_1_1 τ hc
    rw [four_unrootedLength_eq_sum τ {0, 1} (S := {{0, 1}}) (by rw [hc]; decide), sum_singleton]
    exact ⟨by rw [h1]; ring, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := rootingDist4_1_2 τ hc
    rw [four_unrootedLength_eq_sum τ {0, 1} (S := {{2, 3}}) (by rw [hc]; decide), sum_singleton]
    exact ⟨by rw [h1]; ring, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := rootingDist4_1_3 τ hc
    rw [four_unrootedLength_eq_sum τ {0, 1} (S := {{2, 3}}) (by rw [hc]; decide), sum_singleton]
    exact ⟨by rw [h1]; ring, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := rootingDist4_1_4 τ hc
    rw [four_unrootedLength_eq_sum τ {0, 1} (S := {{0, 1}, {2, 3}}) (by rw [hc]; decide),
      sum_pair (by decide), neg_add, exp_add]
    exact ⟨by rw [h1]; ring, by rw [h2]; ring, by rw [h3]; ring⟩
  · obtain ⟨h1, h2, h3⟩ := rootingDist4_1_5 τ hc
    rw [four_unrootedLength_eq_sum τ {0, 1} (S := {{0, 1}}) (by rw [hc]; decide), sum_singleton]
    exact ⟨by rw [h1]; ring, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := rootingDist4_1_6 τ hc
    rw [four_unrootedLength_eq_sum τ {0, 1} (S := {{2, 3}}) (by rw [hc]; decide), sum_singleton]
    exact ⟨by rw [h1]; ring, h2, h3⟩

/-- The gene tree distribution of a rooting of the star `U4 0`. -/
private lemma four_unrootedDist_U4_zero (τ : SpeciesTree (Fin 4)) (h : unroot τ.clusters = U4 0) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 / 3 ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 := by
  have hm := mem_rootings4 τ 0 (by decide) h
  simp only [rootings4, mem_insert, mem_singleton] at hm
  rcases hm with hc | hc | hc | hc | hc
  · exact rootingDist4_0_0 τ hc
  · exact rootingDist4_0_1 τ hc
  · exact rootingDist4_0_2 τ hc
  · exact rootingDist4_0_3 τ hc
  · exact rootingDist4_0_4 τ hc

/-! ### The gene tree distribution on four taxa -/

/-- The unrooted length of a split of a species tree is positive. -/
theorem four_unrootedLength_pos (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) : 0 < σ.unrootedLength A := by
  unfold SpeciesTree.unrootedLength
  refine Finset.sum_pos (fun C hC => ?_) ?_
  · rw [mem_filter] at hC
    exact σ.length_pos C hC.1 hC.2.1
  · rcases mem_unroot.1 hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨A, mem_filter.2 ⟨h1, h2, Or.inl rfl⟩⟩
    · exact ⟨Aᶜ, mem_filter.2 ⟨h1, h2, Or.inr rfl⟩⟩

/-- On four taxa, only the three quartet trees `treeOfClusters {B}` (`#B = 2`) have positive
probability. -/
theorem four_unrootedDist_eq_zero (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (T : Finset (Finset X)) (hT : ∀ B : Finset X, #B = 2 → T ≠ treeOfClusters {B}) :
    σ.unrootedDist id T = 0 := by
  let e : Fin 4 ≃ X := (Fintype.equivFinOfCardEq hX).symm
  have key : ∀ C : Finset (Fin 4), #C = 2 → relabelFamily e.symm T ≠ treeOfClusters {C} := by
    intro C hC hTC
    refine hT (C.map e.toEmbedding) (by rw [card_map, hC]) ?_
    have := congrArg (relabelFamily e.symm.symm) hTC
    rwa [relabelFamily_symm, four_relabelFamily_treeOfClusters, four_relabelFamily_singleton,
      Equiv.symm_symm] at this
  rw [← SpeciesTree.unrootedDist_relabel σ e.symm T]
  exact unrootedDist_eq_zero_four _ _ ⟨key _ (by decide), key _ (by decide), key _ (by decide)⟩

/-- On four taxa, two gene tree distributions agree as soon as they agree on the quartet
trees. -/
theorem four_unrootedDist_ext (hX : Fintype.card X = 4) {σ σ' : SpeciesTree X}
    (h : ∀ B : Finset X, #B = 2 →
      σ.unrootedDist id (treeOfClusters {B}) = σ'.unrootedDist id (treeOfClusters {B})) :
    σ.unrootedDist id = σ'.unrootedDist id := by
  funext T
  by_cases hT : ∃ B : Finset X, #B = 2 ∧ T = treeOfClusters {B}
  · obtain ⟨B, hB, rfl⟩ := hT
    exact h B hB
  · push Not at hT
    rw [four_unrootedDist_eq_zero hX σ T hT, four_unrootedDist_eq_zero hX σ' T hT]

/-- The quartet tree with the split `A | Aᶜ` of the species tree has probability
`1 - (2/3) e^{-t}`, where `t` is the length of the internal edge. -/
theorem four_unrootedDist_of_mem (hX : Fintype.card X = 4) (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    σ.unrootedDist id (treeOfClusters {A}) = 1 - 2 / 3 * exp (-σ.unrootedLength A) := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
  have hA' : A.map e.symm.toEmbedding ∈ U4 k := by
    rw [← he]
    exact (four_mem_unroot_relabel e σ A).1 hA
  have hA'2 : #(A.map e.symm.toEmbedding) = 2 := by rw [card_map, hA2]
  rw [four_dist_relabel e σ A, ← SpeciesTree.unrootedLength_relabel σ e.symm A]
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact absurd hA'2 (four_U4_zero_card_two _ hA')
  · obtain ⟨h1, -, -⟩ := four_unrootedDist_U4_one _ he
    rcases four_U4_one_card_two _ hA' hA'2 with h01 | h23
    · rw [h01, h1]
    · rw [h23, four_treeOfClusters_23, h1, ← four_compl_01, SpeciesTree.unrootedLength_compl]

/-- The two quartet trees other than the one with the split `A | Aᶜ` of the species tree have
probability `(1/3) e^{-t}`, where `t` is the length of the internal edge. -/
theorem four_unrootedDist_of_ne (hX : Fintype.card X = 4) (σ : SpeciesTree X) {A B : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) (hB2 : #B = 2) (hBA : B ≠ A) (hBA' : B ≠ Aᶜ) :
    σ.unrootedDist id (treeOfClusters {B}) = 1 / 3 * exp (-σ.unrootedLength A) := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
  have hA' : A.map e.symm.toEmbedding ∈ U4 k := by
    rw [← he]
    exact (four_mem_unroot_relabel e σ A).1 hA
  have hA'2 : #(A.map e.symm.toEmbedding) = 2 := by rw [card_map, hA2]
  have hB'2 : #(B.map e.symm.toEmbedding) = 2 := by rw [card_map, hB2]
  have hB'A : B.map e.symm.toEmbedding ≠ A.map e.symm.toEmbedding :=
    fun h => hBA (Finset.map_injective _ h)
  have hB'A' : B.map e.symm.toEmbedding ≠ (A.map e.symm.toEmbedding)ᶜ := by
    rw [four_map_compl]
    exact fun h => hBA' (Finset.map_injective _ h)
  rw [four_dist_relabel e σ B, ← SpeciesTree.unrootedLength_relabel σ e.symm A]
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact absurd hA'2 (four_U4_zero_card_two _ hA')
  · obtain ⟨-, h2, h3⟩ := four_unrootedDist_U4_one _ he
    have hcases : (σ.relabel e.symm).unrootedLength (A.map e.symm.toEmbedding) =
        (σ.relabel e.symm).unrootedLength {0, 1} ∧
        B.map e.symm.toEmbedding ≠ {0, 1} ∧ B.map e.symm.toEmbedding ≠ {2, 3} := by
      rcases four_U4_one_card_two _ hA' hA'2 with h01 | h23
      · rw [h01, four_compl_01] at hB'A'
        rw [h01] at hB'A
        exact ⟨by rw [h01], hB'A, hB'A'⟩
      · rw [h23, four_compl_23] at hB'A'
        rw [h23] at hB'A
        exact ⟨by rw [h23, ← four_compl_01, SpeciesTree.unrootedLength_compl], hB'A', hB'A⟩
    rw [hcases.1]
    rcases four_treeOfClusters_cases' _ hB'2 hcases.2.1 hcases.2.2 with h | h
    · rw [h, h2]
    · rw [h, h3]

/-- If the species tree has no internal edge, the three quartet trees have probability `1/3`. -/
theorem four_unrootedDist_of_star (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (hσ : ∀ A ∈ unroot σ.clusters, #A ≠ 2) {B : Finset X} (hB2 : #B = 2) :
    σ.unrootedDist id (treeOfClusters {B}) = 1 / 3 := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
  rw [four_dist_relabel e σ B]
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := four_unrootedDist_U4_zero _ he
    rcases four_treeOfClusters_cases (B.map e.symm.toEmbedding) (by rw [card_map, hB2])
      with h | h | h
    · rw [h, h1]
    · rw [h, h2]
    · rw [h, h3]
  · exfalso
    have h01 : ({0, 1} : Finset (Fin 4)) ∈ relabelFamily e.symm (unroot σ.clusters) := by
      rw [← unroot_relabelFamily, ← SpeciesTree.relabel_clusters, he]
      exact four_mem_U4_one
    rw [mem_relabelFamily] at h01
    exact hσ _ h01 (by rw [card_map]; decide)

/-- On four taxa, a set of taxa that is not of size `2` is a side of a split of the species tree
exactly when it is a single taxon or the complement of one. -/
private lemma four_mem_unroot_iff (hX : Fintype.card X = 4) (σ : SpeciesTree X) {A : Finset X}
    (hA : #A ≠ 2) : A ∈ unroot σ.clusters ↔ #A = 1 ∨ #A = 3 := by
  have hAc : #Aᶜ = 4 - #A := by rw [card_compl, hX]
  have hle : #A ≤ 4 := hX ▸ card_le_univ A
  have hne : ∀ C : Finset X, C ≠ univ → #C ≠ 4 := fun C hC h4 =>
    hC ((card_eq_iff_eq_univ C).1 (h4.trans hX.symm))
  have hne' : ∀ C : Finset X, #C ≠ 4 → C ≠ univ := fun C h hu =>
    h (by rw [hu, card_univ, hX])
  rw [mem_unroot]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have := (σ.nonempty_of_mem A h1).card_pos
      have := hne A h2
      omega
    · have := (σ.nonempty_of_mem _ h1).card_pos
      have := hne _ h2
      omega
  · rintro (h | h)
    · obtain ⟨x, rfl⟩ := card_eq_one.1 h
      exact Or.inl ⟨σ.singleton_mem x, hne' _ (by rw [card_singleton]; omega)⟩
    · obtain ⟨x, hx⟩ := card_eq_one.1 (show #Aᶜ = 1 by omega)
      exact Or.inr ⟨hx ▸ σ.singleton_mem x, hne' _ (by omega)⟩

/-- If two species trees on four taxa have the same gene tree distribution, every nontrivial
split of the first is a split of the second, of the same length. -/
private lemma four_mem_unroot_of_unrootedDist_eq (hX : Fintype.card X = 4)
    {σ σ' : SpeciesTree X} (h : σ.unrootedDist id = σ'.unrootedDist id) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    A ∈ unroot σ'.clusters ∧ σ.unrootedLength A = σ'.unrootedLength A := by
  have h1 := four_unrootedDist_of_mem hX σ hA hA2
  have hlt : exp (-σ.unrootedLength A) < 1 :=
    exp_lt_one_iff.2 (neg_lt_zero.2 (four_unrootedLength_pos σ hA))
  rw [h] at h1
  by_cases hA' : A ∈ unroot σ'.clusters
  · refine ⟨hA', ?_⟩
    rw [four_unrootedDist_of_mem hX σ' hA' hA2] at h1
    have : exp (-σ'.unrootedLength A) = exp (-σ.unrootedLength A) := by linarith
    rw [exp_eq_exp, neg_inj] at this
    exact this.symm
  · exfalso
    by_cases hex : ∃ A' ∈ unroot σ'.clusters, #A' = 2
    · obtain ⟨A', hA'm, hA'2⟩ := hex
      have hne1 : A ≠ A' := fun e => hA' (e ▸ hA'm)
      have hne2 : A ≠ A'ᶜ := fun e => hA' (e ▸ compl_mem_unroot.2 hA'm)
      rw [four_unrootedDist_of_ne hX σ' hA'm hA'2 hA2 hne1 hne2] at h1
      have : exp (-σ'.unrootedLength A') < 1 :=
        exp_lt_one_iff.2 (neg_lt_zero.2 (four_unrootedLength_pos σ' hA'm))
      linarith
    · push Not at hex
      rw [four_unrootedDist_of_star hX σ' hex hA2] at h1
      linarith

/-- On four taxa, two species trees have the same unrooted gene tree distribution exactly when
they have the same unrooted metric tree. -/
theorem unrootedDist_eq_iff_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  have hcard : ∀ A : Finset X, #Aᶜ = 4 - #A := fun A => by rw [card_compl, hX]
  have hle : ∀ A : Finset X, #A ≤ 4 := fun A => hX ▸ card_le_univ A
  constructor
  · intro h
    refine ⟨?_, fun A hA h2 h2' => (four_mem_unroot_of_unrootedDist_eq hX h hA
      (by have := hcard A; have := hle A; omega)).2⟩
    ext A
    by_cases hA2 : #A = 2
    · exact ⟨fun hA => (four_mem_unroot_of_unrootedDist_eq hX h hA hA2).1,
        fun hA => (four_mem_unroot_of_unrootedDist_eq hX h.symm hA hA2).1⟩
    · rw [four_mem_unroot_iff hX σ hA2, four_mem_unroot_iff hX σ' hA2]
  · rintro ⟨hU, hL⟩
    have hlen : ∀ A ∈ unroot σ.clusters, #A = 2 → σ.unrootedLength A = σ'.unrootedLength A :=
      fun A hA hA2 => hL A hA (by omega) (by rw [hcard]; omega)
    refine four_unrootedDist_ext hX fun B hB2 => ?_
    by_cases hB : B ∈ unroot σ.clusters
    · rw [four_unrootedDist_of_mem hX σ hB hB2, four_unrootedDist_of_mem hX σ' (hU ▸ hB) hB2,
        hlen B hB hB2]
    · by_cases hex : ∃ A ∈ unroot σ.clusters, #A = 2
      · obtain ⟨A, hA, hA2⟩ := hex
        have hne1 : B ≠ A := fun e => hB (e ▸ hA)
        have hne2 : B ≠ Aᶜ := fun e => hB (e ▸ compl_mem_unroot.2 hA)
        rw [four_unrootedDist_of_ne hX σ hA hA2 hB2 hne1 hne2,
          four_unrootedDist_of_ne hX σ' (hU ▸ hA) hA2 hB2 hne1 hne2, hlen A hA hA2]
      · push Not at hex
        rw [four_unrootedDist_of_star hX σ hex hB2,
          four_unrootedDist_of_star hX σ' (hU ▸ hex) hB2]

/-- Section 4.1: for a nontrivial split `A | Aᶜ` of `σ⁻` on four taxa, the quartet tree with that
split is strictly the most probable, and the length of the internal edge is
`-log((3/2)(1 - ℙ(T)))`. -/
theorem four_recovery (hX : Fintype.card X = 4) (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    (∀ B : Finset X, #B = 2 → B ≠ A → B ≠ Aᶜ →
        σ.unrootedDist id (treeOfClusters {B}) < σ.unrootedDist id (treeOfClusters {A})) ∧
      σ.unrootedLength A = -log (3 / 2 * (1 - σ.unrootedDist id (treeOfClusters {A}))) := by
  have h1 := four_unrootedDist_of_mem hX σ hA hA2
  have hlt : exp (-σ.unrootedLength A) < 1 :=
    exp_lt_one_iff.2 (neg_lt_zero.2 (four_unrootedLength_pos σ hA))
  refine ⟨fun B hB2 hBA hBA' => ?_, ?_⟩
  · rw [four_unrootedDist_of_ne hX σ hA hA2 hB2 hBA hBA', h1]
    linarith
  · rw [h1, show 3 / 2 * (1 - (1 - 2 / 3 * exp (-σ.unrootedLength A))) =
      exp (-σ.unrootedLength A) by ring, log_exp, neg_neg]

end ADR11
