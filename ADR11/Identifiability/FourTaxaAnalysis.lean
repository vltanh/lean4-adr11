module

public import ADR11.Rootings.Statements
public import ADR11.Trees.Classify
public import ADR11.Trees.Hierarchy

/-!
# The four-taxon analysis (binary species trees)

On four taxa, the unrooted gene tree distribution of a binary species tree determines exactly its
unrooted metric tree (Proposition 3, Theorem 9 for `|X| = 4`). After relabelling, a binary species
tree is one of the five binary rootings of `U4 1` (one internal edge, of length `t`), and by the
formulas of Section 4.1 for its labelling (the closed forms of `ADR11.Rootings.Statements`), the
gene tree with the split of the species tree has probability `1 - (2/3) e^{-t}` and the two others
`(1/3) e^{-t}`. Nonbinary species trees are treated in `ADR11.Nonbinary.FourTaxa`, by the limits
of Section 5.

## Main results

* `four_unrootedDist_of_mem_of_U4`, `four_unrootedDist_of_ne_of_U4`,
  `four_unrootedDist_of_star_of_U4`: the reduction to `Fin 4` (relabelling only, no formula).
* `four_unrootedDist_of_mem`, `four_unrootedDist_of_ne_of_isBinary`: the gene tree distribution of
  a binary species tree on four taxa, in terms of its unrooted metric tree.
* `four_unrootedDist_eq_zero`, `four_unrootedDist_ext`: only the three quartet trees have positive
  probability, so two distributions on four taxa agree once they agree on them.
* `four_unrootedDist_eq_of_sameUnrootedMetricTree`: for binary species trees the distribution
  depends only on `σ⁻` (one half of `unrootedDist_eq_iff_four`).
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

/-- A species tree whose clusters do not satisfy the binary condition is not binary. -/
private lemma four_not_isBinary_of_clusters {τ : SpeciesTree (Fin 4)}
    {H : Finset (Finset (Fin 4))} (hc : τ.clusters = H)
    (hH : ¬ ∀ A ∈ H, 2 ≤ #A → ∃ B ∈ H, ∃ C ∈ H, Disjoint B C ∧ B ∪ C = A) : ¬ τ.IsBinary := by
  intro hb
  refine hH fun A hA h2 => ?_
  rw [← hc] at hA ⊢
  exact hb A hA h2

/-- Section 4.1's formulas for the binary rootings of `U4 1 = AB|CD` (the four caterpillars and the
balanced tree), with internal edge length `t = τ.unrootedLength {0, 1}` (the length of the edge
above `{0, 1}` or `{2, 3}`, or their sum for the balanced rooting). -/
private lemma four_unrootedDist_U4_one (τ : SpeciesTree (Fin 4)) (hτ : τ.IsBinary)
    (h : unroot τ.clusters = U4 1) :
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
  -- the rootings `((a,b),c,d)` and `((c,d),a,b)` are not binary
  · exact absurd hτ (four_not_isBinary_of_clusters hc (by decide))
  · exact absurd hτ (four_not_isBinary_of_clusters hc (by decide))

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

/-! ### Reduction to `Fin 4` -/

/-- **Reduction to `Fin 4`** for the quartet tree with the split `A | Aᶜ` of the species tree: after
relabelling, the species tree has the unrooted topology `U4 1` and `A` becomes `{0, 1}` or `{2, 3}`,
so the probability is given by that of `AB|CD` for the relabelled tree (`core`). -/
theorem four_unrootedDist_of_mem_of_U4 (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    {A : Finset X} (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2)
    (core : ∀ e : Fin 4 ≃ X, unroot (σ.relabel e.symm).clusters = U4 1 →
      (σ.relabel e.symm).unrootedDist id (treeOfClusters {{0, 1}}) =
        1 - 2 / 3 * exp (-(σ.relabel e.symm).unrootedLength {0, 1})) :
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
  · have h1 := core e he
    rcases four_U4_one_card_two _ hA' hA'2 with h01 | h23
    · rw [h01, h1]
    · rw [h23, four_treeOfClusters_23, h1, ← four_compl_01, SpeciesTree.unrootedLength_compl]

/-- **Reduction to `Fin 4`** for the two quartet trees other than the one with the split `A | Aᶜ`
of the species tree: after relabelling they are `AC|BD` and `AD|BC` (`core`). -/
theorem four_unrootedDist_of_ne_of_U4 (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    {A B : Finset X} (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) (hB2 : #B = 2) (hBA : B ≠ A)
    (hBA' : B ≠ Aᶜ)
    (core : ∀ e : Fin 4 ≃ X, unroot (σ.relabel e.symm).clusters = U4 1 →
      (σ.relabel e.symm).unrootedDist id (treeOfClusters {{0, 2}}) =
          1 / 3 * exp (-(σ.relabel e.symm).unrootedLength {0, 1}) ∧
        (σ.relabel e.symm).unrootedDist id (treeOfClusters {{0, 3}}) =
          1 / 3 * exp (-(σ.relabel e.symm).unrootedLength {0, 1})) :
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
  · obtain ⟨h2, h3⟩ := core e he
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

/-- **Reduction to `Fin 4`** for a species tree without internal edge: after relabelling, its
unrooted topology is the star `U4 0` (`core`). -/
theorem four_unrootedDist_of_star_of_U4 (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (hσ : ∀ A ∈ unroot σ.clusters, #A ≠ 2) {B : Finset X} (hB2 : #B = 2)
    (core : ∀ e : Fin 4 ≃ X, unroot (σ.relabel e.symm).clusters = U4 0 →
      (σ.relabel e.symm).unrootedDist id (treeOfClusters {{0, 1}}) = 1 / 3 ∧
        (σ.relabel e.symm).unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 ∧
        (σ.relabel e.symm).unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3) :
    σ.unrootedDist id (treeOfClusters {B}) = 1 / 3 := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
  rw [four_dist_relabel e σ B]
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := core e he
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

/-! ### Binary species trees on four taxa (Section 4.1) -/

/-- The quartet tree with the split `A | Aᶜ` of a binary species tree has probability
`1 - (2/3) e^{-t}`, where `t` is the length of the internal edge (Section 4.1). -/
theorem four_unrootedDist_of_mem (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (hσ : σ.IsBinary) {A : Finset X} (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    σ.unrootedDist id (treeOfClusters {A}) = 1 - 2 / 3 * exp (-σ.unrootedLength A) :=
  four_unrootedDist_of_mem_of_U4 hX σ hA hA2 fun e he =>
    (four_unrootedDist_U4_one _ ((SpeciesTree.isBinary_relabel_iff σ e.symm).2 hσ) he).1

/-- The two quartet trees other than the one with the split `A | Aᶜ` of a binary species tree have
probability `(1/3) e^{-t}`, where `t` is the length of the internal edge (Section 4.1). -/
theorem four_unrootedDist_of_ne_of_isBinary (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (hσ : σ.IsBinary) {A B : Finset X} (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2)
    (hB2 : #B = 2) (hBA : B ≠ A) (hBA' : B ≠ Aᶜ) :
    σ.unrootedDist id (treeOfClusters {B}) = 1 / 3 * exp (-σ.unrootedLength A) :=
  four_unrootedDist_of_ne_of_U4 hX σ hA hA2 hB2 hBA hBA' fun e he =>
    (four_unrootedDist_U4_one _ ((SpeciesTree.isBinary_relabel_iff σ e.symm).2 hσ) he).2

/-- A binary species tree on four taxa has a nontrivial split: after relabelling, its unrooted
topology is not the star `U4 0`, none of whose rootings is binary. -/
private lemma four_exists_split_of_isBinary (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (hσ : σ.IsBinary) : ∃ A ∈ unroot σ.clusters, #A = 2 := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
  have hb := (SpeciesTree.isBinary_relabel_iff σ e.symm).2 hσ
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl
  · exfalso
    have hm := mem_rootings4 _ 0 (by decide) he
    simp only [rootings4, mem_insert, mem_singleton] at hm
    rcases hm with hc | hc | hc | hc | hc <;> exact four_not_isBinary_of_clusters hc (by decide) hb
  · refine ⟨({0, 1} : Finset (Fin 4)).map e.toEmbedding, ?_, by rw [card_map]; decide⟩
    rw [four_mem_unroot_relabel e σ, Finset.map_map,
      Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding,
      Finset.map_refl, he]
    exact four_mem_U4_one

/-- For binary species trees on four taxa, the gene tree distribution depends only on the unrooted
metric tree (Section 4.1): the half of `unrootedDist_eq_iff_four` for binary trees. -/
theorem four_unrootedDist_eq_of_sameUnrootedMetricTree (hX : Fintype.card X = 4)
    {σ σ' : SpeciesTree X} (hσ : σ.IsBinary) (hσ' : σ'.IsBinary)
    (h : σ.SameUnrootedMetricTree σ') : σ.unrootedDist id = σ'.unrootedDist id := by
  obtain ⟨hU, hL⟩ := h
  have hcard : ∀ A : Finset X, #Aᶜ = 4 - #A := fun A => by rw [card_compl, hX]
  have hlen : ∀ A ∈ unroot σ.clusters, #A = 2 → σ.unrootedLength A = σ'.unrootedLength A :=
    fun A hA hA2 => hL A hA (by omega) (by rw [hcard]; omega)
  obtain ⟨A, hA, hA2⟩ := four_exists_split_of_isBinary hX σ hσ
  refine four_unrootedDist_ext hX fun B hB2 => ?_
  by_cases hB : B ∈ unroot σ.clusters
  · rw [four_unrootedDist_of_mem hX σ hσ hB hB2,
      four_unrootedDist_of_mem hX σ' hσ' (hU ▸ hB) hB2, hlen B hB hB2]
  · have hne1 : B ≠ A := fun e => hB (e ▸ hA)
    have hne2 : B ≠ Aᶜ := fun e => hB (e ▸ compl_mem_unroot.2 hA)
    rw [four_unrootedDist_of_ne_of_isBinary hX σ hσ hA hA2 hB2 hne1 hne2,
      four_unrootedDist_of_ne_of_isBinary hX σ' hσ' (hU ▸ hA) hA2 hB2 hne1 hne2, hlen A hA hA2]

/-- Section 4.1: for a nontrivial split `A | Aᶜ` of `σ⁻` on four taxa, `σ` binary, the quartet tree
with that split is strictly the most probable, and the length of the internal edge is
`-log((3/2)(1 - ℙ(T)))`. (The binarity hypothesis is filled in from the context by
`assumption`.) -/
theorem four_recovery (hX : Fintype.card X = 4) (σ : SpeciesTree X) (hσ : σ.IsBinary)
    {A : Finset X} (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    (∀ B : Finset X, #B = 2 → B ≠ A → B ≠ Aᶜ →
        σ.unrootedDist id (treeOfClusters {B}) < σ.unrootedDist id (treeOfClusters {A})) ∧
      σ.unrootedLength A = -log (3 / 2 * (1 - σ.unrootedDist id (treeOfClusters {A}))) := by
  have h1 := four_unrootedDist_of_mem hX σ hσ hA hA2
  have hlt : exp (-σ.unrootedLength A) < 1 :=
    exp_lt_one_iff.2 (neg_lt_zero.2 (four_unrootedLength_pos σ hA))
  refine ⟨fun B hB2 hBA hBA' => ?_, ?_⟩
  · rw [four_unrootedDist_of_ne_of_isBinary hX σ hσ hA hA2 hB2 hBA hBA', h1]
    linarith
  · rw [h1, show 3 / 2 * (1 - (1 - 2 / 3 * exp (-σ.unrootedLength A))) =
      exp (-σ.unrootedLength A) by ring, log_exp, neg_neg]

/-! ### Any species tree with a nontrivial split -/

end ADR11
