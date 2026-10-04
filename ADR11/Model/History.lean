module

public import ADR11.MSC.Basic

/-!
# Coalescent histories: the structure of gene tree probabilities (Section 3)

Helpers for `ADR11.Model`.

* `model_jumpMatrixQ`, `model_jumpMatrix_pow_apply`, `model_kingmanAbsorption_eq_rat`: the jump
  chain, hence the population above the root, has rational transition probabilities.
* `model_IsHistorySum D φ`: the function `φ` of the edge lengths is a sum, over finitely many
  coalescent histories `h`, of `c(h) ∏_{b ∈ D} g_{i(h,b) j(h,b)}(len b)`, with rational
  `c(h) > 0` and `1 ≤ j(h,b) ≤ i(h,b) ≤ #b`. Such sums are closed under sums, nonnegative rational
  multiples, and products of sums over disjoint sets of clusters.
* `model_forestDist_isHistorySum`: the history decomposition of the multispecies coalescent with
  one lineage per taxon, by induction over the clusters (the populations whose lengths appear are
  the clusters other than the root with at least two taxa, `model_internal`).
* `model_equation3`: equation (3); `model_section3_polynomial`: gene tree probabilities are
  polynomials with rational coefficients in the `exp (-x_b)`.
* `model_forestDist_congr_internal`: with one lineage per taxon, pendant edge lengths do not
  matter.
* `model_rootedDist_support`: with at least one lineage, gene trees are binary hierarchies with
  probability `1`.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-! ### The jump chain has rational transition probabilities -/

section Rational

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The jump chain of Kingman's coalescent, with rational entries. -/
def model_jumpMatrixQ : Matrix (Finset (Finset L)) (Finset (Finset L)) ℚ :=
  fun F G =>
    if #(roots F) ≤ 1 then (if G = F then 1 else 0)
    else if G ∈ merges F then (((#(roots F)).choose 2 : ℕ) : ℚ)⁻¹ else 0

theorem model_jumpMatrix_eq_map :
    (jumpMatrix : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) =
      (Rat.castHom ℝ).mapMatrix model_jumpMatrixQ := by
  ext F G
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  unfold jumpMatrix model_jumpMatrixQ
  split_ifs <;> simp

theorem model_jumpMatrix_pow_apply (n : ℕ) (F G : Finset (Finset L)) :
    (jumpMatrix ^ n) F G = (((model_jumpMatrixQ ^ n) F G : ℚ) : ℝ) := by
  rw [model_jumpMatrix_eq_map, ← map_pow, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

/-- The population above the root has rational, nonnegative transition probabilities. -/
theorem model_kingmanAbsorption_eq_rat {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) : ∃ q : ℚ, 0 ≤ q ∧ kingmanAbsorption F G = q := by
  have h : ∃ q : ℚ, kingmanAbsorption F G = q := by
    rw [kingmanAbsorption_apply hF]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨_, model_jumpMatrix_pow_apply _ F G⟩
    · exact ⟨0, by simp⟩
  obtain ⟨q, hq⟩ := h
  refine ⟨q, ?_, hq⟩
  have := kingmanAbsorption_nonneg hF G
  rw [hq] at this
  exact_mod_cast this

end Rational

/-! ### Sums over coalescent histories -/

section HistorySum

variable {X : Type*}

/-- `φ`, a function of the edge lengths, is a sum over finitely many coalescent histories `h` of
`c(h) ∏_{b ∈ D} g_{i(h,b) j(h,b)}(len b)`, with rational `c(h) > 0` and
`1 ≤ j(h,b) ≤ i(h,b) ≤ #b`. -/
def model_IsHistorySum (D : Finset (Finset X)) (φ : (Finset X → ℝ) → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℚ) (i j : ι → Finset X → ℕ),
    (∀ h, 0 < c h) ∧ (∀ h, ∀ b ∈ D, 1 ≤ j h b ∧ j h b ≤ i h b ∧ i h b ≤ #b) ∧
    ∀ len, φ len = ∑ h : ι, (c h : ℝ) * ∏ b ∈ D, deathProb (i h b) (j h b) (len b)

theorem model_IsHistorySum.congr {D : Finset (Finset X)} {φ ψ : (Finset X → ℝ) → ℝ}
    (h : model_IsHistorySum D φ) (e : ∀ len, ψ len = φ len) : model_IsHistorySum D ψ := by
  obtain ⟨ι, _, c, i, j, hc, hij, hφ⟩ := h
  exact ⟨ι, inferInstance, c, i, j, hc, hij, fun len => (e len).trans (hφ len)⟩

theorem model_isHistorySum_zero (D : Finset (Finset X)) :
    model_IsHistorySum D fun _ => 0 :=
  ⟨Empty, inferInstance, Empty.elim, Empty.elim, Empty.elim, fun h => h.elim, fun h => h.elim,
    fun _ => by simp⟩

theorem model_isHistorySum_one : model_IsHistorySum (∅ : Finset (Finset X)) fun _ => 1 :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ _ => 0, fun _ _ => 0, fun _ => one_pos,
    fun _ _ hb => absurd hb (notMem_empty _), fun _ => by simp⟩

theorem model_isHistorySum_single {b : Finset X} {k j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k)
    (h3 : k ≤ #b) : model_IsHistorySum {b} fun len => deathProb k j (len b) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ _ => k, fun _ _ => j, fun _ => one_pos,
    fun _ b' hb' => by rw [mem_singleton.1 hb']; exact ⟨h1, h2, h3⟩, fun _ => by simp⟩

theorem model_isHistorySum_add {D : Finset (Finset X)} {φ ψ : (Finset X → ℝ) → ℝ}
    (hφ : model_IsHistorySum D φ) (hψ : model_IsHistorySum D ψ) :
    model_IsHistorySum D fun len => φ len + ψ len := by
  obtain ⟨ι, _, c, i, j, hc, hij, hφ⟩ := hφ
  obtain ⟨κ, _, c', i', j', hc', hij', hψ⟩ := hψ
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim c c', Sum.elim i i', Sum.elim j j', ?_, ?_, ?_⟩
  · rintro (h | h)
    · exact hc h
    · exact hc' h
  · rintro (h | h)
    · exact hij h
    · exact hij' h
  · intro len
    dsimp only
    rw [Fintype.sum_sum_type, hφ, hψ]
    rfl

theorem model_isHistorySum_sum {α : Type*} {D : Finset (Finset X)} (s : Finset α)
    {φ : α → (Finset X → ℝ) → ℝ} (h : ∀ a ∈ s, model_IsHistorySum D (φ a)) :
    model_IsHistorySum D fun len => ∑ a ∈ s, φ a len := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (model_isHistorySum_zero D).congr fun _ => sum_empty
  | insert a s ha ih =>
    exact (model_isHistorySum_add (h a (mem_insert_self a s))
      (ih fun b hb => h b (mem_insert_of_mem hb))).congr fun _ => sum_insert ha

theorem model_isHistorySum_smul {D : Finset (Finset X)} {φ : (Finset X → ℝ) → ℝ}
    (hφ : model_IsHistorySum D φ) {q : ℚ} (hq : 0 ≤ q) :
    model_IsHistorySum D fun len => (q : ℝ) * φ len := by
  rcases hq.eq_or_lt with rfl | hq
  · exact (model_isHistorySum_zero D).congr fun _ => by simp
  · obtain ⟨ι, _, c, i, j, hc, hij, hφ⟩ := hφ
    refine ⟨ι, inferInstance, fun h => q * c h, i, j, fun h => mul_pos hq (hc h), hij,
      fun len => ?_⟩
    dsimp only
    rw [hφ, mul_sum]
    refine sum_congr rfl fun h _ => ?_
    push_cast
    ring

theorem model_isHistorySum_mul [DecidableEq X] {D D' : Finset (Finset X)} (hD : Disjoint D D')
    {φ ψ : (Finset X → ℝ) → ℝ} (hφ : model_IsHistorySum D φ) (hψ : model_IsHistorySum D' ψ) :
    model_IsHistorySum (D ∪ D') fun len => φ len * ψ len := by
  obtain ⟨ι, _, c, i, j, hc, hij, hφ⟩ := hφ
  obtain ⟨κ, _, c', i', j', hc', hij', hψ⟩ := hψ
  refine ⟨ι × κ, inferInstance, fun h => c h.1 * c' h.2,
    fun h b => if b ∈ D then i h.1 b else i' h.2 b,
    fun h b => if b ∈ D then j h.1 b else j' h.2 b, fun h => mul_pos (hc h.1) (hc' h.2), ?_, ?_⟩
  · rintro ⟨h, h'⟩ b hb
    by_cases hbD : b ∈ D
    · simp only [hbD, ↓reduceIte]
      exact hij h b hbD
    · simp only [hbD, ↓reduceIte]
      exact hij' h' b ((mem_union.1 hb).resolve_left hbD)
  · intro len
    dsimp only
    rw [hφ, hψ, sum_mul_sum, Fintype.sum_prod_type]
    refine sum_congr rfl fun h _ => sum_congr rfl fun h' _ => ?_
    rw [prod_union hD]
    have e1 : ∏ b ∈ D, deathProb (if b ∈ D then i h b else i' h' b)
        (if b ∈ D then j h b else j' h' b) (len b) =
        ∏ b ∈ D, deathProb (i h b) (j h b) (len b) :=
      prod_congr rfl fun b hb => by simp only [hb, ↓reduceIte]
    have e2 : ∏ b ∈ D', deathProb (if b ∈ D then i h b else i' h' b)
        (if b ∈ D then j h b else j' h' b) (len b) =
        ∏ b ∈ D', deathProb (i' h' b) (j' h' b) (len b) :=
      prod_congr rfl fun b hb => by simp only [disjoint_right.1 hD hb, ↓reduceIte]
    dsimp only
    rw [e1, e2]
    push_cast
    ring

theorem model_isHistorySum_prod [DecidableEq X] {α : Type*} [DecidableEq α] (s : Finset α)
    {D : α → Finset (Finset X)} (hD : (s : Set α).PairwiseDisjoint D)
    {φ : α → (Finset X → ℝ) → ℝ} (h : ∀ a ∈ s, model_IsHistorySum (D a) (φ a)) :
    model_IsHistorySum (s.biUnion D) fun len => ∏ a ∈ s, φ a len := by
  induction s using Finset.induction_on with
  | empty =>
    rw [biUnion_empty]
    exact model_isHistorySum_one.congr fun _ => prod_empty
  | insert a s ha ih =>
    rw [biUnion_insert]
    have hD' : (s : Set α).PairwiseDisjoint D := hD.subset (by simp)
    have hdis : Disjoint (D a) (s.biUnion D) := by
      rw [disjoint_biUnion_right]
      intro b hb
      exact hD (by simp) (by simp [hb]) (fun hab => ha (hab ▸ hb))
    exact (model_isHistorySum_mul hdis (h a (mem_insert_self a s))
      (ih hD' fun b hb => h b (mem_insert_of_mem hb))).congr fun _ => prod_insert ha

end HistorySum

/-! ### The history decomposition -/

section Decomposition

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The populations below the cluster `A` whose lengths enter the gene tree probabilities with one
lineage per taxon: the clusters `b ⊆ A` of `H`, other than the root, with at least two taxa. -/
def model_internal (H : Finset (Finset X)) (A : Finset X) : Finset (Finset X) :=
  H.filter fun b => b ⊆ A ∧ b ≠ univ ∧ 2 ≤ #b

theorem model_mem_internal {H : Finset (Finset X)} {A b : Finset X} :
    b ∈ model_internal H A ↔ b ∈ H ∧ b ⊆ A ∧ b ≠ univ ∧ 2 ≤ #b := by
  unfold model_internal
  rw [mem_filter]

theorem model_internal_of_card_le_one {H : Finset (Finset X)} {A : Finset X} (hA : #A ≤ 1) :
    model_internal H A = ∅ := by
  refine eq_empty_of_forall_notMem fun b hb => ?_
  obtain ⟨-, hbA, -, hb2⟩ := model_mem_internal.1 hb
  have := card_le_card hbA
  omega

/-- A cluster strictly inside `A` lies inside a child of `A`. -/
private theorem model_exists_child_superset {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A b : Finset X} (hb : b ∈ H) (hbA : b ⊂ A) : ∃ B ∈ childClusters H A, b ⊆ B := by
  obtain ⟨x, hx⟩ := hH.2.2.1 b hb
  have hA2 : 2 ≤ #A := by
    have h2 := card_lt_card hbA
    have h3 := (hH.2.2.1 b hb).card_pos
    omega
  obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters hA2 (hbA.subset hx)
  refine ⟨B, hB, ?_⟩
  obtain ⟨hBH, -, hmax⟩ := mem_childClusters.1 hB
  rcases hH.2.2.2 b hb B hBH with h | h | h
  · exact h
  · rcases h.eq_or_ssubset with h' | h'
    · exact h'.ge
    · exact absurd hbA (hmax b hb h')
  · exact absurd hxB (disjoint_left.1 h hx)

private theorem model_internal_pairwiseDisjoint {H : Finset (Finset X)} (hH : IsHierarchy H)
    (A : Finset X) :
    ((univ : Finset (childClusters H A)) : Set (childClusters H A)).PairwiseDisjoint
      fun B => model_internal H B := by
  intro B _ B' _ hBB'
  refine disjoint_left.2 fun b hb hb' => ?_
  obtain ⟨-, hbB, -, hb2⟩ := model_mem_internal.1 hb
  obtain ⟨-, hbB', -, -⟩ := model_mem_internal.1 hb'
  have hdis := hH.disjoint_of_mem_childClusters B.2 B'.2 (fun h => hBB' (Subtype.ext h))
  obtain ⟨x, hx⟩ : b.Nonempty := card_pos.1 (by omega)
  exact disjoint_left.1 hdis (hbB hx) (hbB' hx)

private theorem model_internal_erase {H : Finset (Finset X)} (hH : IsHierarchy H)
    (A : Finset X) :
    (model_internal H A).erase A =
      (univ : Finset (childClusters H A)).biUnion fun B => model_internal H B := by
  ext b
  rw [mem_erase, model_mem_internal, mem_biUnion]
  constructor
  · rintro ⟨hbA', hb, hbA, hbu, hb2⟩
    obtain ⟨B, hB, hbB⟩ := model_exists_child_superset hH hb (hbA.ssubset_of_ne hbA')
    exact ⟨⟨B, hB⟩, mem_univ _, model_mem_internal.2 ⟨hb, hbB, hbu, hb2⟩⟩
  · rintro ⟨B, -, hbB⟩
    obtain ⟨hb, hbB, hbu, hb2⟩ := model_mem_internal.1 hbB
    have hBA := (mem_childClusters.1 B.2).2.1
    exact ⟨fun h => not_subset_of_ssubset hBA (h ▸ hbB), hb, hbB.trans hBA.subset, hbu, hb2⟩

private theorem model_internal_of_ne_univ {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : A ∈ H) (hAu : A ≠ univ) (h2 : 2 ≤ #A) :
    model_internal H A =
      ((univ : Finset (childClusters H A)).biUnion fun B => model_internal H B) ∪ {A} := by
  rw [← model_internal_erase hH, union_comm, ← insert_eq,
    insert_erase (model_mem_internal.2 ⟨hA, subset_rfl, hAu, h2⟩)]

private theorem model_internal_univ {H : Finset (Finset X)} (hH : IsHierarchy H) :
    model_internal H univ =
      (univ : Finset (childClusters H univ)).biUnion fun B => model_internal H B := by
  rw [← model_internal_erase hH, erase_eq_of_notMem fun h => (model_mem_internal.1 h).2.2.1 rfl]

/-- **The history decomposition.** With one lineage per taxon, the probability that the forest
leaving the population above a cluster `A` is `G` is a sum over coalescent histories, with
rational weights depending only on the topologies, of products of the `g`'s of the populations
below `A`. -/
theorem model_forestDist_isHistorySum {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : A ∈ H) (G : Finset (Finset X)) :
    model_IsHistorySum (model_internal H A) fun len => forestDist H len id A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  by_cases h2 : 2 ≤ #A
  swap
  · obtain ⟨x, rfl⟩ : ∃ x, A = {x} :=
      card_eq_one.1 (by have := (hH.2.2.1 A hA).card_pos; omega)
    rw [model_internal_of_card_le_one (by omega)]
    refine (model_isHistorySum_smul model_isHistorySum_one
      (q := if G = {{x}} then 1 else 0) (by split_ifs <;> norm_num)).congr fun len => ?_
    rw [forestDist_id_singleton hH, mul_one]
    split_ifs <;> simp
  have hch : ∀ B : childClusters H A, (B : Finset X) ⊂ A ∧ (B : Finset X) ∈ H :=
    fun B => ⟨(mem_childClusters.1 B.2).2.1, (mem_childClusters.1 B.2).1⟩
  have hunf : ∀ len, forestDist H len id A G =
      ∑ f : childClusters H A → Finset (Finset X),
        (∏ B : childClusters H A, forestDist H len id B (f B)) *
          populationKernel len A (univ.sup f ∪ sampledForest id A) G := fun len => by
    rw [forestDist]
  refine (model_isHistorySum_sum (univ : Finset (childClusters H A → Finset (Finset X)))
    (φ := fun f len => (∏ B : childClusters H A, forestDist H len id B (f B)) *
      populationKernel len A (univ.sup f ∪ sampledForest id A) G) fun f _ => ?_).congr hunf
  by_cases hf : ∀ B : childClusters H A,
      IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => id l ∈ (B : Finset X))
  · obtain ⟨hF, hSF, hLF⟩ := hH.isForest_entering f hf
    have hprod := model_isHistorySum_prod (univ : Finset (childClusters H A))
      (model_internal_pairwiseDisjoint hH A)
      (φ := fun B len => forestDist H len id B (f B)) fun B _ => ih B (hch B).1 (hch B).2 (f B)
    by_cases hAu : A = univ
    · subst hAu
      obtain ⟨q, hq0, hq⟩ := model_kingmanAbsorption_eq_rat hF G
      rw [model_internal_univ hH]
      refine (model_isHistorySum_smul hprod hq0).congr fun len => ?_
      rw [populationKernel, ite_eq_left rfl, hq, mul_comm]
    · set F := univ.sup f ∪ sampledForest id A
      have hK : ∀ len, populationKernel len A F G =
          deathProb (#(roots F)) (#(roots G)) (len A) *
            (((model_jumpMatrixQ ^ (#(roots F) - #(roots G))) F G : ℚ) : ℝ) := fun len => by
        rw [populationKernel, ite_eq_right hAu, kingmanTransition_apply hF,
          model_jumpMatrix_pow_apply]
      by_cases hJ : (jumpMatrix ^ (#(roots F) - #(roots G))) F G = 0
      · refine (model_isHistorySum_zero _).congr fun len => ?_
        rw [hK, ← model_jumpMatrix_pow_apply, hJ, mul_zero, mul_zero]
      · obtain ⟨-, -, -, h4⟩ := jumpMatrix_pow_support hF hJ
        have hLA : lineages F = A := by
          rw [hLF]
          ext
          simp
        have hkA : #(roots F) ≤ #A := hLA ▸ hF.card_roots_le_card_lineages
        have hk1 : 1 ≤ #(roots F) := by
          obtain ⟨x, hx⟩ : A.Nonempty := card_pos.1 (by omega)
          have hxF : {x} ∈ F := hSF (singleton_mem_sampledForest.2 hx)
          exact card_pos.2 (roots_nonempty_iff.2 ⟨_, hxF⟩)
        have hj : 1 ≤ #(roots G) ∧ #(roots G) ≤ #(roots F) := by
          split_ifs at h4 <;> omega
        have hq0 : 0 ≤ (model_jumpMatrixQ ^ (#(roots F) - #(roots G))) F G := by
          have := jumpMatrix_pow_nonneg (#(roots F) - #(roots G)) F G
          rw [model_jumpMatrix_pow_apply] at this
          exact_mod_cast this
        have hdis : Disjoint
            ((univ : Finset (childClusters H A)).biUnion fun B => model_internal H B) {A} := by
          rw [disjoint_singleton_right, mem_biUnion]
          rintro ⟨B, -, hAB⟩
          exact not_subset_of_ssubset (hch B).1 (model_mem_internal.1 hAB).2.1
        rw [model_internal_of_ne_univ hH hA hAu h2]
        refine (model_isHistorySum_smul (model_isHistorySum_mul hdis hprod
          (model_isHistorySum_single (b := A) hj.1 hj.2 hkA)) hq0).congr fun len => ?_
        rw [hK]
        ring
  · obtain ⟨B, hB⟩ := not_forall.1 hf
    have h0 : ∀ len, forestDist H len id B (f B) = 0 := fun len => by
      by_contra hne
      obtain ⟨h1, -, h3⟩ := forestDist_support hH len id (hch B).2 hne
      exact hB ⟨h1, h3⟩
    refine (model_isHistorySum_zero _).congr fun len => ?_
    rw [prod_eq_zero (mem_univ B) (h0 len), zero_mul]

/-- **Equation (3)** and the history decomposition. -/
theorem model_equation3 (H : Finset (Finset X)) (G : Finset (Finset X)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℚ) (i j : ι → Finset X → ℕ),
      (∀ h, 0 < c h) ∧
      (∀ h, ∀ b ∈ H, b ≠ univ → 2 ≤ #b → 1 ≤ j h b ∧ j h b ≤ i h b ∧ i h b ≤ #b) ∧
      ∀ σ : SpeciesTree X, σ.clusters = H →
        σ.rootedDist id G =
          ∑ h : ι, (c h : ℝ) * ∏ b ∈ H with b ≠ univ ∧ 2 ≤ #b,
            coalescenceProb (i h b) (j h b) (σ.length b) := by
  by_cases hH : IsHierarchy H
  · obtain ⟨ι, _, c, i, j, hc, hij, hφ⟩ := model_forestDist_isHistorySum hH hH.1 G
    have hD : model_internal H univ = H.filter fun b => b ≠ univ ∧ 2 ≤ #b := by
      unfold model_internal
      exact filter_congr fun b _ => by simp
    refine ⟨ι, inferInstance, c, i, j, hc, fun h b hb hbu hb2 =>
      hij h b (hD ▸ mem_filter.2 ⟨hb, hbu, hb2⟩), fun σ hσ => ?_⟩
    rw [SpeciesTree.rootedDist, hσ]
    refine (hφ σ.length).trans ?_
    rw [hD]
    simp_rw [coalescenceProb_eq_deathProb]
  · exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, Empty.elim, fun h => h.elim,
      fun h => h.elim, fun σ hσ => absurd (hσ ▸ σ.isHierarchy) hH⟩

/-! ### Polynomials in the transformed branch lengths -/

/-- Tavaré's coefficient `a_ijk`, as a rational number. -/
def model_tavareQ (i j k : ℕ) : ℚ :=
  (2 * k - 1) * (-1) ^ (k - j) / ((j.factorial : ℚ) * (k - j).factorial * (j + k - 1)) *
    ∏ m ∈ range k, (((j : ℚ) + m) * ((i : ℚ) - m) / ((i : ℚ) + m))

theorem model_tavareQ_cast (i j k : ℕ) : (model_tavareQ i j k : ℝ) = tavareCoeff i j k := by
  unfold model_tavareQ tavareCoeff
  push_cast
  rfl

/-- The polynomial `∑_{m=j}^{k} a_{kjm} X_b^{m choose 2}`, which evaluates to `g_kj(x_b)` at
`X_b = exp (-x_b)`. -/
noncomputable def model_deathPoly (k j : ℕ) (b : Finset X) : MvPolynomial (Finset X) ℚ :=
  ∑ m ∈ Icc j k, MvPolynomial.C (model_tavareQ k j m) * MvPolynomial.X b ^ (m.choose 2)

omit [Fintype X] [DecidableEq X] in
theorem model_aeval_deathPoly {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (b : Finset X)
    (len : Finset X → ℝ) :
    MvPolynomial.aeval (fun b => exp (-len b)) (model_deathPoly k j b) = deathProb k j (len b) := by
  rw [deathProb_eq_tavare k j hj hjk, model_deathPoly, map_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, ← Real.exp_nat_mul,
    eq_ratCast, model_tavareQ_cast, mul_neg]
  exact mul_comm _ _

/-- Gene tree probabilities, rooted and unrooted, are polynomials with rational coefficients in
the transformed branch lengths `exp (-x_b)`, depending only on the topologies. -/
theorem model_section3_polynomial (H : Finset (Finset X)) (G T : Finset (Finset X)) :
    ∃ p q : MvPolynomial (Finset X) ℚ,
      ∀ σ : SpeciesTree X, σ.clusters = H →
        σ.rootedDist id G = MvPolynomial.aeval (fun b => exp (-σ.length b)) p ∧
        σ.unrootedDist id T = MvPolynomial.aeval (fun b => exp (-σ.length b)) q := by
  have key : ∀ G : Finset (Finset X), ∃ p : MvPolynomial (Finset X) ℚ,
      ∀ σ : SpeciesTree X, σ.clusters = H →
        σ.rootedDist id G = MvPolynomial.aeval (fun b => exp (-σ.length b)) p := by
    intro G
    obtain ⟨ι, _, c, i, j, -, hij, hσ⟩ := model_equation3 H G
    refine ⟨∑ h : ι, MvPolynomial.C (c h) *
      ∏ b ∈ H with b ≠ univ ∧ 2 ≤ #b, model_deathPoly (i h b) (j h b) b, fun σ hσH => ?_⟩
    rw [hσ σ hσH, map_sum]
    refine sum_congr rfl fun h _ => ?_
    rw [map_mul, map_prod, MvPolynomial.aeval_C, eq_ratCast]
    congr 1
    refine prod_congr rfl fun b hb => ?_
    rw [mem_filter] at hb
    have hb' := hij h b hb.1 hb.2.1 hb.2.2
    rw [model_aeval_deathPoly hb'.1 hb'.2.1 b σ.length, coalescenceProb_eq_deathProb]
  choose p hp using key
  refine ⟨p G, ∑ G' : Finset (Finset X), if unroot G' = T then p G' else 0,
    fun σ hσ => ⟨hp G σ hσ, ?_⟩⟩
  rw [SpeciesTree.unrootedDist, map_sum]
  refine sum_congr rfl fun G' _ => ?_
  split_ifs
  · exact hp G' σ hσ
  · simp

/-! ### Pendant edges -/

/-- With one lineage per taxon, `forestDist` depends on the lengths only through the edges above
the clusters other than the root with at least two taxa. -/
theorem model_forestDist_congr_internal {H : Finset (Finset X)} (hH : IsHierarchy H)
    {len len' : Finset X → ℝ} (hlen : ∀ A ∈ H, 2 ≤ #A → A ≠ univ → len A = len' A)
    {A : Finset X} (hA : A ∈ H) (G : Finset (Finset X)) :
    forestDist H len id A G = forestDist H len' id A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  by_cases h2 : 2 ≤ #A
  · rw [forestDist.eq_1 H len, forestDist.eq_1 H len']
    have hK : populationKernel (L := X) len A = populationKernel len' A := by
      unfold populationKernel
      split_ifs with hAu
      · rfl
      · rw [hlen A hA h2 hAu]
    refine sum_congr rfl fun f _ => ?_
    rw [hK]
    congr 1
    exact prod_congr rfl fun B _ =>
      ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 _
  · obtain ⟨x, rfl⟩ : ∃ x, A = {x} :=
      card_eq_one.1 (by have := (hH.2.2.1 A hA).card_pos; omega)
    rw [forestDist_id_singleton hH, forestDist_id_singleton hH]

/-- Section 2: with one lineage per taxon, the rooted gene tree distribution depends only on the
rooted metric species tree. -/
theorem model_rootedDist_eq_of_sameRootedMetricTree {σ σ' : SpeciesTree X}
    (h : σ.SameRootedMetricTree σ') : σ.rootedDist id = σ'.rootedDist id := by
  obtain ⟨hc, hl⟩ := h
  funext G
  unfold SpeciesTree.rootedDist
  rw [← hc]
  exact model_forestDist_congr_internal σ.isHierarchy hl σ.univ_mem G

end Decomposition

/-! ### Gene trees are binary -/

section Binary

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

/-- Every cluster with at least two elements is the union of two disjoint clusters. -/
def model_IsBinaryForest (F : Finset (Finset L)) : Prop :=
  ∀ A ∈ F, 2 ≤ #A → ∃ B ∈ F, ∃ C ∈ F, Disjoint B C ∧ B ∪ C = A

theorem model_isBinaryForest_merge {F G : Finset (Finset L)} (hF : IsForest F)
    (hb : model_IsBinaryForest F) (hG : G ∈ merges F) : model_IsBinaryForest G := by
  obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hG
  intro C hC hC2
  rcases mem_insert.1 hC with rfl | hC
  · exact ⟨A, mem_insert_of_mem (roots_subset F hA), B, mem_insert_of_mem (roots_subset F hB),
      hF.disjoint_of_mem_roots hA hB hAB, rfl⟩
  · obtain ⟨D, hD, E, hE, hDE, hDEC⟩ := hb C hC hC2
    exact ⟨D, mem_insert_of_mem hD, E, mem_insert_of_mem hE, hDE, hDEC⟩

theorem model_isBinaryForest_of_jumpMatrix_pow {F G : Finset (Finset L)} (hF : IsForest F)
    (hb : model_IsBinaryForest F) {n : ℕ} (h : (jumpMatrix ^ n) F G ≠ 0) :
    model_IsBinaryForest G := by
  induction n generalizing F with
  | zero =>
    rw [pow_zero] at h
    by_cases hGF : G = F
    · exact hGF ▸ hb
    · exact absurd (Matrix.one_apply_ne (Ne.symm hGF)) h
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨F', -, hF'⟩ := exists_ne_zero_of_sum_ne_zero h
    have hJ := left_ne_zero_of_mul hF'
    have hJn := right_ne_zero_of_mul hF'
    by_cases hk : #(roots F) ≤ 1
    · have hF'F : F' = F := by
        by_contra hne
        exact hJ (by simp only [jumpMatrix, hk, hne, ↓reduceIte])
      subst hF'F
      exact ih hF hb hJn
    · have hmem : F' ∈ merges F := by
        by_contra hne
        exact hJ (by rw [jumpMatrix_apply_of_isForest (by omega), ite_eq_right hne])
      exact ih (hF.of_mem_merges hmem).1 (model_isBinaryForest_merge hF hb hmem) hJn

theorem model_isBinaryForest_of_populationKernel {len : Finset X → ℝ} {A : Finset X}
    {F G : Finset (Finset L)} (hF : IsForest F) (hb : model_IsBinaryForest F)
    (h : populationKernel len A F G ≠ 0) : model_IsBinaryForest G := by
  unfold populationKernel at h
  split_ifs at h with hA
  · rw [kingmanAbsorption_apply hF] at h
    split_ifs at h with h0 h1 h2
    · exact h1 ▸ hb
    · exact absurd rfl h
    · exact model_isBinaryForest_of_jumpMatrix_pow hF hb h
    · exact absurd rfl h
  · rw [kingmanTransition_apply hF] at h
    exact model_isBinaryForest_of_jumpMatrix_pow hF hb (right_ne_zero_of_mul h)

theorem model_isBinaryForest_of_forestDist {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (s : L → X) {A : Finset X} (hA : A ∈ H) {G : Finset (Finset L)}
    (hG : forestDist H len s A G ≠ 0) : model_IsBinaryForest G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist] at hG
  obtain ⟨f, -, hf⟩ := exists_ne_zero_of_sum_ne_zero hG
  have hprod := left_ne_zero_of_mul hf
  have hfB : ∀ B : childClusters H A,
      IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X)) := by
    intro B
    obtain ⟨h1, -, h3⟩ := forestDist_support hH len s (mem_childClusters.1 B.2).1
      (prod_ne_zero_iff.1 hprod B (mem_univ _))
    exact ⟨h1, h3⟩
  have hbB : ∀ B : childClusters H A, model_IsBinaryForest (f B) := fun B =>
    ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1
      (prod_ne_zero_iff.1 hprod B (mem_univ _))
  refine model_isBinaryForest_of_populationKernel (hH.isForest_entering f hfB).1 ?_
    (right_ne_zero_of_mul hf)
  intro C hC hC2
  rcases mem_union.1 hC with hC | hC
  · obtain ⟨B, -, hCB⟩ := mem_sup.1 hC
    obtain ⟨D, hD, E, hE, hDE, hDEC⟩ := hbB B C hCB hC2
    exact ⟨D, mem_union_left _ (mem_sup.2 ⟨B, mem_univ _, hD⟩),
      E, mem_union_left _ (mem_sup.2 ⟨B, mem_univ _, hE⟩), hDE, hDEC⟩
  · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hC
    simp at hC2

/-- Sections 1 and 5: with at least one lineage, a rooted gene tree with positive probability is a
binary hierarchy on the lineages. (With no lineage at all, the only gene tree is the empty forest,
which is not a hierarchy.) -/
theorem model_rootedDist_support [Nonempty L] (σ : SpeciesTree X) (s : L → X)
    {G : Finset (Finset L)} (hG : σ.rootedDist s G ≠ 0) :
    IsHierarchy G ∧ ∀ A ∈ G, 2 ≤ #A → ∃ B ∈ G, ∃ C ∈ G, Disjoint B C ∧ B ∪ C = A := by
  obtain ⟨h1, h2, h3, -⟩ := forestDist_univ_support σ.isHierarchy σ.length s hG
  have hsing : ∀ l : L, {l} ∈ G := fun l => h2 (singleton_mem_sampledForest.2 (mem_univ _))
  have hk : #(roots G) = 1 := by
    have := (roots_nonempty_iff.2 ⟨_, hsing (Classical.arbitrary L)⟩).card_pos
    have h4 := (forestDist_univ_support σ.isHierarchy σ.length s hG).2.2.2
    omega
  have huniv : (univ : Finset L) ∈ G := h3 ▸ lineages_mem_of_card_roots_eq_one hk
  exact ⟨⟨huniv, hsing, h1.1, h1.2⟩,
    model_isBinaryForest_of_forestDist σ.isHierarchy σ.length s σ.univ_mem hG⟩

end Binary

end ADR11
