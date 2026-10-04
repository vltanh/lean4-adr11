module

public import ADR11.MSC.Basic

/-!
# Relabelling taxa

Everything in the model is natural with respect to bijections of the taxa: relabelling a species
tree relabels its gene tree distributions.

* `relabelFamily e F`: the image of a family of clusters under a bijection `e : X ≃ Y`;
  `relabelFamilyEquiv e`: the same map, as an equivalence.
* `SpeciesTree.relabel σ e`: the species tree `σ` with taxa relabelled by `e`.

## Main results

* `kingmanGenerator_relabelFamily`, `kingmanTransition_relabelFamily`,
  `kingmanAbsorption_relabelFamily`: Kingman's coalescent is invariant under relabelling the
  lineages.
* `forestDist_relabel`: naturality of the multispecies coalescent under relabelling the taxa and
  the lineages; `forestDist_relabel_lineages`: relabelling the lineages only.
* `SpeciesTree.unrootedDist_relabel`, `SpeciesTree.rootedDist_relabel`: the gene tree
  distributions of the relabelled tree are the relabelled distributions.
* `SpeciesTree.sameRootedMetricTree_relabel_iff`, `SpeciesTree.sameUnrootedMetricTree_relabel_iff`:
  relabelling preserves and reflects equality of metric trees.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The image of a family of clusters under a bijection. -/
def relabelFamily (e : X ≃ Y) (F : Finset (Finset X)) : Finset (Finset Y) :=
  F.image fun A => A.map e.toEmbedding

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
private lemma msc_map_symm_map (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding).map e.symm.toEmbedding = A := by
  ext x
  simp

private lemma msc_map_compl (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding)ᶜ = Aᶜ.map e.toEmbedding := by
  ext y
  simp [Finset.mem_map_equiv]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
private lemma msc_map_map_symm (e : X ≃ Y) (B : Finset Y) :
    (B.map e.symm.toEmbedding).map e.toEmbedding = B := by
  ext x
  simp

omit [DecidableEq X] [DecidableEq Y] in
private lemma msc_map_eq_univ_iff (e : X ≃ Y) (A : Finset X) :
    A.map e.toEmbedding = univ ↔ A = univ := by
  rw [← Finset.map_univ_equiv e, Finset.map_inj]

omit [Fintype X] [DecidableEq X] [Fintype Y] in
theorem relabelFamily_injective (e : X ≃ Y) : Function.Injective (relabelFamily e) :=
  Finset.image_injective (Finset.map_injective e.toEmbedding)

omit [Fintype X] [Fintype Y] in
theorem relabelFamily_symm (e : X ≃ Y) (F : Finset (Finset X)) :
    relabelFamily e.symm (relabelFamily e F) = F := by
  unfold relabelFamily
  rw [image_image]
  conv_rhs => rw [← image_id (s := F)]
  congr 1
  funext A
  exact msc_map_symm_map e A

theorem unroot_relabelFamily (e : X ≃ Y) (F : Finset (Finset X)) :
    unroot (relabelFamily e F) = relabelFamily e (unroot F) := by
  have herase : (relabelFamily e F).erase univ = relabelFamily e (F.erase univ) := by
    unfold relabelFamily
    rw [Finset.image_erase (Finset.map_injective e.toEmbedding), Finset.map_univ_equiv]
  unfold unroot
  rw [herase]
  unfold relabelFamily
  rw [image_union, image_image, image_image]
  congr 2
  funext A
  exact msc_map_compl e A

/-- Relabelling families of clusters along `e`, as an equivalence. -/
def relabelFamilyEquiv (e : X ≃ Y) : Finset (Finset X) ≃ Finset (Finset Y) where
  toFun := relabelFamily e
  invFun := relabelFamily e.symm
  left_inv := relabelFamily_symm e
  right_inv := fun F => by simpa using relabelFamily_symm e.symm F

omit [Fintype X] [Fintype Y] in
@[simp] theorem relabelFamilyEquiv_apply (e : X ≃ Y) (F : Finset (Finset X)) :
    relabelFamilyEquiv e F = relabelFamily e F := rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] in
theorem mem_relabelFamily {e : X ≃ Y} {F : Finset (Finset X)} {B : Finset Y} :
    B ∈ relabelFamily e F ↔ B.map e.symm.toEmbedding ∈ F := by
  unfold relabelFamily
  rw [mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    rwa [msc_map_symm_map]
  · intro h
    refine ⟨_, h, ?_⟩
    ext y
    simp [Finset.mem_map_equiv]

omit [Fintype X] [DecidableEq X] [Fintype Y] in
theorem map_mem_relabelFamily {e : X ≃ Y} {F : Finset (Finset X)} {A : Finset X} :
    A.map e.toEmbedding ∈ relabelFamily e F ↔ A ∈ F := by
  rw [mem_relabelFamily, msc_map_symm_map]

omit [Fintype X] [Fintype Y] in
theorem relabelFamily_union (e : X ≃ Y) (F G : Finset (Finset X)) :
    relabelFamily e (F ∪ G) = relabelFamily e F ∪ relabelFamily e G :=
  image_union _ _


section Kernels

variable {L : Type*} [Fintype L] [DecidableEq L] {M : Type*} [Fintype M] [DecidableEq M]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem roots_relabelFamily (e : L ≃ M) (F : Finset (Finset L)) :
    roots (relabelFamily e F) = relabelFamily e (roots F) := by
  unfold roots relabelFamily
  rw [filter_image]
  congr 1
  refine filter_congr fun A _ => ?_
  rw [Finset.forall_mem_image]
  constructor
  · intro h B hB hAB
    exact Finset.map_injective _ (h hB (Finset.map_subset_map.2 hAB))
  · intro h B hB hAB
    rw [h B hB (Finset.map_subset_map.1 hAB)]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype L] [DecidableEq L]
  [Fintype M] in
theorem card_relabelFamily (e : L ≃ M) (F : Finset (Finset L)) :
    #(relabelFamily e F) = #F :=
  card_image_of_injective _ (Finset.map_injective e.toEmbedding)

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- The generator of Kingman's coalescent is invariant under relabelling the lineages. -/
theorem kingmanGenerator_relabelFamily (e : L ≃ M) (F G : Finset (Finset L)) :
    kingmanGenerator (relabelFamily e F) (relabelFamily e G) = kingmanGenerator F G := by
  unfold kingmanGenerator
  rw [roots_relabelFamily, card_relabelFamily]
  by_cases hGF : G = F
  · subst hGF
    simp
  · have hne : relabelFamily e G ≠ relabelFamily e F := fun h => hGF (relabelFamily_injective e h)
    rw [ite_eq_right hne, ite_eq_right hGF]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨A', hA', B', hB', hAB', hF⟩
      obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
      obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
      refine ⟨A, hA, B, hB, fun h => hAB' (h ▸ rfl), relabelFamily_injective e ?_⟩
      rw [hF]
      unfold relabelFamily
      rw [image_insert, Finset.map_union]
    · rintro ⟨A, hA, B, hB, hAB, rfl⟩
      refine ⟨A.map e.toEmbedding, mem_image_of_mem _ hA, B.map e.toEmbedding,
        mem_image_of_mem _ hB, fun h => hAB (Finset.map_injective _ h), ?_⟩
      unfold relabelFamily
      rw [image_insert, Finset.map_union]

/-- The matrix exponential commutes with reindexing along an equivalence. -/
private lemma msc_exp_submatrix {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (π : n ≃ m) (A : Matrix m m ℝ) :
    NormedSpace.exp (A.submatrix π π) = (NormedSpace.exp A).submatrix π π := by
  have hpow : ∀ k : ℕ, (A.submatrix π π) ^ k = (A ^ k).submatrix π π := by
    intro k
    induction k with
    | zero => simp [Matrix.submatrix_one_equiv]
    | succ k ih => rw [pow_succ, ih, Matrix.submatrix_mul_equiv, pow_succ]
  let g := Matrix.reindexLinearEquiv ℝ ℝ π.symm π.symm
  have hg : ∀ M : Matrix m m ℝ, g M = M.submatrix π π := fun M => rfl
  have hgc : Continuous g := by
    show Continuous fun M : Matrix m m ℝ => M.submatrix π π
    exact continuous_id.matrix_submatrix π π
  have hg'c : Continuous fun M : Matrix n n ℝ => M.submatrix π.symm π.symm :=
    continuous_id.matrix_submatrix π.symm π.symm
  have hinv : Function.LeftInverse (fun M : Matrix n n ℝ => M.submatrix π.symm π.symm) g := by
    intro M
    show (M.submatrix π π).submatrix π.symm π.symm = M
    rw [Matrix.submatrix_submatrix, π.self_comp_symm, Matrix.submatrix_id_id]
  have key := Function.LeftInverse.map_tsum (L := SummationFilter.unconditional ℕ)
    (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • A ^ k) hgc hg'c hinv
  simp only [hg] at key
  rw [NormedSpace.exp_eq_tsum ℝ, NormedSpace.exp_eq_tsum ℝ]
  dsimp only
  rw [key]
  congr 1
  funext k
  rw [Matrix.submatrix_smul, hpow]
  rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- Kingman's coalescent is invariant under relabelling the lineages. -/
theorem kingmanTransition_relabelFamily (e : L ≃ M) (t : ℝ) (F G : Finset (Finset L)) :
    kingmanTransition t (relabelFamily e F) (relabelFamily e G) = kingmanTransition t F G := by
  have hQ : (kingmanGenerator (L := M)).submatrix (relabelFamilyEquiv e) (relabelFamilyEquiv e) =
      kingmanGenerator (L := L) := by
    ext F G
    exact kingmanGenerator_relabelFamily e F G
  have hs : t • (kingmanGenerator (L := M)).submatrix (relabelFamilyEquiv e)
      (relabelFamilyEquiv e) = (t • kingmanGenerator (L := M)).submatrix (relabelFamilyEquiv e)
      (relabelFamilyEquiv e) := by
    ext F G
    rfl
  unfold kingmanTransition
  rw [← hQ, hs, msc_exp_submatrix]
  rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem kingmanAbsorption_relabelFamily (e : L ≃ M) (F G : Finset (Finset L)) :
    kingmanAbsorption (relabelFamily e F) (relabelFamily e G) = kingmanAbsorption F G := by
  unfold kingmanAbsorption
  simp_rw [kingmanTransition_relabelFamily]

end Kernels

section Naturality

variable {L : Type*} [Fintype L] [DecidableEq L] {M : Type*} [Fintype M] [DecidableEq M]

theorem childClusters_relabelFamily (e : X ≃ Y) (H : Finset (Finset X)) (A : Finset X) :
    childClusters (relabelFamily e H) (A.map e.toEmbedding) =
      relabelFamily e (childClusters H A) := by
  unfold childClusters relabelFamily
  rw [filter_image]
  congr 1
  refine filter_congr fun B _ => ?_
  simp only [Finset.map_ssubset_map, Finset.forall_mem_image]

omit [Fintype X] [Fintype Y] in
theorem sampledForest_relabel (e : X ≃ Y) (eL : L ≃ M) {s : L → X} {s' : M → Y}
    (hs : ∀ l, s' (eL l) = e (s l)) (A : Finset X) :
    sampledForest s' (A.map e.toEmbedding) = relabelFamily eL (sampledForest s A) := by
  ext C
  rw [mem_sampledForest, mem_relabelFamily, mem_sampledForest]
  constructor
  · rintro ⟨l', hl', rfl⟩
    refine ⟨eL.symm l', ?_, by simp⟩
    have := hs (eL.symm l')
    rw [eL.apply_symm_apply] at this
    rw [this, Finset.mem_map_equiv, e.symm_apply_apply] at hl'
    exact hl'
  · rintro ⟨l, hl, hC⟩
    refine ⟨eL l, ?_, ?_⟩
    · rw [hs]
      exact Finset.mem_map_of_mem _ hl
    · rw [← msc_map_map_symm eL C, ← hC]
      simp

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype L] [Fintype M] in
private lemma msc_relabelFamily_sup {ι : Type*} [Fintype ι] (eL : L ≃ M)
    (f : ι → Finset (Finset L)) :
    relabelFamily eL (univ.sup f) = univ.sup (fun i => relabelFamily eL (f i)) :=
  Finset.apply_sup_eq_sup_comp (relabelFamily eL) (fun F G => image_union F G) (image_empty _)

private lemma msc_sup_univ_equiv {ι κ α : Type*} [Fintype ι] [Fintype κ] [SemilatticeSup α]
    [OrderBot α] (ψ : ι ≃ κ) (g : κ → α) :
    univ.sup (fun i => g (ψ i)) = univ.sup g := by
  conv_rhs => rw [← Finset.map_univ_equiv ψ, Finset.sup_map]
  rfl

theorem populationKernel_relabel (e : X ≃ Y) (eL : L ≃ M)
    {len : Finset X → ℝ} {len' : Finset Y → ℝ} (hlen : ∀ A, len' (A.map e.toEmbedding) = len A)
    (A : Finset X) (F G : Finset (Finset L)) :
    populationKernel len' (A.map e.toEmbedding) (relabelFamily eL F) (relabelFamily eL G) =
      populationKernel len A F G := by
  unfold populationKernel
  by_cases hA : A = univ
  · rw [ite_eq_left ((msc_map_eq_univ_iff e A).2 hA), ite_eq_left hA]
    exact kingmanAbsorption_relabelFamily eL F G
  · rw [ite_eq_right (mt (msc_map_eq_univ_iff e A).1 hA), ite_eq_right hA, hlen]
    exact kingmanTransition_relabelFamily eL _ F G

/-- **Naturality of the multispecies coalescent.** Relabelling the taxa along `e` and the
lineages along `eL` (compatibly with the sampling maps) relabels the distribution of the forest
leaving each population. -/
theorem forestDist_relabel (e : X ≃ Y) (eL : L ≃ M) (H : Finset (Finset X))
    {len : Finset X → ℝ} {len' : Finset Y → ℝ} (hlen : ∀ A, len' (A.map e.toEmbedding) = len A)
    {s : L → X} {s' : M → Y} (hs : ∀ l, s' (eL l) = e (s l)) (A : Finset X)
    (G : Finset (Finset L)) :
    forestDist (relabelFamily e H) len' s' (A.map e.toEmbedding) (relabelFamily eL G) =
      forestDist H len s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist.eq_1 (relabelFamily e H), forestDist.eq_1 H]
  have hch := childClusters_relabelFamily e H A
  let ψ : childClusters H A ≃ childClusters (relabelFamily e H) (A.map e.toEmbedding) :=
    (Equiv.finsetCongr e).subtypeEquiv fun B => by
      rw [hch, Equiv.finsetCongr_apply, map_mem_relabelFamily]
  let Φ := ψ.arrowCongr (relabelFamilyEquiv eL)
  rw [← Φ.sum_comp]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hΦ : ∀ B : childClusters H A, Φ f (ψ B) = relabelFamily eL (f B) := fun B => by
    simp [Φ, Equiv.arrowCongr_apply]
  have hψ : ∀ B : childClusters H A,
      ((ψ B : childClusters (relabelFamily e H) (A.map e.toEmbedding)) : Finset Y) =
        (B : Finset X).map e.toEmbedding := fun B => rfl
  congr 1
  · rw [← ψ.prod_comp]
    refine Finset.prod_congr rfl fun B _ => ?_
    rw [hΦ, hψ]
    exact ih B (mem_childClusters.1 B.2).2.1 (f B)
  · have hsup : univ.sup (Φ f) = relabelFamily eL (univ.sup f) := by
      rw [msc_relabelFamily_sup, ← msc_sup_univ_equiv ψ]
      simp only [hΦ]
    rw [hsup, sampledForest_relabel e eL hs, ← relabelFamily_union]
    exact populationKernel_relabel e eL hlen A _ G

omit [Fintype X] in
theorem relabelFamily_refl (F : Finset (Finset X)) : relabelFamily (Equiv.refl X) F = F := by
  unfold relabelFamily
  conv_rhs => rw [← image_id (s := F)]
  congr 1
  funext A
  ext x
  simp

/-- Relabelling the lineages only. -/
theorem forestDist_relabel_lineages (eL : L ≃ M) (H : Finset (Finset X)) (len : Finset X → ℝ)
    (s : L → X) (A : Finset X) (G : Finset (Finset L)) :
    forestDist H len (s ∘ eL.symm) A (relabelFamily eL G) = forestDist H len s A G := by
  have hmap : ∀ B : Finset X, B.map (Equiv.refl X).toEmbedding = B := fun B => by
    ext x
    simp
  have := forestDist_relabel (Equiv.refl X) eL H (len := len) (len' := len)
    (fun B => by rw [hmap]) (s := s) (s' := s ∘ eL.symm) (fun l => by simp) A G
  rwa [relabelFamily_refl, hmap] at this

end Naturality

theorem SpeciesTree.relabel_univ_mem (σ : SpeciesTree X) (e : X ≃ Y) :
    (univ : Finset Y) ∈ relabelFamily e σ.clusters :=
  mem_image.2 ⟨univ, σ.univ_mem, Finset.map_univ_equiv e⟩

omit [Fintype Y] in
theorem SpeciesTree.relabel_singleton_mem (σ : SpeciesTree X) (e : X ≃ Y) (y : Y) :
    {y} ∈ relabelFamily e σ.clusters :=
  mem_image.2 ⟨{e.symm y}, σ.singleton_mem _, by simp⟩

omit [Fintype Y] in
theorem SpeciesTree.relabel_nonempty_of_mem (σ : SpeciesTree X) (e : X ≃ Y) :
    ∀ B ∈ relabelFamily e σ.clusters, B.Nonempty := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
  exact Finset.map_nonempty.2 (σ.nonempty_of_mem A hA)

omit [Fintype Y] in
theorem SpeciesTree.relabel_laminar (σ : SpeciesTree X) (e : X ≃ Y) :
    ∀ B ∈ relabelFamily e σ.clusters, ∀ C ∈ relabelFamily e σ.clusters,
      B ⊆ C ∨ C ⊆ B ∨ Disjoint B C := by
  intro B hB C hC
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
  obtain ⟨A', hA', rfl⟩ := mem_image.1 hC
  rw [Finset.map_subset_map, Finset.map_subset_map, Finset.disjoint_map]
  exact σ.laminar A hA A' hA'

theorem SpeciesTree.relabel_length_pos (σ : SpeciesTree X) (e : X ≃ Y) :
    ∀ B ∈ relabelFamily e σ.clusters, B ≠ univ → 0 < σ.length (B.map e.symm.toEmbedding) := by
  intro B hB hBu
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
  rw [msc_map_symm_map]
  exact σ.length_pos A hA fun h => hBu ((msc_map_eq_univ_iff e A).2 h)

/-- The species tree `σ` with its taxa relabelled by `e`. -/
def SpeciesTree.relabel (σ : SpeciesTree X) (e : X ≃ Y) : SpeciesTree Y where
  clusters := relabelFamily e σ.clusters
  univ_mem := σ.relabel_univ_mem e
  singleton_mem := σ.relabel_singleton_mem e
  nonempty_of_mem := σ.relabel_nonempty_of_mem e
  laminar := σ.relabel_laminar e
  length B := σ.length (B.map e.symm.toEmbedding)
  length_pos := σ.relabel_length_pos e

@[simp] theorem SpeciesTree.relabel_clusters (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).clusters = relabelFamily e σ.clusters := rfl

theorem SpeciesTree.relabel_length (σ : SpeciesTree X) (e : X ≃ Y) (B : Finset Y) :
    (σ.relabel e).length B = σ.length (B.map e.symm.toEmbedding) := rfl

@[simp] theorem SpeciesTree.relabel_length_map (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).length (A.map e.toEmbedding) = σ.length A := by
  rw [SpeciesTree.relabel_length, msc_map_symm_map]

private lemma msc_speciesTree_eq {σ σ' : SpeciesTree X} (h1 : σ.clusters = σ'.clusters)
    (h2 : σ.length = σ'.length) : σ = σ' := by
  cases σ
  cases σ'
  cases h1
  cases h2
  rfl

/-- Relabelling back along `e.symm` gives the original species tree. -/
theorem SpeciesTree.relabel_relabel_symm (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).relabel e.symm = σ := by
  refine msc_speciesTree_eq (relabelFamily_symm e σ.clusters) ?_
  funext A
  show σ.length ((A.map e.symm.symm.toEmbedding).map e.symm.toEmbedding) = σ.length A
  rw [Equiv.symm_symm, msc_map_symm_map]

private lemma msc_isBinary_relabel {σ : SpeciesTree X} (e : X ≃ Y) (h : σ.IsBinary) :
    (σ.relabel e).IsBinary := by
  intro B hB hB2
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
  rw [Finset.card_map] at hB2
  obtain ⟨C, hC, D, hD, hCD, hCDA⟩ := h A hA hB2
  refine ⟨C.map e.toEmbedding, mem_image_of_mem _ hC, D.map e.toEmbedding, mem_image_of_mem _ hD,
    (Finset.disjoint_map _).2 hCD, ?_⟩
  rw [← Finset.map_union, hCDA]

theorem SpeciesTree.isBinary_relabel_iff (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).IsBinary ↔ σ.IsBinary := by
  refine ⟨fun h => ?_, msc_isBinary_relabel e⟩
  have := msc_isBinary_relabel e.symm h
  rwa [SpeciesTree.relabel_relabel_symm] at this

theorem SpeciesTree.rootedDist_relabel (σ : SpeciesTree X) (e : X ≃ Y) (G : Finset (Finset X)) :
    (σ.relabel e).rootedDist id (relabelFamily e G) = σ.rootedDist id G := by
  unfold SpeciesTree.rootedDist
  have := forestDist_relabel e e σ.clusters (len := σ.length) (len' := (σ.relabel e).length)
    (σ.relabel_length_map e) (s := id) (s' := id) (fun _ => rfl) univ G
  rwa [Finset.map_univ_equiv] at this

theorem SpeciesTree.unrootedDist_relabel (σ : SpeciesTree X) (e : X ≃ Y)
    (T : Finset (Finset X)) :
    (σ.relabel e).unrootedDist id (relabelFamily e T) = σ.unrootedDist id T := by
  unfold SpeciesTree.unrootedDist
  rw [← (relabelFamilyEquiv e).sum_comp]
  refine Finset.sum_congr rfl fun G _ => ?_
  simp only [relabelFamilyEquiv_apply, unroot_relabelFamily, (relabelFamily_injective e).eq_iff,
    SpeciesTree.rootedDist_relabel]

theorem SpeciesTree.unrootedDist_relabel_eq_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).unrootedDist id = (σ'.relabel e).unrootedDist id ↔
      σ.unrootedDist id = σ'.unrootedDist id := by
  constructor
  · intro h
    funext T
    have := congrFun h (relabelFamily e T)
    rwa [SpeciesTree.unrootedDist_relabel, SpeciesTree.unrootedDist_relabel] at this
  · intro h
    funext T
    obtain ⟨T₀, rfl⟩ := (relabelFamilyEquiv e).surjective T
    rw [relabelFamilyEquiv_apply, SpeciesTree.unrootedDist_relabel,
      SpeciesTree.unrootedDist_relabel, h]

theorem SpeciesTree.sameRootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameRootedMetricTree (σ'.relabel e) ↔ σ.SameRootedMetricTree σ' := by
  unfold SpeciesTree.SameRootedMetricTree
  refine and_congr (relabelFamily_injective e).eq_iff ⟨fun h A hA hA2 hAu => ?_,
    fun h B hB hB2 hBu => ?_⟩
  · have := h (A.map e.toEmbedding) (map_mem_relabelFamily.2 hA) (by rwa [Finset.card_map])
      fun h' => hAu ((msc_map_eq_univ_iff e A).1 h')
    rwa [SpeciesTree.relabel_length_map, SpeciesTree.relabel_length_map] at this
  · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    rw [SpeciesTree.relabel_length_map, SpeciesTree.relabel_length_map]
    exact h A hA (by rwa [Finset.card_map] at hB2) fun h' => hBu ((msc_map_eq_univ_iff e A).2 h')

theorem SpeciesTree.unrootedLength_relabel (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).unrootedLength (A.map e.toEmbedding) = σ.unrootedLength A := by
  unfold SpeciesTree.unrootedLength
  rw [SpeciesTree.relabel_clusters]
  unfold relabelFamily
  rw [filter_image, sum_image fun x _ y _ h => Finset.map_injective _ h]
  refine Finset.sum_congr (filter_congr fun C _ => ?_) fun C _ =>
    SpeciesTree.relabel_length_map σ e C
  simp only [ne_eq, msc_map_eq_univ_iff, Finset.map_inj, msc_map_compl]

theorem SpeciesTree.sameUnrootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameUnrootedMetricTree (σ'.relabel e) ↔ σ.SameUnrootedMetricTree σ' := by
  unfold SpeciesTree.SameUnrootedMetricTree
  simp only [SpeciesTree.relabel_clusters, unroot_relabelFamily]
  refine and_congr (relabelFamily_injective e).eq_iff ⟨fun h A hA hA2 hAc2 => ?_,
    fun h B hB hB2 hBc2 => ?_⟩
  · have := h (A.map e.toEmbedding) (map_mem_relabelFamily.2 hA) (by rwa [Finset.card_map])
      (by rwa [msc_map_compl, Finset.card_map])
    rwa [SpeciesTree.unrootedLength_relabel, SpeciesTree.unrootedLength_relabel] at this
  · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    rw [SpeciesTree.unrootedLength_relabel, SpeciesTree.unrootedLength_relabel]
    exact h A hA (by rwa [Finset.card_map] at hB2) (by rwa [msc_map_compl, Finset.card_map] at hBc2)

end ADR11
