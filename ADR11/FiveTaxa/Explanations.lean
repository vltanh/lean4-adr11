module

public import ADR11.FiveTaxa.Lemma4
public import ADR11.Model
public import ADR11.Identifiability.Lemma5
public import ADR11.Identifiability.FourTaxaAnalysis
public import ADR11.Computation.FiveTaxa

/-!
# The explanations of the linear invariants of Tables 1–3 (Section 4.2)

The paper proves each invariant of Tables 1–3 by an "explanation" (l. 392–556); only the facts
that the invariants form a basis and that there are no others rest on the explicit formulas
(11)–(13) (l. 375). This module formalizes the explanations, for any species tree.

## Main results

* **Symmetry** (l. 394–397): `ex_unrootedDist_eq_of_symmetry`: if relabelling the taxa by a
  permutation `π` leaves the rooted metric species tree `σ⁺` unchanged (the same clusters and the
  same lengths of internal edges), every gene tree has the probability of its image under `π`;
  `ex_u_eq_of_perm`: the same on five taxa, for a permutation that maps the clusters of `σ` to
  clusters of `σ` and fixes every internal cluster.
* **Above the root** (l. 399–403): `ex_unrootedDist_aboveRoot`: a gene tree none of whose split
  sides with at least two taxa lies inside a cluster of `σ` other than the root can only be
  realized if all coalescent events occur above the root; its probability is the probability
  that no event occurs below the root times the probability of the gene tree from the uncoalesced
  lineages. On five taxa the latter is `1/15` by Lemma 4 (`ex_u_aboveRoot`), so all such gene
  trees are equiprobable (`ex_u_eq_aboveRoot`).
* **Near the root** (l. 466–471 for the caterpillar, l. 517–518 for the pseudocaterpillar):
  `ex_unrootedDist_nearRoot`: if the children of the root are `N` and `{o}`, a gene tree none of
  whose split sides with at least two taxa lies inside a cluster strictly inside `N` can only be
  realized if the lineages enter the near-the-root population above `N` uncoalesced, and then
  only events in that population and above the root matter; `ex_unrootedDist_eq_nearRoot`,
  `ex_u_eq_nearRoot`: two such gene trees that correspond under a permutation of the lineages
  entering the near-the-root population (fixing the outgroup `o`) are equiprobable.
* **Marginalization** (l. 495–501): `ex_lemma5_T5`: Lemma 5 on five taxa, as a sum over the
  fifteen gene trees `T_i`.

The supporting facts on the coalescent: `ex_exists_of_enteringDist_ne_zero` (a forest entering a
population that is not the forest of the uncoalesced lineages contains a cluster of at least two
lineages, formed in a population below), `ex_unrootedOutcome_eq_zero` (a forest with a cluster
that is not a split side of `T` cannot produce `T` above the root, since the coalescent only adds
clusters), `ex_unrootedOutcome_relabelFamily` (relabelling the lineages does not change the
probabilities above the root). On five taxa, the paper checks that no event can occur below a
population on the cherries of the gene tree, which its first coalescent event joins:
`ex_T5_cherry_subset` (every split side with at least two taxa contains a cherry) and
`ex_T5_noSide` turn this into the condition on all split sides.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Supporting facts on the coalescent -/

/-- Relabelling the lineages does not change the probability that the population above the root
produces a given unrooted gene tree. -/
theorem ex_unrootedOutcome_relabelFamily {L M : Type*} [Fintype L] [DecidableEq L] [Fintype M]
    [DecidableEq M] (e : L ≃ M) (F T : Finset (Finset L)) :
    unrootedOutcome (relabelFamily e F) (relabelFamily e T) = unrootedOutcome F T := by
  unfold unrootedOutcome
  rw [← (relabelFamilyEquiv e).sum_comp]
  refine sum_congr rfl fun G _ => ?_
  rw [relabelFamilyEquiv_apply, unroot_relabelFamily, kingmanAbsorption_relabelFamily]
  exact if_congr (relabelFamily_injective e).eq_iff rfl rfl

/-- A forest containing a cluster `C ≠ univ` that is not a side of a split of `T` cannot produce
`T` above the root: the coalescent only adds clusters, so `C` is a cluster of the gene tree. -/
theorem ex_unrootedOutcome_eq_zero {L : Type*} [Fintype L] [DecidableEq L]
    {F T : Finset (Finset L)} (hF : IsForest F) {C : Finset L} (hC : C ∈ F) (hCu : C ≠ univ)
    (hCT : C ∉ T) : unrootedOutcome F T = 0 := by
  unfold unrootedOutcome
  refine sum_eq_zero fun G _ => ?_
  split_ifs with hG
  · by_contra hne
    have hK : populationKernel (X := L) (fun _ => (0 : ℝ)) univ F G ≠ 0 := by
      rwa [populationKernel, ite_eq_left rfl]
    obtain ⟨-, hFG, -⟩ := populationKernel_support hF hK
    exact hCT (hG ▸ absorb_mem_unroot.2 (Or.inl ⟨hFG hC, hCu⟩))
  · rfl

/-- The forest entering the population above `A` (one lineage per taxon), when it is not the
forest of the uncoalesced lineages of `A`, contains a cluster of at least two lineages inside a
cluster of the species tree strictly inside `A`: a coalescent event occurred below `A`. -/
theorem ex_exists_of_enteringDist_ne_zero {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {A : Finset X} {F : Finset (Finset X)}
    (hF : enteringDist H len id A F ≠ 0) (hne : F ≠ sampledForest id A) :
    ∃ C ∈ F, 2 ≤ #C ∧ ∃ B ∈ H, B ⊂ A ∧ C ⊆ B := by
  obtain ⟨hFf, hSF, -⟩ := enteringDist_support hH len id hF
  obtain ⟨C, hCF, hCS⟩ : ∃ C ∈ F, C ∉ sampledForest id A := by
    by_contra h
    push Not at h
    exact hne (Subset.antisymm h hSF)
  unfold enteringDist at hF
  obtain ⟨f, -, hf⟩ := exists_ne_zero_of_sum_ne_zero hF
  split_ifs at hf with hfF
  swap
  · exact absurd rfl hf
  have hCF' := hCF
  rw [← hfF] at hCF'
  rcases mem_union.1 hCF' with hC | hC
  · obtain ⟨B, -, hCB⟩ := mem_sup.1 hC
    have hB := mem_childClusters.1 B.2
    obtain ⟨-, -, hlin⟩ :=
      forestDist_support hH len id hB.1 (prod_ne_zero_iff.1 hf B (mem_univ _))
    have hCsub : C ⊆ (B : Finset X) := by
      intro x hx
      have hx' : x ∈ lineages (f B) := mem_lineages.2 ⟨C, hCB, hx⟩
      rw [hlin, mem_filter] at hx'
      exact hx'.2
    refine ⟨C, hCF, ?_, B, hB.1, hB.2.1, hCsub⟩
    obtain ⟨x, hx⟩ := hFf.1 C hCF
    by_contra h2
    have hC1 : C = {x} :=
      eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => card_le_one.1 (by omega) y hy x hx⟩
    apply hCS
    rw [hC1, singleton_mem_sampledForest]
    exact hB.2.1.subset (hCsub hx)
  · exact absurd hC hCS

/-! ### Cherries of the five-taxon gene trees -/

/-- Every side of a split of a 5-taxon gene tree `T_i` with at least two taxa contains a cherry
of `T_i` (a side with two taxa). -/
theorem ex_T5_cherry_subset :
    ∀ i ∈ Icc 1 15, ∀ A ∈ T5 i, 2 ≤ #A → ∃ P ∈ T5 i, #P = 2 ∧ P ⊆ A := by
  decide

/-- If no cherry of `T_i` lies inside a set of taxa `B`, no side of a split of `T_i` with at least
two taxa does: the first coalescent event among the lineages of such a side joins the two
lineages of a cherry inside it. -/
theorem ex_T5_noSide {i : ℕ} (hi : i ∈ Icc 1 15) {B : Finset (Fin 5)}
    (h : ∀ P ∈ T5 i, #P = 2 → ¬ P ⊆ B) : ∀ A ∈ T5 i, A ⊆ B → #A ≤ 1 := by
  intro A hA hAB
  by_contra h2
  obtain ⟨P, hP, hP2, hPA⟩ := ex_T5_cherry_subset i hi A hA (by omega)
  exact h P hP hP2 (hPA.trans hAB)

/-! ### Symmetry -/

/-- **Symmetry** (Section 4.2.1). If relabelling the taxa by `π` leaves the rooted metric species
tree `σ⁺` unchanged (the same clusters and the same lengths of internal edges), the gene tree
distribution is invariant under `π`: every gene tree has the probability of its image. -/
theorem ex_unrootedDist_eq_of_symmetry (σ : SpeciesTree X) (π : Equiv.Perm X)
    (hπ : (σ.relabel π).SameRootedMetricTree σ) (T : Finset (Finset X)) :
    σ.unrootedDist id (relabelFamily π T) = σ.unrootedDist id T := by
  rw [← σ.unrootedDist_relabel π T]
  unfold SpeciesTree.unrootedDist
  rw [rootedDist_eq_of_sameRootedMetricTree hπ]

/-- **Symmetry** on five taxa (Section 4.2.1). A permutation `π` of the taxa that maps the clusters
`H` of `σ` onto themselves and fixes every internal cluster is a symmetry of `σ⁺`, so
`ℙ(T_i) = ℙ(T_j)` when `π` maps `T_i` to `T_j`. -/
theorem ex_u_eq_of_perm (σ : SpeciesTree (Fin 5)) {H : Finset (Finset (Fin 5))}
    (hσ : σ.clusters = H) (π : Equiv.Perm (Fin 5)) (hH : relabelFamily π H = H)
    (hfix : ∀ A ∈ H, 2 ≤ #A → A ≠ univ → A.map π.symm.toEmbedding = A) {i j : ℕ}
    (hij : relabelFamily π (T5 i) = T5 j) : u σ i = u σ j := by
  have hsym : (σ.relabel π).SameRootedMetricTree σ := by
    refine ⟨by rw [SpeciesTree.relabel_clusters, hσ, hH], fun A hA hA2 hAu => ?_⟩
    rw [SpeciesTree.relabel_clusters, hσ, hH] at hA
    rw [SpeciesTree.relabel_length, hfix A hA hA2 hAu]
  unfold u
  rw [← hij, ex_unrootedDist_eq_of_symmetry σ π hsym]

/-! ### Above the root -/

/-- **Above the root** (Section 4.2.1). If no side of a split of `T` with at least two taxa lies
inside a cluster of `σ` other than the root, `T` can only be realized when all coalescent events
occur above the root (an event below the root would form a clade of the gene tree inside such a
cluster): its probability is the probability that the lineages enter the population above the root
uncoalesced, times the probability that this population produces `T` from them. -/
theorem ex_unrootedDist_aboveRoot (σ : SpeciesTree X) {T : Finset (Finset X)}
    (hT : ∀ B ∈ σ.clusters, B ≠ univ → ∀ A ∈ T, A ⊆ B → #A ≤ 1) :
    σ.unrootedDist id T = enteringDist σ.clusters σ.length id univ (sampledForest id univ) *
      unrootedOutcome (sampledForest id univ) T := by
  rw [σ.unrootedDist_eq_unrootedDistOf, unrootedDistOf_eq_sum_entering]
  refine Fintype.sum_eq_single _ fun F hF => ?_
  by_cases hE : enteringDist σ.clusters σ.length id univ F = 0
  · rw [hE, zero_mul]
  -- a coalescent event below the root would create a cluster that is not a split side of `T`
  obtain ⟨C, hCF, hC2, B, hB, hBu, hCB⟩ :=
    ex_exists_of_enteringDist_ne_zero σ.isHierarchy σ.length hE hF
  have hFf := (enteringDist_support σ.isHierarchy σ.length id hE).1
  have hCu : C ≠ univ := by
    rintro rfl
    exact hBu.ne (univ_subset_iff.1 hCB)
  have hCT : C ∉ T := fun h => absurd (hT B hB hBu.ne C h hCB) (by omega)
  rw [ex_unrootedOutcome_eq_zero hFf hCF hCu hCT, mul_zero]

/-- **Above the root** (Section 4.2.1), with **Lemma 4**. On five taxa, let no cherry of the gene
tree `T_i` lie inside a cluster of `σ` other than the root. The first coalescent event of any
realization of `T_i` joins the two lineages of a cherry, so it can only occur above the root, and
all events occur above the root: `ℙ(T_i) = ℙ(no event below the root) · 1/15`. -/
theorem ex_u_aboveRoot (σ : SpeciesTree (Fin 5)) {i : ℕ} (hi : i ∈ Icc 1 15)
    (hT : ∀ B ∈ σ.clusters, B ≠ univ → ∀ P ∈ T5 i, #P = 2 → ¬ P ⊆ B) :
    u σ i = enteringDist σ.clusters σ.length id univ (singletonForest 5) * (1 / 15) := by
  have hS : sampledForest (id : Fin 5 → Fin 5) univ = singletonForest 5 := by
    rw [sampledForest_id]
    rfl
  rw [u, ex_unrootedDist_aboveRoot σ fun B hB hBu => ex_T5_noSide hi (hT B hB hBu), hS]
  congr 1
  exact lemma4 i hi

/-- **Above the root** (Section 4.2.1): two gene trees that can only be realized if all coalescent
events occur above the root (none of their cherries lies inside a cluster of `σ` other than the
root) are equiprobable, by Lemma 4. -/
theorem ex_u_eq_aboveRoot (σ : SpeciesTree (Fin 5)) {i j : ℕ} (hi : i ∈ Icc 1 15)
    (hj : j ∈ Icc 1 15) (hTi : ∀ B ∈ σ.clusters, B ≠ univ → ∀ P ∈ T5 i, #P = 2 → ¬ P ⊆ B)
    (hTj : ∀ B ∈ σ.clusters, B ≠ univ → ∀ P ∈ T5 j, #P = 2 → ¬ P ⊆ B) : u σ i = u σ j := by
  rw [ex_u_aboveRoot σ hi hTi, ex_u_aboveRoot σ hj hTj]

/-! ### Near the root -/

/-- **Near the root** (Section 4.2.2). Let the children of the root be `N` and `{o}`. If no side
of a split of `T` with at least two taxa lies inside a cluster of `σ` strictly inside `N`, `T` can
only be realized when the lineages enter the near-the-root population above `N` uncoalesced (an
event below `N` would form a clade of the gene tree inside such a cluster): its probability is the
probability of that event times the probability that the population above `N` (for the time
`σ.length N`) and then the population above the root, with the lineage sampled from `o`,
produce `T`. -/
theorem ex_unrootedDist_nearRoot (σ : SpeciesTree X) {N : Finset X} {o : X}
    (hch : childClusters σ.clusters univ = {N, {o}}) (hNo : N ≠ {o}) {T : Finset (Finset X)}
    (hT : ∀ B ∈ σ.clusters, B ⊂ N → ∀ A ∈ T, A ⊆ B → #A ≤ 1) :
    σ.unrootedDist id T = enteringDist σ.clusters σ.length id N (sampledForest id N) *
      ∑ F, kingmanTransition (σ.length N) (sampledForest id N) F *
        unrootedOutcome (F ∪ sampledForest id univ) T := by
  have hH := σ.isHierarchy
  have hNu : N ≠ univ := by
    have hN : N ∈ childClusters σ.clusters univ := by
      rw [hch]
      exact mem_insert_self _ _
    exact (mem_childClusters.1 hN).2.1.ne
  -- the forest leaving the root: the lineage sampled from `o` joins the forest leaving `N`
  have hroot : ∀ G, forestDist σ.clusters σ.length id univ G =
      ∑ F, forestDist σ.clusters σ.length id N F *
        kingmanAbsorption (F ∪ sampledForest id univ) G := by
    intro G
    rw [forestDist_of_childClusters_eq_pair hch hNo]
    refine sum_congr rfl fun F _ => ?_
    rw [Fintype.sum_eq_single {{o}} fun F₂ hF₂ => by
      rw [forestDist_id_singleton hH, ite_eq_right hF₂, mul_zero, zero_mul]]
    rw [forestDist_id_singleton hH, ite_eq_left rfl, mul_one, populationKernel, ite_eq_left rfl,
      union_assoc, union_eq_right.2 (singleton_subset_iff.2
        (singleton_mem_sampledForest.2 (mem_univ o)))]
  -- the forest leaving `N`: the forest entering `N`, through the population above `N`
  have hN : ∀ F, forestDist σ.clusters σ.length id N F =
      ∑ F', enteringDist σ.clusters σ.length id N F' * kingmanTransition (σ.length N) F' F := by
    intro F
    rw [forestDist_eq_sum_entering]
    simp only [populationKernel, ite_eq_right hNu]
  have hu : σ.unrootedDist id T = ∑ F, forestDist σ.clusters σ.length id N F *
      unrootedOutcome (F ∪ sampledForest id univ) T := by
    unfold SpeciesTree.unrootedDist SpeciesTree.rootedDist unrootedOutcome
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun G _ => ?_
    rw [hroot]
    split_ifs <;> simp
  -- a coalescent event below `N` would create a cluster that is not a split side of `T`
  have hzero : ∀ F' ≠ sampledForest id N, ∑ F, enteringDist σ.clusters σ.length id N F' *
      kingmanTransition (σ.length N) F' F * unrootedOutcome (F ∪ sampledForest id univ) T = 0 := by
    intro F' hF'
    by_cases hE : enteringDist σ.clusters σ.length id N F' = 0
    · simp [hE]
    obtain ⟨C, hCF, hC2, B, hB, hBN, hCB⟩ := ex_exists_of_enteringDist_ne_zero hH σ.length hE hF'
    have hF'f := (enteringDist_support hH σ.length id hE).1
    have hCu : C ≠ univ := by
      rintro rfl
      exact hNu (univ_subset_iff.1 (hCB.trans hBN.subset))
    have hCT : C ∉ T := fun h => absurd (hT B hB hBN C h hCB) (by omega)
    refine sum_eq_zero fun F _ => ?_
    by_cases hK : kingmanTransition (σ.length N) F' F = 0
    · rw [hK, mul_zero, zero_mul]
    obtain ⟨hFf, hF'F, -⟩ := kingmanTransition_support hF'f hK
    have hFS : IsForest (F ∪ sampledForest id univ) := hFf.union_image_singleton _
    rw [ex_unrootedOutcome_eq_zero hFS (mem_union_left _ (hF'F hCF)) hCu hCT, mul_zero]
  rw [hu]
  simp_rw [hN, sum_mul]
  rw [sum_comm, Fintype.sum_eq_single _ hzero, mul_sum]
  exact sum_congr rfl fun F _ => mul_assoc _ _ _

/-- **Near the root** (Sections 4.2.2 and 4.2.3). Let the children of the root be `{o}ᶜ` and `{o}`
(`o` is the outgroup), and let `T`, `T'` be gene trees that can only be realized when the lineages
enter the near-the-root population above `{o}ᶜ` uncoalesced. If a permutation `π` of the lineages
entering that population (fixing `o`) maps `T` to `T'`, then the coalescent events in that
population and above the root that realize `T` correspond under `π` to equally likely events
realizing `T'`: `T` and `T'` are equiprobable. -/
theorem ex_unrootedDist_eq_nearRoot (σ : SpeciesTree X) {o : X}
    (hch : childClusters σ.clusters univ = {{o}ᶜ, {o}}) (π : Equiv.Perm X) (hπ : π o = o)
    {T T' : Finset (Finset X)} (hTT' : relabelFamily π T = T')
    (hT : ∀ B ∈ σ.clusters, B ⊂ {o}ᶜ → ∀ A ∈ T, A ⊆ B → #A ≤ 1)
    (hT' : ∀ B ∈ σ.clusters, B ⊂ {o}ᶜ → ∀ A ∈ T', A ⊆ B → #A ≤ 1) :
    σ.unrootedDist id T = σ.unrootedDist id T' := by
  have hNo : ({o}ᶜ : Finset X) ≠ {o} := fun h => by
    have h' : o ∈ ({o}ᶜ : Finset X) := by
      rw [h]
      exact mem_singleton_self o
    exact (mem_compl.1 h') (mem_singleton_self o)
  rw [ex_unrootedDist_nearRoot σ hch hNo hT, ex_unrootedDist_nearRoot σ hch hNo hT']
  congr 1
  -- `π` fixes the forests of the uncoalesced lineages entering `{o}ᶜ` and the root
  have hmap : ({o}ᶜ : Finset X).map π.toEmbedding = {o}ᶜ := by
    ext x
    rw [mem_map_equiv, mem_compl, mem_compl, mem_singleton, mem_singleton, Equiv.symm_apply_eq, hπ]
  have hπN : relabelFamily π (sampledForest id ({o}ᶜ : Finset X)) = sampledForest id {o}ᶜ := by
    rw [← sampledForest_relabel π π (s := id) (s' := id) (fun _ => rfl), hmap]
  have hπS : relabelFamily π (sampledForest id (univ : Finset X)) = sampledForest id univ := by
    rw [← sampledForest_relabel π π (s := id) (s' := id) (fun _ => rfl), map_univ_equiv]
  refine Fintype.sum_equiv (relabelFamilyEquiv π) _ _ fun F => ?_
  rw [relabelFamilyEquiv_apply]
  congr 1
  · conv_rhs => rw [← hπN]
    exact (kingmanTransition_relabelFamily π _ _ _).symm
  · rw [← hTT', ← ex_unrootedOutcome_relabelFamily π (F ∪ sampledForest id univ) T,
      relabelFamily_union, hπS]

/-- **Near the root** (Sections 4.2.2 and 4.2.3), for gene trees `T_i`, `T_j` on five taxa. Let
the children of the root be `{o}ᶜ` and `{o}`, and let no cherry of `T_i` or of `T_j` lie inside a
cluster of `σ` strictly inside `{o}ᶜ`: their first coalescent events, which join the lineages of a
cherry, cannot occur below the near-the-root population, so no event does. If a permutation `π` of
the lineages entering that population (fixing `o`) maps `T_i` to `T_j`, then `u_i = u_j`. -/
theorem ex_u_eq_nearRoot (σ : SpeciesTree (Fin 5)) {o : Fin 5}
    (hch : childClusters σ.clusters univ = {{o}ᶜ, {o}}) (π : Equiv.Perm (Fin 5)) (hπ : π o = o)
    {i j : ℕ} (hi : i ∈ Icc 1 15) (hj : j ∈ Icc 1 15) (hij : relabelFamily π (T5 i) = T5 j)
    (hTi : ∀ B ∈ σ.clusters, B ⊂ {o}ᶜ → ∀ P ∈ T5 i, #P = 2 → ¬ P ⊆ B)
    (hTj : ∀ B ∈ σ.clusters, B ⊂ {o}ᶜ → ∀ P ∈ T5 j, #P = 2 → ¬ P ⊆ B) : u σ i = u σ j :=
  ex_unrootedDist_eq_nearRoot σ hch π hπ hij (fun B hB hBN => ex_T5_noSide hi (hTi B hB hBN))
    fun B hB hBN => ex_T5_noSide hj (hTj B hB hBN)

/-! ### Marginalization -/

/-- **Lemma 5** on five taxa, as a sum over the fifteen gene trees `T_i` (every other unrooted tree
has probability `0`): `ℙ_{σ⁺(S)}(T') = ∑_{T_i(S) = T'} ℙ_{σ⁺}(T_i)`. -/
theorem ex_lemma5_T5 (σ : SpeciesTree (Fin 5)) (S : Finset (Fin 5)) (hS : S.Nonempty)
    (T' : Finset (Finset S)) :
    (σ.restrict S hS).unrootedDist id T' =
      ∑ i ∈ Icc 1 15, if restrictSplits S (T5 i) = T' then u σ i else 0 := by
  have hz : ∀ T ∈ (univ : Finset (Finset (Finset (Fin 5)))), T ∉ (Icc 1 15).image T5 →
      (if restrictSplits S T = T' then σ.unrootedDist id T else 0) = 0 := by
    intro T _ hT
    rw [unrootedDist_eq_zero_five σ T fun i hi h => hT (mem_image.2 ⟨i, hi, h.symm⟩), ite_self]
  rw [lemma5 σ S hS T', ← sum_subset (subset_univ ((Icc 1 15).image T5)) hz,
    sum_image fun i hi j hj h => Computation.T5_inj hi hj h]
  rfl

end ADR11
