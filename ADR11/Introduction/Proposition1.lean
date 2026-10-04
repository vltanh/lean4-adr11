module

public import ADR11.Introduction
public import ADR11.Identifiability.Lemma5
public import ADR11.Trees.Hierarchy
public import ADR11.MSC.Relabel

/-!
# Proposition 1 and Corollary 2: rooted triples

* `proposition1`: for a species tree with `n ≥ 3` taxa, the probabilities of rooted triple gene
  tree topologies determine the species tree topology and internal branch lengths.
* `corollary2`: so does the distribution of rooted gene trees.

By Lemma 5 (rooted version), the probability of the rooted triple `ab|c` is that of the rooted
gene tree `((A,B),C)` under the induced species tree on `{a, b, c}`; by equation (1) it exceeds
`1/3` exactly when the species tree has a cluster containing `a` and `b` but not `c`, and then
determines the length of the corresponding edge, `t = -log((3/2)(1 - p))`. Rooted triples determine
the clusters (`SpeciesTree.mem_clusters_of_triples`) and suitable triples isolate each internal
edge.

## Helper results

* `triple_rootedTripleProb_comm`, `triple_rootedTripleProb_relabel`,
  `triple_rootedTripleProb_restrict`: the probability of `ab|c` is symmetric in `a, b`, natural
  under relabelling, and unchanged by passing to an induced species tree containing `a, b, c`.
* `triple_isHierarchy_of_rootedDist_ne_zero`: rooted gene trees with positive probability are
  hierarchies.
* `triple_fin3_eq_hierarchyOf_pair`, `triple_fin3_rootedTripleProb`: on `Fin 3`, a hierarchy with
  the cluster `{i, j}` is the tree with cherry `{i, j}`, so `ℙ(ij|k)` is the probability of that
  rooted gene tree.
* `triple_exists_fin3`: the three rooted triples on distinct taxa `a, b, c` have the probabilities
  of the three rooted gene trees under a species tree on `Fin 3` (the induced tree on `{a, b, c}`,
  relabelled), whose 2-element clusters and edge lengths are read off the clusters of `σ`.
* `triple_rootedTripleProb_of_resolved`: if a cluster contains `a, b` but not `c`, then
  `ℙ(ab|c) = 1 - (2/3) e^{-t}` and `ℙ(ac|b) = ℙ(bc|a) = (1/3) e^{-t}`, where `t > 0`
  (`triple_length_pos`) is the sum of the lengths of the clusters containing `a, b` but not `c`;
  hence `triple_one_third_lt_of_resolved`, `triple_lt_one_third_of_resolved_left`,
  `triple_lt_one_third_of_resolved_right`.
* `triple_resolved_or_of_isBinary`, `triple_resolved_iff_of_isBinary`: a binary species tree
  resolves every triple of distinct taxa, so it displays `ab|c` exactly when `ℙ(ab|c) > 1/3`.
* `triple_sameRootedMetricTree`: two species trees with the same rooted triple probabilities,
  in which a triple `ab|c` is displayed exactly when its probability exceeds `1/3`, have the same
  rooted metric tree. This gives Proposition 1 here and its nonbinary version in Section 5
  (`ADR11.Nonbinary.Triples`).
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Rooted triple probabilities under relabelling and restriction -/

/-- The probability of the rooted triple `ab|c` is symmetric in `a` and `b`. -/
theorem triple_rootedTripleProb_comm (σ : SpeciesTree X) (a b c : X) :
    σ.rootedTripleProb a b c = σ.rootedTripleProb b a c := by
  unfold SpeciesTree.rootedTripleProb
  refine Finset.sum_congr rfl fun G _ => if_congr ?_ rfl rfl
  constructor <;> rintro ⟨C, hC, h1, h2, h3⟩ <;> exact ⟨C, hC, h2, h1, h3⟩

/-- Relabelling the taxa relabels the rooted triple probabilities. -/
theorem triple_rootedTripleProb_relabel {Y : Type*} [Fintype Y] [DecidableEq Y]
    (σ : SpeciesTree X) (e : X ≃ Y) (a b c : X) :
    (σ.relabel e).rootedTripleProb (e a) (e b) (e c) = σ.rootedTripleProb a b c := by
  unfold SpeciesTree.rootedTripleProb
  rw [← (relabelFamilyEquiv e).sum_comp]
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [relabelFamilyEquiv_apply, SpeciesTree.rootedDist_relabel]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨C, hC, ha, hb, hc⟩
    rw [mem_relabelFamily] at hC
    refine ⟨C.map e.symm.toEmbedding, hC, ?_, ?_, ?_⟩
    · rw [Finset.mem_map_equiv, Equiv.symm_symm]
      exact ha
    · rw [Finset.mem_map_equiv, Equiv.symm_symm]
      exact hb
    · rw [Finset.mem_map_equiv, Equiv.symm_symm]
      exact hc
  · rintro ⟨A, hA, ha, hb, hc⟩
    refine ⟨A.map e.toEmbedding, map_mem_relabelFamily.2 hA, ?_, ?_, ?_⟩
    · rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact ha
    · rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hb
    · rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hc

/-- The rooted triple probabilities of an induced species tree are those of the species tree
(by Lemma 5, rooted version). -/
theorem triple_rootedTripleProb_restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty)
    (a b c : S) :
    (σ.restrict S hS).rootedTripleProb a b c = σ.rootedTripleProb a b c := by
  have key : ∀ G : Finset (Finset X), (∃ C ∈ restrictClusters S G, a ∈ C ∧ b ∈ C ∧ c ∉ C) ↔
      ∃ C ∈ G, (a : X) ∈ C ∧ (b : X) ∈ C ∧ (c : X) ∉ C := by
    intro G
    constructor
    · rintro ⟨C, hC, ha, hb, hc⟩
      obtain ⟨A, hA, -, rfl⟩ := mem_restrictClusters.1 hC
      exact ⟨A, hA, mem_subtype.1 ha, mem_subtype.1 hb, fun h => hc (mem_subtype.2 h)⟩
    · rintro ⟨A, hA, ha, hb, hc⟩
      exact ⟨A.subtype (· ∈ S), subtype_mem_restrictClusters hA ⟨a, mem_inter.2 ⟨ha, a.2⟩⟩,
        mem_subtype.2 ha, mem_subtype.2 hb, fun h => hc (mem_subtype.1 h)⟩
  unfold SpeciesTree.rootedTripleProb
  simp_rw [lemma5_rooted σ S hS]
  calc ∑ G' : Finset (Finset S), (if ∃ C ∈ G', a ∈ C ∧ b ∈ C ∧ c ∉ C then
          ∑ G : Finset (Finset X), (if restrictClusters S G = G' then σ.rootedDist id G else 0)
          else 0)
      = ∑ G' : Finset (Finset S), ∑ G : Finset (Finset X), (if restrictClusters S G = G' then
          (if ∃ C ∈ G', a ∈ C ∧ b ∈ C ∧ c ∉ C then σ.rootedDist id G else 0) else 0) := by
        refine Finset.sum_congr rfl fun G' _ => ?_
        split_ifs with h
        · rfl
        · simp
    _ = ∑ G : Finset (Finset X), ∑ G' : Finset (Finset S), (if restrictClusters S G = G' then
          (if ∃ C ∈ G', a ∈ C ∧ b ∈ C ∧ c ∉ C then σ.rootedDist id G else 0) else 0) :=
        Finset.sum_comm
    _ = ∑ G : Finset (Finset X), (if ∃ C ∈ G, (a : X) ∈ C ∧ (b : X) ∈ C ∧ (c : X) ∉ C then
          σ.rootedDist id G else 0) := by
        refine Finset.sum_congr rfl fun G _ => ?_
        rw [Finset.sum_ite_eq, ite_eq_left (mem_univ _)]
        exact if_congr (key G) rfl rfl

/-! ### Rooted gene trees with positive probability -/

/-- A rooted gene tree with positive probability (one lineage per taxon) is a hierarchy. -/
theorem triple_isHierarchy_of_rootedDist_ne_zero [Nonempty X] (σ : SpeciesTree X)
    {G : Finset (Finset X)} (hG : σ.rootedDist id G ≠ 0) : IsHierarchy G := by
  obtain ⟨h1, h2, h3, h4⟩ := forestDist_univ_support σ.isHierarchy σ.length id hG
  have hsing : ∀ l : X, {l} ∈ G := fun l => h2 (singleton_mem_sampledForest.2 (mem_univ _))
  have hk : #(roots G) = 1 := by
    have := (roots_nonempty_iff.2 ⟨_, hsing (Classical.arbitrary X)⟩).card_pos
    omega
  have huniv : (univ : Finset X) ∈ G := h3 ▸ h1.lineages_mem_of_card_roots_eq_one hk
  exact ⟨huniv, hsing, h1.1, h1.2⟩

/-! ### Three taxa -/

/-- On `Fin 3`, a hierarchy containing the pair `{i, j}` is the rooted tree with cherry `{i, j}`. -/
theorem triple_fin3_eq_hierarchyOf_pair {H : Finset (Finset (Fin 3))} (hH : IsHierarchy H)
    {i j : Fin 3} (hij : i ≠ j) (h : {i, j} ∈ H) : H = hierarchyOf {{i, j}} := by
  have key : ∀ i j : Fin 3, i ≠ j → ∀ D : Finset (Fin 3), D.Nonempty →
      (D ⊆ {i, j} ∨ {i, j} ⊆ D ∨ Disjoint D {i, j}) → D ∈ hierarchyOf {{i, j}} := by
    decide
  ext D
  constructor
  · intro hD
    exact key i j hij D (hH.2.2.1 D hD) (hH.2.2.2 D hD _ h)
  · intro hD
    simp only [hierarchyOf, mem_insert, mem_union, mem_singleton, mem_image, mem_univ,
      true_and] at hD
    rcases hD with rfl | rfl | ⟨x, rfl⟩
    exacts [hH.1, h, hH.2.1 x]

/-- On `Fin 3`, the probability of the rooted triple `ij|k` is that of the rooted gene tree with
cherry `{i, j}`. -/
theorem triple_fin3_rootedTripleProb (τ : SpeciesTree (Fin 3)) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    τ.rootedTripleProb i j k = τ.rootedDist id (rootedTree3 {i, j}) := by
  have hpair : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∀ C : Finset (Fin 3),
      i ∈ C → j ∈ C → k ∉ C → C = {i, j} := by
    decide
  unfold SpeciesTree.rootedTripleProb
  rw [Finset.sum_eq_single (rootedTree3 {i, j})]
  · refine ite_eq_left ⟨{i, j}, ?_, mem_insert_self _ _, mem_insert_of_mem (mem_singleton_self _),
      ?_⟩
    · simp [rootedTree3, hierarchyOf]
    · rw [mem_insert, mem_singleton, not_or]
      exact ⟨hik.symm, hjk.symm⟩
  · intro G _ hG
    split_ifs with h
    · by_contra hne
      obtain ⟨C, hC, hi, hj, hk⟩ := h
      rw [hpair i j k hij hik hjk C hi hj hk] at hC
      exact hG (triple_fin3_eq_hierarchyOf_pair (triple_isHierarchy_of_rootedDist_ne_zero τ hne)
        hij hC)
    · rfl
  · intro h
    exact absurd (mem_univ _) h

omit [Fintype X] in
/-- On a set `S = {x, y, z}` of three taxa, the trace of `A` is `{x, y}` exactly when `A` contains
`x` and `y` but not `z`. -/
private theorem triple_subtype_eq_pair {S A : Finset X} {x y z : X}
    (hS : ∀ w ∈ S, w = x ∨ w = y ∨ w = z) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxz : x ≠ z)
    (hyz : y ≠ z) :
    A.subtype (· ∈ S) = {⟨x, hx⟩, ⟨y, hy⟩} ↔ x ∈ A ∧ y ∈ A ∧ z ∉ A := by
  constructor
  · intro h
    have hx' : (⟨x, hx⟩ : S) ∈ A.subtype (· ∈ S) := by
      rw [h]
      exact mem_insert_self _ _
    have hy' : (⟨y, hy⟩ : S) ∈ A.subtype (· ∈ S) := by
      rw [h]
      exact mem_insert_of_mem (mem_singleton_self _)
    refine ⟨mem_subtype.1 hx', mem_subtype.1 hy', fun hzA => ?_⟩
    have hz' : (⟨z, hz⟩ : S) ∈ A.subtype (· ∈ S) := mem_subtype.2 hzA
    rw [h, mem_insert, mem_singleton, Subtype.mk.injEq, Subtype.mk.injEq] at hz'
    rcases hz' with h1 | h1
    exacts [hxz h1.symm, hyz h1.symm]
  · rintro ⟨hxA, hyA, hzA⟩
    ext ⟨w, hw⟩
    rw [mem_subtype, mem_insert, mem_singleton, Subtype.mk.injEq, Subtype.mk.injEq]
    rcases hS w hw with rfl | rfl | rfl
    · simp [hxA]
    · simp [hyA]
    · simp [hzA, hxz.symm, hyz.symm]

/-- The bijection between three distinct taxa `{a, b, c}` and `Fin 3`. -/
private def tripleEquiv {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset X) ≃ Fin 3 where
  toFun x := if x.1 = a then 0 else if x.1 = b then 1 else 2
  invFun := ![⟨a, by simp⟩, ⟨b, by simp⟩, ⟨c, by simp⟩]
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [hab.symm, hac.symm, hbc.symm]
  right_inv i := by
    fin_cases i <;> simp [hab.symm, hac.symm, hbc.symm]

/-- **Reduction to three taxa.** For distinct taxa `a, b, c`, the probabilities of the rooted
triples `ab|c`, `ac|b`, `bc|a` are those of the rooted gene trees with cherries `{0, 1}`,
`{0, 2}`, `{1, 2}` under a species tree `τ` on `Fin 3` (the induced tree on `{a, b, c}`,
relabelled); the 2-element clusters of `τ` correspond to the clusters of `σ` containing exactly two
of `a, b, c`, and the length of the edge above `{0, 1}` is the sum of the lengths of the clusters
of `σ` containing `a` and `b` but not `c`. -/
theorem triple_exists_fin3 (σ : SpeciesTree X) {a b c : X} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    ∃ τ : SpeciesTree (Fin 3),
      σ.rootedTripleProb a b c = τ.rootedDist id (rootedTree3 {0, 1}) ∧
      σ.rootedTripleProb a c b = τ.rootedDist id (rootedTree3 {0, 2}) ∧
      σ.rootedTripleProb b c a = τ.rootedDist id (rootedTree3 {1, 2}) ∧
      (({0, 1} : Finset (Fin 3)) ∈ τ.clusters ↔ ∃ C ∈ σ.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C) ∧
      (({0, 2} : Finset (Fin 3)) ∈ τ.clusters ↔ ∃ C ∈ σ.clusters, a ∈ C ∧ c ∈ C ∧ b ∉ C) ∧
      (({1, 2} : Finset (Fin 3)) ∈ τ.clusters ↔ ∃ C ∈ σ.clusters, b ∈ C ∧ c ∈ C ∧ a ∉ C) ∧
      τ.length {0, 1} = ∑ A ∈ σ.clusters with a ∈ A ∧ b ∈ A ∧ c ∉ A, σ.length A := by
  set S : Finset X := {a, b, c} with hSdef
  have hS : S.Nonempty := insert_nonempty _ _
  have haS : a ∈ S := by simp [hSdef]
  have hbS : b ∈ S := by simp [hSdef]
  have hcS : c ∈ S := by simp [hSdef]
  have hS3 : ∀ w ∈ S, w = a ∨ w = b ∨ w = c := by simp [hSdef]
  set e := tripleEquiv hab hac hbc with he
  have hea : e ⟨a, haS⟩ = 0 := by simp [he, tripleEquiv]
  have heb : e ⟨b, hbS⟩ = 1 := by simp [he, tripleEquiv, hab.symm]
  have hec : e ⟨c, hcS⟩ = 2 := by simp [he, tripleEquiv, hac.symm, hbc.symm]
  have hea' : e.symm 0 = ⟨a, haS⟩ := by rw [Equiv.symm_apply_eq, hea]
  have heb' : e.symm 1 = ⟨b, hbS⟩ := by rw [Equiv.symm_apply_eq, heb]
  set τ := (σ.restrict S hS).relabel e with hτ
  -- the rooted triples
  have htriple : ∀ (x y z : X) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S),
      σ.rootedTripleProb x y z = τ.rootedTripleProb (e ⟨x, hx⟩) (e ⟨y, hy⟩) (e ⟨z, hz⟩) := by
    intro x y z hx hy hz
    rw [hτ, triple_rootedTripleProb_relabel]
    exact (triple_rootedTripleProb_restrict σ S hS ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩).symm
  -- the clusters
  have hclusters : ∀ (x y z : X) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S), x ≠ z → y ≠ z →
      (∀ w ∈ S, w = x ∨ w = y ∨ w = z) →
      (({e ⟨x, hx⟩, e ⟨y, hy⟩} : Finset (Fin 3)) ∈ τ.clusters ↔
        ∃ C ∈ σ.clusters, x ∈ C ∧ y ∈ C ∧ z ∉ C) := by
    intro x y z hx hy hz hxz hyz hS'
    rw [hτ, SpeciesTree.relabel_clusters, mem_relabelFamily, Finset.map_insert,
      Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    rw [SpeciesTree.restrict_clusters, mem_restrictClusters]
    constructor
    · rintro ⟨A, hA, -, hAxy⟩
      exact ⟨A, hA, (triple_subtype_eq_pair hS' hx hy hz hxz hyz).1 hAxy⟩
    · rintro ⟨A, hA, hxyz⟩
      exact ⟨A, hA, ⟨x, mem_inter.2 ⟨hxyz.1, hx⟩⟩,
        (triple_subtype_eq_pair hS' hx hy hz hxz hyz).2 hxyz⟩
  refine ⟨τ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htriple a b c haS hbS hcS, hea, heb, hec]
    exact triple_fin3_rootedTripleProb τ (by decide) (by decide) (by decide)
  · rw [htriple a c b haS hcS hbS, hea, heb, hec]
    exact triple_fin3_rootedTripleProb τ (by decide) (by decide) (by decide)
  · rw [htriple b c a hbS hcS haS, hea, heb, hec]
    exact triple_fin3_rootedTripleProb τ (by decide) (by decide) (by decide)
  · have := hclusters a b c haS hbS hcS hac hbc hS3
    rwa [hea, heb] at this
  · have := hclusters a c b haS hcS hbS hab hbc.symm (fun w hw => by
      rcases hS3 w hw with h | h | h <;> simp [h])
    rwa [hea, hec] at this
  · have := hclusters b c a hbS hcS haS hab.symm hac.symm (fun w hw => by
      rcases hS3 w hw with h | h | h <;> simp [h])
    rwa [heb, hec] at this
  · rw [hτ, SpeciesTree.relabel_length, Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding, hea', heb']
    rw [SpeciesTree.restrict_length]
    unfold SpeciesTree.restrictLength
    refine Finset.sum_congr (filter_congr fun A _ => ?_) fun _ _ => rfl
    rw [triple_subtype_eq_pair hS3 haS hbS hcS hac hbc]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun hA => h.2.2 ?_, h⟩
      rw [hA]
      exact mem_univ c

/-! ### Resolved triples -/

/-- The sum of the lengths of the clusters containing `a` and `b` but not `c` is positive if there
is such a cluster. -/
theorem triple_length_pos (σ : SpeciesTree X) {a b c : X}
    (h : ∃ C ∈ σ.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C) :
    0 < ∑ A ∈ σ.clusters with a ∈ A ∧ b ∈ A ∧ c ∉ A, σ.length A := by
  obtain ⟨C, hC, hC'⟩ := h
  refine Finset.sum_pos (fun A hA => ?_) ⟨C, mem_filter.2 ⟨hC, hC'⟩⟩
  obtain ⟨hA, -, -, hcA⟩ := mem_filter.1 hA
  refine σ.length_pos A hA fun hAu => hcA ?_
  rw [hAu]
  exact mem_univ c

/-- **The probabilities of the rooted triples on a resolved triple.** If some cluster contains `a`
and `b` but not `c`, then `ℙ(ab|c) = 1 - (2/3) e^{-t}` and `ℙ(ac|b) = ℙ(bc|a) = (1/3) e^{-t}`, where
`t` is the sum of the lengths of the clusters containing `a` and `b` but not `c` (equation (1) on
the induced species tree on `{a, b, c}`). -/
theorem triple_rootedTripleProb_of_resolved (σ : SpeciesTree X) {a b c : X} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (h : ∃ C ∈ σ.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C) :
    σ.rootedTripleProb a b c =
        1 - 2 / 3 * exp (-∑ A ∈ σ.clusters with a ∈ A ∧ b ∈ A ∧ c ∉ A, σ.length A) ∧
      σ.rootedTripleProb a c b =
        1 / 3 * exp (-∑ A ∈ σ.clusters with a ∈ A ∧ b ∈ A ∧ c ∉ A, σ.length A) ∧
      σ.rootedTripleProb b c a =
        1 / 3 * exp (-∑ A ∈ σ.clusters with a ∈ A ∧ b ∈ A ∧ c ∉ A, σ.length A) := by
  obtain ⟨τ, h1, h2, h3, h01, -, -, hlen⟩ := triple_exists_fin3 σ hab hac hbc
  have hτ : τ.clusters = clusters3 :=
    triple_fin3_eq_hierarchyOf_pair τ.isHierarchy (by decide) (h01.2 h)
  obtain ⟨e1, e2, e3, -, -⟩ := equation1 τ hτ
  rw [h1, h2, h3, e1, e2, e3, hlen]
  exact ⟨rfl, rfl, rfl⟩

/-- If some cluster contains `a` and `b` but not `c`, then `ℙ(ab|c) > 1/3`. -/
theorem triple_one_third_lt_of_resolved (σ : SpeciesTree X) {a b c : X} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (h : ∃ C ∈ σ.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C) :
    1 / 3 < σ.rootedTripleProb a b c := by
  rw [(triple_rootedTripleProb_of_resolved σ hab hac hbc h).1]
  have := exp_lt_one_iff.2 (neg_lt_zero.2 (triple_length_pos σ h))
  linarith

/-- If some cluster contains `a` and `c` but not `b`, then `ℙ(ab|c) < 1/3`. -/
theorem triple_lt_one_third_of_resolved_left (σ : SpeciesTree X) {a b c : X} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (h : ∃ C ∈ σ.clusters, a ∈ C ∧ c ∈ C ∧ b ∉ C) :
    σ.rootedTripleProb a b c < 1 / 3 := by
  rw [(triple_rootedTripleProb_of_resolved σ hac hab hbc.symm h).2.1]
  have := exp_lt_one_iff.2 (neg_lt_zero.2 (triple_length_pos σ h))
  linarith

/-- If some cluster contains `b` and `c` but not `a`, then `ℙ(ab|c) < 1/3`. -/
theorem triple_lt_one_third_of_resolved_right (σ : SpeciesTree X) {a b c : X} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (h : ∃ C ∈ σ.clusters, b ∈ C ∧ c ∈ C ∧ a ∉ C) :
    σ.rootedTripleProb a b c < 1 / 3 := by
  rw [triple_rootedTripleProb_comm,
    (triple_rootedTripleProb_of_resolved σ hbc hab.symm hac.symm h).2.1]
  have := exp_lt_one_iff.2 (neg_lt_zero.2 (triple_length_pos σ h))
  linarith

/-! ### Binary species trees -/

/-- A binary species tree resolves every triple of distinct taxa: some cluster contains exactly
two of them. -/
theorem triple_resolved_or_of_isBinary {σ : SpeciesTree X} (hσ : σ.IsBinary) {a b c : X}
    (hab : a ≠ b) :
    (∃ C ∈ σ.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C) ∨ (∃ C ∈ σ.clusters, a ∈ C ∧ c ∈ C ∧ b ∉ C) ∨
      ∃ C ∈ σ.clusters, b ∈ C ∧ c ∈ C ∧ a ∉ C := by
  have hH := σ.isHierarchy
  set T : Finset X := {a, b, c} with hT
  have hTne : T.Nonempty := insert_nonempty _ _
  have hL := hH.lca_mem hTne
  have hTL : T ⊆ lca σ.clusters T := subset_lca _ _
  have haL : a ∈ lca σ.clusters T := hTL (by simp [hT])
  have hbL : b ∈ lca σ.clusters T := hTL (by simp [hT])
  have hcL : c ∈ lca σ.clusters T := hTL (by simp [hT])
  have hL2 : 2 ≤ #(lca σ.clusters T) := one_lt_card.2 ⟨a, haL, b, hbL, hab⟩
  obtain ⟨B, hB, C, hC, hBC, hBCL⟩ := hσ _ hL hL2
  -- `T` lies in neither part
  have hnot : ∀ D ∈ σ.clusters, ∀ E ∈ σ.clusters, Disjoint D E → D ∪ E = lca σ.clusters T →
      ¬ (a ∈ D ∧ b ∈ D ∧ c ∈ D) := by
    rintro D hD E hE hDE hDEL ⟨haD, hbD, hcD⟩
    have hLD : lca σ.clusters T ⊆ D := lca_subset hD (by
      intro x hx
      simp only [hT, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption)
    obtain ⟨y, hy⟩ := σ.nonempty_of_mem E hE
    have hyD : y ∈ D := hLD (hDEL ▸ mem_union_right D hy)
    exact disjoint_left.1 hDE hyD hy
  have hnotB := hnot B hB C hC hBC hBCL
  have hnotC := hnot C hC B hB hBC.symm (by rw [union_comm]; exact hBCL)
  have hpart : ∀ x ∈ lca σ.clusters T, (x ∈ B ∧ x ∉ C) ∨ (x ∈ C ∧ x ∉ B) := by
    intro x hx
    rw [← hBCL, mem_union] at hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hx, disjoint_left.1 hBC hx⟩
    · exact Or.inr ⟨hx, disjoint_right.1 hBC hx⟩
  rcases hpart a haL with ⟨haB, haC⟩ | ⟨haC, haB⟩ <;>
    rcases hpart b hbL with ⟨hbB, hbC⟩ | ⟨hbC, hbB⟩ <;>
    rcases hpart c hcL with ⟨hcB, hcC⟩ | ⟨hcC, hcB⟩
  · exact absurd ⟨haB, hbB, hcB⟩ hnotB
  · exact Or.inl ⟨B, hB, haB, hbB, hcB⟩
  · exact Or.inr (Or.inl ⟨B, hB, haB, hcB, hbB⟩)
  · exact Or.inr (Or.inr ⟨C, hC, hbC, hcC, haC⟩)
  · exact Or.inr (Or.inr ⟨B, hB, hbB, hcB, haB⟩)
  · exact Or.inr (Or.inl ⟨C, hC, haC, hcC, hbC⟩)
  · exact Or.inl ⟨C, hC, haC, hbC, hcC⟩
  · exact absurd ⟨haC, hbC, hcC⟩ hnotC

/-- In a binary species tree, a cluster contains `a` and `b` but not `c` if and only if the
probability of the rooted triple `ab|c` exceeds `1/3`. -/
theorem triple_resolved_iff_of_isBinary {σ : SpeciesTree X} (hσ : σ.IsBinary) {a b c : X}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∃ C ∈ σ.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C) ↔ 1 / 3 < σ.rootedTripleProb a b c := by
  refine ⟨triple_one_third_lt_of_resolved σ hab hac hbc, fun hp => ?_⟩
  rcases triple_resolved_or_of_isBinary hσ (c := c) hab with h | h | h
  · exact h
  · exact absurd hp (not_lt.2 (triple_lt_one_third_of_resolved_left σ hab hac hbc h).le)
  · exact absurd hp (not_lt.2 (triple_lt_one_third_of_resolved_right σ hab hac hbc h).le)

/-! ### Rooted triples determine the rooted metric tree -/

/-- A cluster `A` with at least two taxa, other than the root, is the only cluster containing two
taxa `a₁, a₂` of `A` (from different children of `A`) and not containing a taxon `b` (from the
parent of `A`). -/
private theorem triple_exists_witness {H : Finset (Finset X)} (hH : IsHierarchy H) {A : Finset X}
    (hA : A ∈ H) (hAu : A ≠ univ) (h2 : 2 ≤ #A) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b ∉ A, a₁ ≠ a₂ ∧ ∀ B ∈ H, a₁ ∈ B → a₂ ∈ B → b ∉ B → B = A := by
  obtain ⟨a₁, ha₁⟩ : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨B₁, hB₁, ha₁B₁⟩ := hH.exists_mem_childClusters h2 ha₁
  obtain ⟨a₂, ha₂, ha₂B₁⟩ := exists_of_ssubset (mem_childClusters.1 hB₁).2.1
  obtain ⟨b, hbP, hbA⟩ := exists_of_ssubset (hH.ssubset_parentCluster hA hAu)
  refine ⟨a₁, ha₁, a₂, ha₂, b, hbA, fun e => ha₂B₁ (e ▸ ha₁B₁),
    fun B hB ha₁B ha₂B hbB => ?_⟩
  rcases hH.subset_or_subset_of_mem hB hA ha₁B ha₁ with h | h
  · by_contra hne
    have hBA : B ⊂ A := ssubset_of_subset_not_subset h fun h' => hne (Subset.antisymm h h')
    exact ha₂B₁ (hH.subset_of_mem_childClusters hB₁ hB hBA
      (not_disjoint_iff.2 ⟨a₁, ha₁B₁, ha₁B⟩) ha₂B)
  · by_contra hne
    have hAB : A ⊂ B := ssubset_of_subset_not_subset h fun h' => hne (Subset.antisymm h' h)
    exact hbB (parentCluster_subset hB hAB hbP)

/-- One inclusion of the clusters in `triple_sameRootedMetricTree`. -/
private theorem triple_clusters_subset (σ σ' : SpeciesTree X)
    (hσ : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      ((∃ C ∈ σ.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C) ↔ 1 / 3 < σ.rootedTripleProb a b c))
    (hσ' : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      ((∃ C ∈ σ'.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C) ↔ 1 / 3 < σ'.rootedTripleProb a b c))
    (h : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      σ.rootedTripleProb a b c = σ'.rootedTripleProb a b c) :
    σ.clusters ⊆ σ'.clusters := by
  intro A hA
  apply σ'.mem_clusters_of_triples (σ.nonempty_of_mem A hA)
  intro a ha a' ha' b hb
  have hab : a ≠ b := fun e => hb (e ▸ ha)
  have ha'b : a' ≠ b := fun e => hb (e ▸ ha')
  by_cases haa' : a = a'
  · subst haa'
    refine ⟨{a}, σ'.singleton_mem a, mem_singleton_self a, mem_singleton_self a, ?_⟩
    rw [mem_singleton]
    exact fun e => hab e.symm
  · rw [hσ' a a' b haa' hab ha'b, ← h a a' b haa' hab ha'b]
    exact (hσ a a' b haa' hab ha'b).1 ⟨A, hA, ha, ha', hb⟩

/-- **Rooted triples determine the rooted metric tree.** Two species trees with the same
probabilities of rooted triples, in each of which a cluster contains `a` and `b` but not `c`
exactly when `ℙ(ab|c) > 1/3`, have the same rooted metric tree. -/
theorem triple_sameRootedMetricTree (σ σ' : SpeciesTree X)
    (hσ : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      ((∃ C ∈ σ.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C) ↔ 1 / 3 < σ.rootedTripleProb a b c))
    (hσ' : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      ((∃ C ∈ σ'.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C) ↔ 1 / 3 < σ'.rootedTripleProb a b c))
    (h : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c →
      σ.rootedTripleProb a b c = σ'.rootedTripleProb a b c) :
    σ.SameRootedMetricTree σ' := by
  have hcl : σ.clusters = σ'.clusters :=
    Subset.antisymm (triple_clusters_subset σ σ' hσ hσ' h)
      (triple_clusters_subset σ' σ hσ' hσ fun a b c hab hac hbc => (h a b c hab hac hbc).symm)
  refine ⟨hcl, fun A hA h2 hAu => ?_⟩
  obtain ⟨a₁, ha₁, a₂, ha₂, b, hb, ha₁₂, huniq⟩ := triple_exists_witness σ.isHierarchy hA hAu h2
  have ha₁b : a₁ ≠ b := fun e => hb (e ▸ ha₁)
  have ha₂b : a₂ ≠ b := fun e => hb (e ▸ ha₂)
  have hres : ∃ C ∈ σ.clusters, a₁ ∈ C ∧ a₂ ∈ C ∧ b ∉ C := ⟨A, hA, ha₁, ha₂, hb⟩
  -- `A` is the only cluster containing `a₁` and `a₂` but not `b`
  have hfilter : ∀ τ : SpeciesTree X, τ.clusters = σ.clusters →
      ∑ B ∈ τ.clusters with a₁ ∈ B ∧ a₂ ∈ B ∧ b ∉ B, τ.length B = τ.length A := by
    intro τ hτ
    rw [hτ, Finset.sum_eq_single_of_mem A (mem_filter.2 ⟨hA, ha₁, ha₂, hb⟩)]
    intro B hB hBA
    obtain ⟨hB, h1, h2, h3⟩ := mem_filter.1 hB
    exact absurd (huniq B hB h1 h2 h3) hBA
  have e := h a₁ a₂ b ha₁₂ ha₁b ha₂b
  rw [(triple_rootedTripleProb_of_resolved σ ha₁₂ ha₁b ha₂b hres).1,
    (triple_rootedTripleProb_of_resolved σ' ha₁₂ ha₁b ha₂b (hcl ▸ hres)).1,
    hfilter σ rfl, hfilter σ' hcl.symm] at e
  have e' : exp (-σ.length A) = exp (-σ'.length A) := by linarith
  exact neg_inj.1 (exp_injective e')

/-- **Proposition 1** (`prop:rootedtriple`). For a species tree with `n ≥ 3` taxa, the probabilities of rooted triple
gene tree topologies determine the species tree topology and internal branch lengths. -/
theorem proposition1 (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary)
    (h : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c → σ.rootedTripleProb a b c = σ'.rootedTripleProb a b c) :
    σ.SameRootedMetricTree σ' :=
  triple_sameRootedMetricTree σ σ'
    (fun _ _ _ hab hac hbc => triple_resolved_iff_of_isBinary hσ hab hac hbc)
    (fun _ _ _ hab hac hbc => triple_resolved_iff_of_isBinary hσ' hab hac hbc) h

/-- **Corollary 2** (`cor:rgt`). For a species tree with `n ≥ 3` taxa, the distribution of rooted gene tree
topologies determines the species tree topology and internal branch lengths. -/
theorem corollary2 (hX : 3 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.rootedDist id = σ'.rootedDist id) :
    σ.SameRootedMetricTree σ' := by
  refine proposition1 σ σ' hσ hσ' fun a b c _ _ _ => ?_
  unfold SpeciesTree.rootedTripleProb
  rw [h]

end ADR11
