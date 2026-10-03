module

public import ADR11.Identifiability.Corollary10
public import ADR11.Identifiability.Unrooted
public import ADR11.Trees.RootLocation

/-!
# Theorem 9 and Corollary 10 for nonbinary species trees

Helpers for Proposition 11, from the end of its proof (Appendix C): "Theorem 9 also extends,
noting that if the root of the species tree has degree greater than 2, then its location will be
identified by some 5-taxon subtree with the same property. The proof of Corollary 10 did not use
the assumption that `σ⁺` is binary, so it applies to nonbinary species trees as well."

The five-taxon case (Proposition 8 for nonbinary species trees) is a hypothesis of these results.

The location of the root `ρ` on `σ⁻` is an edge (a root of degree two) or a vertex (a root of
degree at least three); in both cases it is given by the children of the root, the sides of the
splits of `σ⁻` at `ρ` away from `ρ`.

## Main results

* `rl_nb_mem_childClusters_iff`: the root location. A side `A` of a split of `σ⁻` is a child of the
  root if and only if, for every set `S` of five taxa meeting `A` and `Aᶜ`, `A ∩ S` is a child of
  the root of `σ(S)`. As in the binary case (`rl_exists_five_not_rootOn`), the converse direction
  uses a quartet distinguishing the split [Steel 1992, Proposition 6] completed by a taxon so that
  the most recent common ancestor of the five taxa is `ρ`; when the root has degree greater than
  two, five taxa meeting three children of the root, whose tree has a root of degree greater than
  two as well, also serve.
* `rl_nb_childClusters_univ_eq`: hence the unrooted tree and the induced five-taxon trees determine
  the children of the root.
* `rl_nb_theorem9`: Theorem 9 for nonbinary species trees, given the five-taxon case.
* `c10_nb_corollary10`: Corollary 10 for nonbinary species trees, given the five-taxon case.
-/

@[expose] public section

namespace ADR11

open Finset

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- The root location for species trees that need not be binary (proof of Proposition 11). If
`A | Aᶜ` is a split of `σ⁻` and `A` is not a child of the root `ρ` of `σ`, then some set `S` of five
taxa meeting `A` and `Aᶜ` induces a tree `σ(S)` in which `A ∩ S` is not a child of the root.

* An internal edge, as in the paper: a quartet `Q` distinguishing the edge
  [Steel 1992, Proposition 6] and a taxon `x ∉ Q` such that the most recent common ancestor of
  `S = Q ∪ {x}` is `ρ`; the children of the root of `σ(S)` are then the traces of the children of
  `ρ`, and only `A` separates the quartet as `A` does.
* The pendant edge of a taxon `ℓ` whose leaf is not a child of the root (departure from the paper,
  as in the binary case, `rl_exists_five_not_rootOn`: no quartet distinguishes a pendant edge):
  `S` consists of `ℓ`, another taxon `m` of the child `R` of the root containing `ℓ`, a taxon
  `r ∉ R`, and two more taxa.
* `A = X ∖ {ℓ}` where the leaf `ℓ` is a child of a root of degree greater than two: `S` meets
  three children of the root (`ℓ`, `r₁`, `r₂`), so that the root of `σ(S)` has degree greater
  than two as well, and `A ∩ S`, containing `r₁` and `r₂`, is not one of its children. -/
theorem rl_nb_exists_five_not_mem_childClusters (hX : 5 ≤ Fintype.card X) (σ : SpeciesTree X)
    {A : Finset X} (hA : A ∈ unroot σ.clusters) (hAR : A ∉ childClusters σ.clusters univ) :
    ∃ S : Finset X, ∃ hS : S.Nonempty, #S = 5 ∧ (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧
      A.subtype (· ∈ S) ∉ childClusters (σ.restrict S hS).clusters univ := by
  have hH := σ.isHierarchy
  have h2 : 2 ≤ Fintype.card X := by omega
  obtain ⟨hAne, hAu⟩ := counts_nonempty_of_mem_unroot hH hA
  have hAcne := rl_compl_nonempty hAu
  have hroot := rl_exists_mem_childClusters_univ hH h2
  -- another taxon of a child of the root other than a leaf
  have hother : ∀ {R : Finset X} {ℓ : X}, ℓ ∈ R → R ≠ {ℓ} → ∃ m ∈ R, m ≠ ℓ := by
    intro R ℓ hℓR hRℓ
    by_contra hcon
    exact hRℓ (eq_singleton_iff_unique_mem.2 ⟨hℓR, fun y hy =>
      Classical.byContradiction fun hyℓ => hcon ⟨y, hy, hyℓ⟩⟩)
  by_cases hA1 : #A = 1
  · -- the pendant edge `{ℓ} | X ∖ {ℓ}`, where `{ℓ}` is not a child of the root
    obtain ⟨ℓ, rfl⟩ := card_eq_one.1 hA1
    obtain ⟨R, hR, hℓR⟩ := hroot ℓ
    obtain ⟨m, hmR, hmℓ⟩ := hother hℓR fun e => hAR (e ▸ hR)
    obtain ⟨r, hr⟩ := rl_compl_nonempty (rl_ne_univ_of_mem_childClusters hR)
    obtain ⟨S, hTS, hS5⟩ := rl_exists_five hX (T := {ℓ, m, r})
      (card_le_three.trans (by norm_num))
    have hℓS : ℓ ∈ S := hTS (by simp)
    have hmS : m ∈ S := hTS (by simp)
    have hrS : r ∈ S := hTS (by simp)
    have hS : S.Nonempty := ⟨ℓ, hℓS⟩
    refine ⟨S, hS, hS5, ⟨ℓ, mem_inter.2 ⟨mem_singleton_self ℓ, hℓS⟩⟩,
      ⟨m, mem_inter.2 ⟨mem_compl.2 (by simpa using hmℓ), hmS⟩⟩, fun hC => ?_⟩
    -- the most recent common ancestor of `S` is the root
    have hmrca : ∀ R' ∈ childClusters σ.clusters univ, ¬ S ⊆ R' := by
      intro R' hR' hSR'
      have := rl_eq_of_mem_childClusters hH hR hR' hℓR (hSR' hℓS)
      subst this
      exact mem_compl.1 hr (hSR' hrS)
    obtain ⟨R', hR', -, hR'eq⟩ := (rl_mem_childClusters_restrict_iff σ hS hmrca).1 hC
    -- `R' ∩ S = {ℓ}`, so `R' = R`, which contains `m`
    have hℓR' : ℓ ∈ R' := (rl_mem_iff_of_subtype_eq hR'eq hℓS).2 (mem_singleton_self ℓ)
    have := rl_eq_of_mem_childClusters hH hR hR' hℓR hℓR'
    subst this
    exact hmℓ (mem_singleton.1 ((rl_mem_iff_of_subtype_eq hR'eq hmS).1 hmR))
  by_cases hAc1 : #Aᶜ = 1
  · -- the pendant edge `X ∖ {ℓ} | {ℓ}`
    obtain ⟨ℓ, hℓ⟩ := card_eq_one.1 hAc1
    have hmemA : ∀ y, y ∈ A ↔ y ≠ ℓ := fun y => by
      have hy : y ∉ A ↔ y = ℓ := by rw [← mem_compl, hℓ, mem_singleton]
      exact ⟨fun hyA e => hy.2 e hyA, fun hyℓ => Classical.byContradiction fun hyA =>
        hyℓ (hy.1 hyA)⟩
    have hℓA : ℓ ∈ Aᶜ := by
      rw [hℓ]
      exact mem_singleton_self ℓ
    obtain ⟨R, hR, hℓR⟩ := hroot ℓ
    by_cases hRℓ : R = {ℓ}
    · -- `{ℓ}` is a child of the root, whose degree is then greater than two: five taxa meeting
      -- three children of the root, `ℓ`, `r₁ ∈ R₁` and `r₂ ∈ R₂`
      subst hRℓ
      obtain ⟨r₁, hr₁⟩ : ∃ r₁ : X, r₁ ≠ ℓ := by
        obtain ⟨y, hy⟩ := hAne
        exact ⟨y, (hmemA y).1 hy⟩
      obtain ⟨R₁, hR₁, hr₁R₁⟩ := hroot r₁
      have hℓR₁ : ℓ ∉ R₁ := fun h => by
        have := rl_eq_of_mem_childClusters hH hR hR₁ (mem_singleton_self ℓ) h
        subst this
        exact hr₁ (mem_singleton.1 hr₁R₁)
      -- `R₁ ≠ A`, so a taxon `r₂ ≠ ℓ` lies outside `R₁`
      obtain ⟨r₂, hr₂, hr₂R₁⟩ : ∃ r₂, r₂ ≠ ℓ ∧ r₂ ∉ R₁ := by
        by_contra hcon
        refine hAR ?_
        have hR₁A : R₁ = A := by
          ext y
          rw [hmemA]
          constructor
          · rintro hy rfl
            exact hℓR₁ hy
          · intro hy
            exact Classical.byContradiction fun hyR => hcon ⟨y, hy, hyR⟩
        exact hR₁A ▸ hR₁
      obtain ⟨S, hTS, hS5⟩ := rl_exists_five hX (T := {ℓ, r₁, r₂})
        (card_le_three.trans (by norm_num))
      have hℓS : ℓ ∈ S := hTS (by simp)
      have hr₁S : r₁ ∈ S := hTS (by simp)
      have hr₂S : r₂ ∈ S := hTS (by simp)
      have hS : S.Nonempty := ⟨ℓ, hℓS⟩
      refine ⟨S, hS, hS5, ⟨r₁, mem_inter.2 ⟨(hmemA r₁).2 hr₁, hr₁S⟩⟩,
        ⟨ℓ, mem_inter.2 ⟨hℓA, hℓS⟩⟩, fun hC => ?_⟩
      -- the most recent common ancestor of `S` is the root
      have hmrca : ∀ R' ∈ childClusters σ.clusters univ, ¬ S ⊆ R' := by
        intro R' hR' hSR'
        have := rl_eq_of_mem_childClusters hH hR hR' (mem_singleton_self ℓ) (hSR' hℓS)
        subst this
        exact hr₁ (mem_singleton.1 (hSR' hr₁S))
      obtain ⟨R', hR', -, hR'eq⟩ := (rl_mem_childClusters_restrict_iff σ hS hmrca).1 hC
      -- `R' ∩ S = A ∩ S` contains `r₁` and `r₂`, so `R' = R₁` contains `r₂`
      have h1 : r₁ ∈ R' := (rl_mem_iff_of_subtype_eq hR'eq hr₁S).2 ((hmemA r₁).2 hr₁)
      have h2 : r₂ ∈ R' := (rl_mem_iff_of_subtype_eq hR'eq hr₂S).2 ((hmemA r₂).2 hr₂)
      have := rl_eq_of_mem_childClusters hH hR₁ hR' hr₁R₁ h1
      subst this
      exact hr₂R₁ h2
    · -- `{ℓ}` is not a child of the root: `ℓ`, another taxon `m` of the child `R` of the root
      -- containing `ℓ`, and a taxon `r ∉ R`
      obtain ⟨m, hmR, hmℓ⟩ := hother hℓR hRℓ
      obtain ⟨r, hr⟩ := rl_compl_nonempty (rl_ne_univ_of_mem_childClusters hR)
      have hrℓ : r ≠ ℓ := fun e => mem_compl.1 hr (e ▸ hℓR)
      obtain ⟨S, hTS, hS5⟩ := rl_exists_five hX (T := {ℓ, m, r})
        (card_le_three.trans (by norm_num))
      have hℓS : ℓ ∈ S := hTS (by simp)
      have hmS : m ∈ S := hTS (by simp)
      have hrS : r ∈ S := hTS (by simp)
      have hS : S.Nonempty := ⟨ℓ, hℓS⟩
      refine ⟨S, hS, hS5, ⟨m, mem_inter.2 ⟨(hmemA m).2 hmℓ, hmS⟩⟩,
        ⟨ℓ, mem_inter.2 ⟨hℓA, hℓS⟩⟩, fun hC => ?_⟩
      -- the most recent common ancestor of `S` is the root
      have hmrca : ∀ R' ∈ childClusters σ.clusters univ, ¬ S ⊆ R' := by
        intro R' hR' hSR'
        have := rl_eq_of_mem_childClusters hH hR hR' hℓR (hSR' hℓS)
        subst this
        exact mem_compl.1 hr (hSR' hrS)
      obtain ⟨R', hR', -, hR'eq⟩ := (rl_mem_childClusters_restrict_iff σ hS hmrca).1 hC
      -- `R' ∩ S = A ∩ S` contains `m`, so `R' = R`, and it contains `r ∉ R`
      have hmR' : m ∈ R' := (rl_mem_iff_of_subtype_eq hR'eq hmS).2 ((hmemA m).2 hmℓ)
      have := rl_eq_of_mem_childClusters hH hR hR' hmR hmR'
      subst this
      exact mem_compl.1 hr ((rl_mem_iff_of_subtype_eq hR'eq hrS).2 ((hmemA r).2 hrℓ))
  -- an internal edge: a quartet `aa'|bb'` distinguishing it [Steel 1992, Proposition 6]
  have hA2 : 2 ≤ #A := by
    have := card_pos.2 hAne
    omega
  have hAc2 : 2 ≤ #Aᶜ := by
    have := card_pos.2 hAcne
    omega
  obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, hQ⟩ :=
    exists_distinguishing_quartet σ hA hA2 hAc2
  rw [mem_compl] at hb hb'
  have hab : a ≠ b := by rintro rfl; exact hb ha
  have hab' : a ≠ b' := by rintro rfl; exact hb' ha
  have ha'b : a' ≠ b := by rintro rfl; exact hb ha'
  have ha'b' : a' ≠ b' := by rintro rfl; exact hb' ha'
  have hQ4 : #({a, a', b, b'} : Finset X) = 4 := by
    rw [card_insert_of_notMem (by simp [haa, hab, hab']),
      card_insert_of_notMem (by simp [ha'b, ha'b']), card_pair hbb]
  -- a taxon `x` such that the most recent common ancestor of `S = Q ∪ {x}` is the root
  obtain ⟨R₀, hR₀, haR₀⟩ := hroot a
  obtain ⟨x, hxQ, hS1, hS2⟩ := rl_exists_insert_meets hX hQ4 ⟨a, haR₀⟩
    (rl_compl_nonempty (rl_ne_univ_of_mem_childClusters hR₀))
  set S : Finset X := insert x {a, a', b, b'} with hSdef
  have hS : S.Nonempty := insert_nonempty _ _
  have hS5 : #S = 5 := by rw [hSdef, card_insert_of_notMem hxQ, hQ4]
  have haS : a ∈ S := by simp [hSdef]
  have ha'S : a' ∈ S := by simp [hSdef]
  have hbS : b ∈ S := by simp [hSdef]
  have hb'S : b' ∈ S := by simp [hSdef]
  refine ⟨S, hS, hS5, ⟨a, mem_inter.2 ⟨ha, haS⟩⟩, ⟨b, mem_inter.2 ⟨mem_compl.2 hb, hbS⟩⟩,
    fun hC => ?_⟩
  have hmrca : ∀ R' ∈ childClusters σ.clusters univ, ¬ S ⊆ R' := by
    intro R' hR' hSR'
    obtain ⟨y, hy⟩ := hS1
    have := rl_eq_of_mem_childClusters hH hR₀ hR' (mem_inter.1 hy).1 (hSR' (mem_inter.1 hy).2)
    subst this
    obtain ⟨z, hz⟩ := hS2
    exact mem_compl.1 (mem_inter.1 hz).1 (hSR' (mem_inter.1 hz).2)
  -- `A ∩ S` would be the trace `R' ∩ S` of a child `R'` of the root, which separates `aa'` from
  -- `bb'` as `A` does, so `R' = A`
  obtain ⟨R', hR', -, hR'eq⟩ := (rl_mem_childClusters_restrict_iff σ hS hmrca).1 hC
  have hmem : ∀ y ∈ S, y ∈ R' ↔ y ∈ A := fun y hy => rl_mem_iff_of_subtype_eq hR'eq hy
  have hR'U : R' ∈ unroot σ.clusters :=
    mem_unroot.2 (Or.inl ⟨(mem_childClusters.1 hR').1, rl_ne_univ_of_mem_childClusters hR'⟩)
  have := hQ R' hR'U ((hmem a haS).2 ha) ((hmem a' ha'S).2 ha')
    (fun h => hb ((hmem b hbS).1 h)) (fun h => hb' ((hmem b' hb'S).1 h))
  exact hAR (this ▸ hR')

/-- The root location for species trees that need not be binary (proof of Proposition 11): on at
least five taxa, a side `A` of a split of `σ⁻` is a child of the root if and only if, for every set
`S` of five taxa meeting `A` and `Aᶜ` (so that `σ⁻(S)` has the split), `A ∩ S` is a child of the
root of `σ(S)`. If `A` is a child of the root `ρ`, the most recent common ancestor of such an `S`
is `ρ`; the converse is `rl_nb_exists_five_not_mem_childClusters`. -/
theorem rl_nb_mem_childClusters_iff (hX : 5 ≤ Fintype.card X) (σ : SpeciesTree X)
    {A : Finset X} (hA : A ∈ unroot σ.clusters) :
    A ∈ childClusters σ.clusters univ ↔
      ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 → (A ∩ S).Nonempty → (Aᶜ ∩ S).Nonempty →
        A.subtype (· ∈ S) ∈ childClusters (σ.restrict S hS).clusters univ := by
  constructor
  · intro hAR S hS _ hAS hAcS
    refine (rl_mem_childClusters_restrict_iff σ hS fun R hR hSR => ?_).2 ⟨A, hAR, hAS, rfl⟩
    obtain ⟨y, hy⟩ := hAS
    have := rl_eq_of_mem_childClusters σ.isHierarchy hAR hR (mem_inter.1 hy).1
      (hSR (mem_inter.1 hy).2)
    subst this
    obtain ⟨z, hz⟩ := hAcS
    exact mem_compl.1 (mem_inter.1 hz).1 (hSR (mem_inter.1 hz).2)
  · intro h
    by_contra hAR
    obtain ⟨S, hS, hS5, hAS, hAcS, hnot⟩ := rl_nb_exists_five_not_mem_childClusters hX σ hA hAR
    exact hnot (h S hS hS5 hAS hAcS)

/-- The location of the root is determined (proof of Proposition 11): two species trees on at least
five taxa with the same unrooted tree and the same induced trees on all sets of five taxa have
the same children of the root. -/
theorem rl_nb_childClusters_univ_eq (hX : 5 ≤ Fintype.card X) {σ σ' : SpeciesTree X}
    (hU : unroot σ.clusters = unroot σ'.clusters)
    (h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).clusters = (σ'.restrict S hS).clusters) :
    childClusters σ.clusters univ = childClusters σ'.clusters univ := by
  have key : ∀ τ τ' : SpeciesTree X, unroot τ.clusters = unroot τ'.clusters →
      (∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
        (τ.restrict S hS).clusters = (τ'.restrict S hS).clusters) →
      ∀ A ∈ childClusters τ.clusters univ, A ∈ childClusters τ'.clusters univ := by
    intro τ τ' hU h5 A hA
    have hAU : A ∈ unroot τ.clusters :=
      mem_unroot.2 (Or.inl ⟨(mem_childClusters.1 hA).1, rl_ne_univ_of_mem_childClusters hA⟩)
    refine (rl_nb_mem_childClusters_iff hX τ' (hU ▸ hAU)).2 fun S hS hS5 hAS hAcS => ?_
    rw [← h5 S hS hS5]
    exact (rl_nb_mem_childClusters_iff hX τ hAU).1 hA S hS hS5 hAS hAcS
  ext A
  exact ⟨key σ σ' hU h5 A, key σ' σ hU.symm (fun S hS hS5 => (h5 S hS hS5).symm) A⟩

/-- Theorem 9 for species trees that need not be binary (proof of Proposition 11: "Theorem 9 also
extends, noting that if the root of the species tree has degree greater than 2, then its location
will be identified by some 5-taxon subtree with the same property"), given the five-taxon case
`five` (Proposition 8 for nonbinary species trees, for the induced five-taxon trees). For
`|X| ≥ 5`, the unrooted gene tree distribution determines the metric species tree.

The proof of Theorem 9: `σ⁻` is determined (Corollary 6 for nonbinary species trees,
`sameUnrootedMetricTree_of_unrootedDist_eq`), and by Lemma 5 and `five` so is every induced
five-taxon tree; they determine the location of the root (`rl_nb_childClusters_univ_eq`), hence
`ψ⁺` (`rl_eq_of_unroot_eq`), and the edge lengths (`rl_sameRootedMetricTree_of_clusters_eq`).

Departure from the paper: as in the binary case, a pendant edge is handled by another choice of
five taxa (see `rl_nb_exists_five_not_mem_childClusters`). -/
theorem rl_nb_theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id)
    (five : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).unrootedDist id = (σ'.restrict S hS).unrootedDist id →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS)) :
    σ.SameRootedMetricTree σ' := by
  -- `σ⁻` is determined (Corollary 6 for nonbinary species trees)
  have hU := sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h
  -- every induced five-taxon tree is determined (Lemma 5 and the five-taxon case)
  have h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS) :=
    fun S hS hS5 => five S hS hS5 (unrootedDist_restrict_eq h S hS)
  -- the location of the root: the children of the root
  have hR := rl_nb_childClusters_univ_eq hX hU.1 fun S hS hS5 => (h5 S hS hS5).1
  -- `ψ⁺`: the rooting of `ψ⁻` at the location of the root
  have hcl := rl_eq_of_unroot_eq σ.isHierarchy σ'.isHierarchy hU.1 hR
  -- the edge lengths
  exact rl_sameRootedMetricTree_of_clusters_eq hX hcl hU h5

/-- Corollary 10 for species trees that need not be binary (proof of Proposition 11: "The proof of
Corollary 10 did not use the assumption that `σ⁺` is binary, so it applies to nonbinary species
trees as well"), given the five-taxon case `five` (Proposition 8 for nonbinary species trees): the
proof of Corollary 10 (`c10_of_theorem9`) with Theorem 9 for nonbinary species trees
(`rl_nb_theorem9`). -/
theorem c10_nb_corollary10
    (five : ∀ {Y : Type u} [Fintype Y] [DecidableEq Y], Fintype.card Y = 5 →
      ∀ τ τ' : SpeciesTree Y, τ.unrootedDist id = τ'.unrootedDist id →
        τ.SameRootedMetricTree τ')
    (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} :=
  c10_of_theorem9 (P := fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun hY τ τ' _ _ hd => rl_nb_theorem9 hY τ τ' hd fun _ _ hS5 hdS =>
      five (by simpa using hS5) _ _ hdS)
    ℓ hℓ hcond σ σ' trivial trivial h

end ADR11
