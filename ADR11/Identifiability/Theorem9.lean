module

public import ADR11.Identifiability.Corollary6
public import ADR11.Identifiability.Proposition3
public import ADR11.Identifiability.Proposition8
public import ADR11.Trees.RootLocation

/-!
# Theorem 9: the main theorem

* `theorem9`: for `|X| ≥ 5` the unrooted gene tree distribution determines the metric species
  tree `σ⁺`.
* `theorem9_four`: for `|X| = 4` it determines exactly the unrooted metric species tree `σ⁻`.

## Proof (the paper's)

By Corollary 6, `σ⁻ = (ψ⁻, λ⁻)` is determined, and by Lemma 5 and Proposition 8 so is every
induced five-taxon tree `σ⁺(S)`. The root `ρ` lies on an edge `e` of `ψ⁻`; for each edge `e`, the
root lies on `e` if and only if the root of `ψ⁺(S)` lies on `e` for every set `S` of five taxa
such that `ψ⁻(S)` has the edge `e` (`rl_rootOn_iff`): if `ρ` is not on `e`, a quartet `Q`
distinguishing `e` [Steel 1992, Proposition 6] together with a taxon `x` such that the most recent
common ancestor of `S = Q ∪ {x}` is `ρ` gives such an `S` whose tree has its root `ρ` off `e`
(`rl_exists_five_not_rootOn`). So the location of the root is determined, hence `ψ⁺` (the rooting
of `ψ⁻` on that edge, `counts_reroot_unroot`), and the lengths of the edges at the root are read
off five-taxon trees having these edges (`rl_sameRootedMetricTree_of_clusters_eq`).

The paper's argument has a gap for a pendant edge `e`, which no quartet distinguishes; it is
repaired by another choice of the five taxa (`rl_exists_five_not_rootOn_pendant`; see the
docstring of `rl_exists_five_not_rootOn`).
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The root location for a pendant edge (used by `rl_exists_five_not_rootOn`, where the departure
from the paper is described). If the root of `σ` lies on the edge `A₁ | A₁ᶜ` of `σ⁻` and this is
not the pendant edge of the taxon `ℓ`, then some set `S` of five taxa containing `ℓ` induces a tree
`σ(S)` whose root does not lie on the pendant edge of `ℓ`: `S` consists of `ℓ`, another taxon `m`
of the child of the root containing `ℓ`, a taxon `r` of the other child, and two more taxa. -/
theorem rl_exists_five_not_rootOn_pendant (hX : 5 ≤ Fintype.card X) (σ : SpeciesTree X)
    {A₁ : Finset X} (hA₁ : A₁ ∈ σ.clusters) (hA₁c : A₁ᶜ ∈ σ.clusters) {ℓ : X}
    (hne : ({ℓ} : Finset X) ≠ A₁) (hne' : ({ℓ} : Finset X) ≠ A₁ᶜ) :
    ∃ S : Finset X, ∃ hS : S.Nonempty, #S = 5 ∧ ({ℓ} ∩ S).Nonempty ∧ ({ℓ}ᶜ ∩ S).Nonempty ∧
      ¬ (({ℓ} : Finset X).subtype (· ∈ S) ∈ (σ.restrict S hS).clusters ∧
        (({ℓ} : Finset X).subtype (· ∈ S))ᶜ ∈ (σ.restrict S hS).clusters) := by
  -- the child `R` of the root containing `ℓ`: it is not `{ℓ}`, so it contains another taxon `m`
  obtain ⟨R, hR, hRc, hℓR, hRℓ⟩ : ∃ R ∈ σ.clusters, Rᶜ ∈ σ.clusters ∧ ℓ ∈ R ∧ R ≠ {ℓ} := by
    by_cases h : ℓ ∈ A₁
    · exact ⟨A₁, hA₁, hA₁c, h, Ne.symm hne⟩
    · exact ⟨A₁ᶜ, hA₁c, by rwa [compl_compl], mem_compl.2 h, Ne.symm hne'⟩
  obtain ⟨m, hmR, hmℓ⟩ : ∃ m ∈ R, m ≠ ℓ := by
    by_contra hcon
    exact hRℓ (eq_singleton_iff_unique_mem.2 ⟨hℓR, fun y hy =>
      Classical.byContradiction fun hyℓ => hcon ⟨y, hy, hyℓ⟩⟩)
  -- a taxon `r` of the other child of the root
  obtain ⟨r, hr⟩ := σ.nonempty_of_mem _ hRc
  obtain ⟨S, hTS, hS5⟩ := rl_exists_five hX (T := {ℓ, m, r}) (card_le_three.trans (by norm_num))
  have hℓS : ℓ ∈ S := hTS (by simp)
  have hmS : m ∈ S := hTS (by simp)
  have hrS : r ∈ S := hTS (by simp)
  have hS : S.Nonempty := ⟨ℓ, hℓS⟩
  refine ⟨S, hS, hS5, ⟨ℓ, mem_inter.2 ⟨mem_singleton_self ℓ, hℓS⟩⟩,
    ⟨m, mem_inter.2 ⟨mem_compl.2 (by simpa using hmℓ), hmS⟩⟩, fun ⟨h1, h2⟩ => ?_⟩
  -- the root of `σ(S)` is the root of `σ`; it lies on the edge `(R ∩ S) | (Rᶜ ∩ S)`
  obtain ⟨hR1, hR2⟩ := rl_restrict_compl_mem σ hR hRc ⟨ℓ, mem_inter.2 ⟨hℓR, hℓS⟩⟩
    ⟨r, mem_inter.2 ⟨hr, hrS⟩⟩ hS
  -- which is not the pendant edge of `ℓ`
  rcases rl_eq_or_eq_compl (σ.restrict S hS).isHierarchy hR1 hR2 h1 h2 with h | h
  · -- `{ℓ} = R ∩ S` would contain `m`
    exact hmℓ (mem_singleton.1 ((rl_mem_iff_of_subtype_eq h hmS).2 hmR))
  · -- `{ℓ} = Rᶜ ∩ S` would not contain `ℓ`
    rw [← subtype_compl] at h
    exact mem_compl.1 ((rl_mem_iff_of_subtype_eq h hℓS).1 (mem_singleton_self ℓ)) hℓR

/-- The paper's root location (proof of Theorem 9). If the root `ρ` of `σ` lies on the edge
`A₁ | A₁ᶜ` of `σ⁻`, and `A | Aᶜ` is another edge of `σ⁻`, then some set `S` of five taxa meeting
`A` and `Aᶜ` (so that `σ⁻(S)` has the edge `A | Aᶜ`) induces a tree `σ(S)` whose root does not lie
on that edge. For an internal edge, as in the paper: for a quartet `Q` distinguishing the edge
[Steel 1992, Proposition 6], choose `x ∉ Q` so that the most recent common ancestor of
`S = Q ∪ {x}` is `ρ` (`S` meets `A₁` and `A₁ᶜ`); then `σ(S)` has root `ρ`, on the edge
`(A₁ ∩ S) | (A₁ᶜ ∩ S)`, which is not the edge of `A`, since only `A` separates the quartet as `A`
does.

Departure from the paper: the paper's quartet does not exist for a pendant edge `{ℓ} | X ∖ {ℓ}`
(no quartet distinguishes it), a gap in the paper's argument. For a pendant edge the set of five
taxa is chosen instead as `ℓ`, another taxon `m` of the child of the root containing `ℓ`, a taxon
`r` of the other child of the root, and two more taxa: the root of `σ(S)` is `ρ`, on the edge
separating `{ℓ, m}` from `r`, so not on the pendant edge of `ℓ`
(`rl_exists_five_not_rootOn_pendant`). -/
theorem rl_exists_five_not_rootOn (hX : 5 ≤ Fintype.card X) (σ : SpeciesTree X)
    {A₁ A : Finset X} (hA₁ : A₁ ∈ σ.clusters) (hA₁c : A₁ᶜ ∈ σ.clusters)
    (hA : A ∈ unroot σ.clusters) (hne : A ≠ A₁) (hne' : A ≠ A₁ᶜ) :
    ∃ S : Finset X, ∃ hS : S.Nonempty, #S = 5 ∧ (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧
      ¬ (A.subtype (· ∈ S) ∈ (σ.restrict S hS).clusters ∧
        (A.subtype (· ∈ S))ᶜ ∈ (σ.restrict S hS).clusters) := by
  obtain ⟨hAne, hAu⟩ := counts_nonempty_of_mem_unroot σ.isHierarchy hA
  have hAcne := rl_compl_nonempty hAu
  have hA₁u : A₁ ≠ univ := fun e => by
    have := σ.nonempty_of_mem _ hA₁c
    rw [e, compl_univ] at this
    exact not_nonempty_empty this
  by_cases hA1 : #A = 1
  · -- the pendant edge `{ℓ} | X ∖ {ℓ}`
    obtain ⟨ℓ, rfl⟩ := card_eq_one.1 hA1
    exact rl_exists_five_not_rootOn_pendant hX σ hA₁ hA₁c hne hne'
  by_cases hAc1 : #Aᶜ = 1
  · -- the pendant edge `X ∖ {ℓ} | {ℓ}`
    obtain ⟨ℓ, hℓ⟩ := card_eq_one.1 hAc1
    have h1 : ({ℓ} : Finset X) ≠ A₁ := by
      rw [← hℓ]
      intro e
      exact hne' (by rw [← e, compl_compl])
    have h2 : ({ℓ} : Finset X) ≠ A₁ᶜ := by
      rw [← hℓ]
      intro e
      exact hne (compl_injective e)
    obtain ⟨S, hS, hS5, hS1, hS2, hnot⟩ := rl_exists_five_not_rootOn_pendant hX σ hA₁ hA₁c h1 h2
    rw [← hℓ] at hS1 hS2 hnot
    rw [compl_compl] at hS2
    rw [subtype_compl, compl_compl] at hnot
    exact ⟨S, hS, hS5, hS2, hS1, fun ⟨h1, h2⟩ => hnot ⟨h2, h1⟩⟩
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
  obtain ⟨x, hxQ, hS1, hS2⟩ := rl_exists_insert_meets hX hQ4 (σ.nonempty_of_mem _ hA₁)
    (σ.nonempty_of_mem _ hA₁c)
  set S : Finset X := insert x {a, a', b, b'} with hSdef
  have hS : S.Nonempty := insert_nonempty _ _
  have hS5 : #S = 5 := by rw [hSdef, card_insert_of_notMem hxQ, hQ4]
  have haS : a ∈ S := by simp [hSdef]
  have ha'S : a' ∈ S := by simp [hSdef]
  have hbS : b ∈ S := by simp [hSdef]
  have hb'S : b' ∈ S := by simp [hSdef]
  refine ⟨S, hS, hS5, ⟨a, mem_inter.2 ⟨ha, haS⟩⟩, ⟨b, mem_inter.2 ⟨mem_compl.2 hb, hbS⟩⟩,
    fun ⟨h1, h2⟩ => ?_⟩
  -- `σ(S)` has root `ρ`, which lies on the edge `(A₁ ∩ S) | (A₁ᶜ ∩ S)`
  obtain ⟨hR1, hR2⟩ := rl_restrict_compl_mem σ hA₁ hA₁c hS1 hS2 hS
  -- a split of `σ⁻` inducing the split `(A ∩ S) | (Aᶜ ∩ S)` separates `aa'` from `bb'`, so it
  -- is `A`
  have hsep : ∀ C ∈ unroot σ.clusters, C.subtype (· ∈ S) = A.subtype (· ∈ S) → C = A := by
    intro C hC hCA
    have hmem : ∀ y ∈ S, y ∈ C ↔ y ∈ A := fun y hy => rl_mem_iff_of_subtype_eq hCA hy
    exact hQ C hC ((hmem a haS).2 ha) ((hmem a' ha'S).2 ha') (fun h => hb ((hmem b hbS).1 h))
      (fun h => hb' ((hmem b' hb'S).1 h))
  -- so if the root of `σ(S)` lay on the edge of `A`, that edge would be `A₁ | A₁ᶜ`
  rcases rl_eq_or_eq_compl (σ.restrict S hS).isHierarchy hR1 hR2 h1 h2 with h | h
  · exact hne (hsep A₁ (mem_unroot.2 (Or.inl ⟨hA₁, hA₁u⟩)) h.symm).symm
  · rw [← subtype_compl] at h
    exact hne' (hsep A₁ᶜ (compl_mem_unroot.2 (mem_unroot.2 (Or.inl ⟨hA₁, hA₁u⟩))) h.symm).symm

/-- The root location (proof of Theorem 9). Let `σ` be a species tree on at least five taxa whose
root lies on an edge of `σ⁻` (as for a binary tree), and let `A | Aᶜ` be an edge of `σ⁻`. The root
lies on this edge if and only if, for every set `S` of five taxa such that `σ⁻(S)` has the edge
`A | Aᶜ` (`S` meets `A` and `Aᶜ`), the root of `σ(S)` lies on it: if the root lies on the edge,
it is the root of each such `σ(S)` (`rl_restrict_compl_mem`); otherwise
`rl_exists_five_not_rootOn` gives an `S` whose root is elsewhere. -/
theorem rl_rootOn_iff (hX : 5 ≤ Fintype.card X) (σ : SpeciesTree X)
    (hσ : ∃ A₁ ∈ σ.clusters, A₁ᶜ ∈ σ.clusters) {A : Finset X} (hA : A ∈ unroot σ.clusters) :
    (A ∈ σ.clusters ∧ Aᶜ ∈ σ.clusters) ↔
      ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 → (A ∩ S).Nonempty → (Aᶜ ∩ S).Nonempty →
        A.subtype (· ∈ S) ∈ (σ.restrict S hS).clusters ∧
          (A.subtype (· ∈ S))ᶜ ∈ (σ.restrict S hS).clusters := by
  constructor
  · rintro ⟨h1, h2⟩ S hS - hAS hAcS
    exact rl_restrict_compl_mem σ h1 h2 hAS hAcS hS
  · intro h
    by_contra hnot
    obtain ⟨A₁, hA₁, hA₁c⟩ := hσ
    have hne : A ≠ A₁ := fun e => hnot ⟨e ▸ hA₁, e ▸ hA₁c⟩
    have hne' : A ≠ A₁ᶜ := fun e => hnot ⟨e ▸ hA₁c, by rw [e, compl_compl]; exact hA₁⟩
    obtain ⟨S, hS, hS5, hAS, hAcS, hS'⟩ := rl_exists_five_not_rootOn hX σ hA₁ hA₁c hA hne hne'
    exact hS' (h S hS hS5 hAS hAcS)

/-- **Theorem 9** (`thm:main`), `|X| ≥ 5`. The unrooted topological gene tree distribution `ℙ_{σ⁺}` arising
from the multispecies coalescent model for samples of one lineage per taxon determines the metric
species tree `σ⁺` provided `|X| ≥ 5`.

Departure from the paper: in locating the root, the paper's quartet distinguishing an edge does
not exist for a pendant edge; for a pendant edge the set of five taxa is chosen differently (see
`rl_exists_five_not_rootOn`). -/
theorem theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := by
  -- By Corollary 6, `σ⁻ = (ψ⁻, λ⁻)` is determined.
  have hU : σ.SameUnrootedMetricTree σ' := corollary6 σ σ' hσ hσ' h
  -- By Lemma 5 and Proposition 8, every induced five-taxon tree `σ⁺(S)` is determined.
  have h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS) := fun S hS hS5 =>
    proposition8 (by simpa using hS5) _ _ (SpeciesTree.restrict_isBinary hσ S hS)
      (SpeciesTree.restrict_isBinary hσ' S hS) (unrootedDist_restrict_eq h S hS)
  have h2 : 2 ≤ Fintype.card X := by omega
  -- The root `ρ` of `σ` lies on an edge `e = A | Aᶜ` of `ψ⁻`.
  obtain ⟨A, hA, hAc⟩ := rl_exists_compl_mem hσ h2
  have hAu : A ≠ univ := fun e => by
    have := σ.nonempty_of_mem _ hAc
    rw [e, compl_univ] at this
    exact not_nonempty_empty this
  have hAU : A ∈ unroot σ.clusters := mem_unroot.2 (Or.inl ⟨hA, hAu⟩)
  -- So the root of every `ψ⁺(S)` such that `ψ⁻(S)` has the edge `e` lies on `e`. These trees are
  -- the same for `σ'`, so the root of `σ'` lies on `e` too.
  have hA' : A ∈ σ'.clusters ∧ Aᶜ ∈ σ'.clusters := by
    refine (rl_rootOn_iff hX σ' (rl_exists_compl_mem hσ' h2) (hU.1 ▸ hAU)).2
      fun S hS hS5 hAS hAcS => ?_
    rw [← (h5 S hS hS5).1]
    exact (rl_rootOn_iff hX σ ⟨A, hA, hAc⟩ hAU).1 ⟨hA, hAc⟩ S hS hS5 hAS hAcS
  -- Thus `ψ⁺` is determined: it is `ψ⁻` rooted on the edge `e`.
  have hcl : σ.clusters = σ'.clusters := by
    rw [← counts_reroot_unroot σ.isHierarchy hA hAu hAc,
      ← counts_reroot_unroot σ'.isHierarchy hA'.1 hAu hA'.2, hU.1]
  -- The lengths of the edges not at the root are given by `λ⁻`, and those of the edges at the
  -- root are recovered from a five-taxon subset `S` such that `ψ⁺(S)` has these edges, by
  -- Lemma 5 and Proposition 8 again.
  exact rl_sameRootedMetricTree_of_clusters_eq hX hcl hU h5

/-- **Theorem 9** (`thm:main`), `|X| = 4`. If `|X| = 4`, `ℙ_{σ⁺}` determines only the unrooted metric species
tree `σ⁻`: two species trees have the same unrooted gene tree distribution exactly when they have
the same unrooted metric tree.

Proposition 3 gives the case `|X| = 4`: `ℙ_{σ⁺}` determines `σ⁻`; and it depends only on `σ⁻`
(the four-taxon distributions of Section 4.1), so it determines nothing more. -/
theorem theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' :=
  ⟨(proposition3 hX).1 σ σ' hσ hσ', four_unrootedDist_eq_of_sameUnrootedMetricTree hX hσ hσ'⟩

end ADR11
