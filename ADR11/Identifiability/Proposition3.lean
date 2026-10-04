module

public import ADR11.Identifiability.FourTaxaAnalysis
public import ADR11.FourTaxa

/-!
# Proposition 3: four taxa

## Main results

* `fourTaxa_recovery`: for any binary 4-taxon species tree, the most probable unrooted gene tree
  has the topology of the unrooted species tree, and the internal edge length of the unrooted
  species tree is `-log((3/2)(1 - ℙ(T)))`.
* `proposition3`: for `|X| = 4`, `σ⁻` is identifiable from `ℙ_σ`, but `σ⁺` is not.
* `f1_exists_split_of_isBinary`, `f1_mem_unroot_iff_of_split`: a binary species tree on four
  taxa has a nontrivial split `A | Aᶜ` with `#A = 2`, and this split determines its unrooted
  topology.
* `f1_exists_sameUnrootedDist_not_sameRooted_four`: two of the rooted species trees of
  Section 4.1 with the same unrooted gene tree distribution, `(((a,b),c),d)` and `(((a,b),d),c)`.

## Proof of Proposition 3 (the paper's, Section 4.1)

`σ⁻` is identifiable: a binary species tree `σ` on four taxa has exactly one nontrivial split
`A | Aᶜ`, with `#A = 2`. By the four-taxon distributions (`fourTaxa_recovery`), the gene tree with
that split is the strictly most probable one, so a second binary species tree `σ'` with the same
distribution has the same split (the strictly most probable gene tree is unique), hence the same
unrooted topology; the internal edge length of both is `-log((3/2)(1 - ℙ(T)))` for that gene tree
`T`. `σ⁺` is not identifiable: the five rooted species trees listed in Section 4.1
(`fourTaxa_sameDistribution`) have the same distribution, and two of them have different rooted
topologies.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Section 4.1: for any binary species tree on four taxa, with nontrivial split `A | Aᶜ` of its
unrooted topology, the unrooted gene tree `T` with that split is strictly the most probable, and
the internal edge length of `σ⁻` is `-log((3/2)(1 - ℙ(T)))`. -/
theorem fourTaxa_recovery (hX : Fintype.card X = 4) (σ : SpeciesTree X) (hσ : σ.IsBinary)
    (A : Finset X) (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    (∀ B : Finset X, #B = 2 → B ≠ A → B ≠ Aᶜ →
        σ.unrootedDist id (treeOfClusters {B}) < σ.unrootedDist id (treeOfClusters {A})) ∧
      σ.unrootedLength A = -log (3 / 2 * (1 - σ.unrootedDist id (treeOfClusters {A}))) :=
  four_recovery hX σ hσ hA hA2

/-- A binary species tree on four taxa has a nontrivial split `A | Aᶜ` with `#A = 2`: the two
children of the root have two taxa each, or one and three taxa, and then the child with three
taxa has a child with two. -/
theorem f1_exists_split_of_isBinary (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (hσ : σ.IsBinary) : ∃ A ∈ unroot σ.clusters, #A = 2 := by
  -- a cluster with two taxa is a side of a split
  suffices h : ∃ A ∈ σ.clusters, #A = 2 by
    obtain ⟨A, hA, hA2⟩ := h
    refine ⟨A, classify_mem_unroot.2 (Or.inl ⟨hA, fun hu => ?_⟩), hA2⟩
    rw [hu, card_univ, hX] at hA2
    omega
  -- the two children of a cluster with `n ≥ 2` taxa have `n` taxa together, at least one each
  have hsplit : ∀ D ∈ σ.clusters, 2 ≤ #D → ∃ B ∈ σ.clusters, ∃ C ∈ σ.clusters,
      #B + #C = #D ∧ 1 ≤ #B ∧ 1 ≤ #C := by
    intro D hD hD2
    obtain ⟨B, hB, C, hC, hBC, hBCD⟩ := hσ D hD hD2
    exact ⟨B, hB, C, hC, by rw [← card_union_of_disjoint hBC, hBCD],
      (σ.nonempty_of_mem B hB).card_pos, (σ.nonempty_of_mem C hC).card_pos⟩
  -- a cluster with three taxa has a child with two
  have h3 : ∀ D ∈ σ.clusters, #D = 3 → ∃ A ∈ σ.clusters, #A = 2 := by
    intro D hD hD3
    obtain ⟨B, hB, C, hC, hBC, hB1, hC1⟩ := hsplit D hD (by omega)
    rcases (by omega : #B = 2 ∨ #C = 2) with h | h
    · exact ⟨B, hB, h⟩
    · exact ⟨C, hC, h⟩
  obtain ⟨B, hB, C, hC, hBC, hB1, hC1⟩ :=
    hsplit univ σ.univ_mem (by rw [card_univ, hX]; omega)
  rw [card_univ, hX] at hBC
  rcases (by omega : #B = 2 ∨ #B = 3 ∨ #C = 3) with h | h | h
  · exact ⟨B, hB, h⟩
  · exact h3 B hB h
  · exact h3 C hC h

/-- On four taxa, the unrooted topology of a species tree with the nontrivial split `A | Aᶜ`
(`#A = 2`) consists of this split and the trivial splits. -/
theorem f1_mem_unroot_iff_of_split (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    {A : Finset X} (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) (B : Finset X) :
    B ∈ unroot σ.clusters ↔ #B = 1 ∨ #B = 3 ∨ B = A ∨ B = Aᶜ := by
  have h3 : Fintype.card X - 1 = 3 := by rw [hX]
  rw [classify_mem_unroot_iff (Or.inl hX) σ B, h3, mem_filter, mem_filter]
  constructor
  · rintro (h | h | ⟨hB, hB2⟩ | ⟨hB, hB2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (classify_eq_or_eq_compl_of_card_two hX σ hA hB hA2 hB2))
    · rcases classify_eq_or_eq_compl_of_card_two hX σ hA hB hA2 hB2 with h | h
      · exact Or.inr (Or.inr (Or.inr (by rw [← h, compl_compl])))
      · exact Or.inr (Or.inr (Or.inl (compl_injective h)))
  · rintro (h | h | rfl | rfl)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨hA, hA2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by rwa [compl_compl], by rw [compl_compl, hA2]⟩))

/-- Section 4.1: two of the five rooted species trees `(((a,b):x,c):y₁,d)`, `(((a,b):x,d):y₂,c)`,
`(((c,d):x,a):y₃,b)`, `(((c,d):x,b):y₄,a)` and `((a,b):z,(c,d):x-z)`, which produce the same
unrooted gene tree distribution (`fourTaxa_sameDistribution`, here with `x = 1`, `yᵢ = 1`,
`z = 1/2`), namely the binary trees `(((a,b),c),d)` and `(((a,b),d),c)`, have different rooted
topologies. -/
theorem f1_exists_sameUnrootedDist_not_sameRooted_four :
    ∃ σ σ' : SpeciesTree (Fin 4), σ.IsBinary ∧ σ'.IsBinary ∧
      σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  let σ₁ := SpeciesTree.ofLengths (X := Fin 4) (hierarchyOf {{0, 1}, {0, 1, 2}}) (fun _ => 1)
    (by decide) (by decide) (by decide) (by decide) (fun _ _ _ _ => one_pos)
  let σ₂ := SpeciesTree.ofLengths (X := Fin 4) (hierarchyOf {{0, 1}, {0, 1, 3}}) (fun _ => 1)
    (by decide) (by decide) (by decide) (by decide) (fun _ _ _ _ => one_pos)
  let σ₃ := SpeciesTree.ofLengths (X := Fin 4) (hierarchyOf {{2, 3}, {0, 2, 3}}) (fun _ => 1)
    (by decide) (by decide) (by decide) (by decide) (fun _ _ _ _ => one_pos)
  let σ₄ := SpeciesTree.ofLengths (X := Fin 4) (hierarchyOf {{2, 3}, {1, 2, 3}}) (fun _ => 1)
    (by decide) (by decide) (by decide) (by decide) (fun _ _ _ _ => one_pos)
  let σ₅ := SpeciesTree.ofLengths (X := Fin 4) (hierarchyOf {{0, 1}, {2, 3}}) (fun _ => 1 / 2)
    (by decide) (by decide) (by decide) (by decide) (fun _ _ _ _ => by norm_num)
  have h01 : ¬ #({0, 1} : Finset (Fin 4)) ≤ 1 := by decide
  have h23 : ¬ #({2, 3} : Finset (Fin 4)) ≤ 1 := by decide
  have e₁ : σ₁.length {0, 1} = 1 := by
    show (if #({0, 1} : Finset (Fin 4)) ≤ 1 then (1 : ℝ) else 1) = 1
    rw [ite_eq_right h01]
  have e₂ : σ₂.length {0, 1} = 1 := by
    show (if #({0, 1} : Finset (Fin 4)) ≤ 1 then (1 : ℝ) else 1) = 1
    rw [ite_eq_right h01]
  have e₃ : σ₃.length {2, 3} = 1 := by
    show (if #({2, 3} : Finset (Fin 4)) ≤ 1 then (1 : ℝ) else 1) = 1
    rw [ite_eq_right h23]
  have e₄ : σ₄.length {2, 3} = 1 := by
    show (if #({2, 3} : Finset (Fin 4)) ≤ 1 then (1 : ℝ) else 1) = 1
    rw [ite_eq_right h23]
  have e₅ : σ₅.length {0, 1} + σ₅.length {2, 3} = 1 := by
    show (if #({0, 1} : Finset (Fin 4)) ≤ 1 then (1 : ℝ) else 1 / 2) +
      (if #({2, 3} : Finset (Fin 4)) ≤ 1 then (1 : ℝ) else 1 / 2) = 1
    rw [ite_eq_right h01, ite_eq_right h23]
    norm_num
  -- the five trees of Section 4.1 have the same distribution
  have key := fourTaxa_sameDistribution σ₁ σ₂ σ₃ σ₄ σ₅ rfl rfl rfl rfl rfl
    (e₂.trans e₁.symm) (e₃.trans e₁.symm) (e₄.trans e₁.symm) (e₅.trans e₁.symm)
  have hb₁ : ∀ A ∈ (hierarchyOf {{0, 1}, {0, 1, 2}} : Finset (Finset (Fin 4))), 2 ≤ #A →
      ∃ B ∈ (hierarchyOf {{0, 1}, {0, 1, 2}} : Finset (Finset (Fin 4))),
        ∃ C ∈ (hierarchyOf {{0, 1}, {0, 1, 2}} : Finset (Finset (Fin 4))),
          Disjoint B C ∧ B ∪ C = A := by
    decide
  have hb₂ : ∀ A ∈ (hierarchyOf {{0, 1}, {0, 1, 3}} : Finset (Finset (Fin 4))), 2 ≤ #A →
      ∃ B ∈ (hierarchyOf {{0, 1}, {0, 1, 3}} : Finset (Finset (Fin 4))),
        ∃ C ∈ (hierarchyOf {{0, 1}, {0, 1, 3}} : Finset (Finset (Fin 4))),
          Disjoint B C ∧ B ∪ C = A := by
    decide
  have hne : (hierarchyOf {{0, 1}, {0, 1, 2}} : Finset (Finset (Fin 4))) ≠
      hierarchyOf {{0, 1}, {0, 1, 3}} := by
    decide
  exact ⟨σ₁, σ₂, hb₁, hb₂, key.1.symm, fun hs => hne hs.1⟩

/-- **Proposition 3** (`prop:4taxa`). For `|X| = 4` taxa, `σ⁻` is identifiable from `ℙ_{σ⁺}`, but `σ⁺` is not.

Proof (the paper's, Section 4.1): each of two binary species trees `σ`, `σ'` with the same
distribution has exactly one nontrivial split (`f1_exists_split_of_isBinary`), whose gene tree is
the strictly most probable one (`fourTaxa_recovery`); so the two splits agree, hence the unrooted
topologies (`f1_mem_unroot_iff_of_split`), and the internal edge lengths agree since both are
`-log((3/2)(1 - ℙ(T)))` for the most probable gene tree `T`. Two of the rooted trees of
Section 4.1 with the same distribution have different rooted topologies
(`f1_exists_sameUnrootedDist_not_sameRooted_four`, relabelled to `X`). -/
theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
        σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
        σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  refine ⟨fun σ σ' hσ hσ' h => ?_, ?_⟩
  · -- `σ⁻` is identifiable: the nontrivial splits `A | Aᶜ` of `σ⁻` and `A' | A'ᶜ` of `σ'⁻`
    obtain ⟨A, hA, hA2⟩ := f1_exists_split_of_isBinary hX σ hσ
    obtain ⟨A', hA', hA'2⟩ := f1_exists_split_of_isBinary hX σ' hσ'
    obtain ⟨hmax, hlen⟩ := fourTaxa_recovery hX σ hσ A hA hA2
    obtain ⟨hmax', -⟩ := fourTaxa_recovery hX σ' hσ' A' hA' hA'2
    -- the topology of `σ⁻` and of `σ'⁻` is that of the most probable gene tree
    have hAσ' : A ∈ unroot σ'.clusters := by
      by_cases h1 : A' = A
      · rwa [h1] at hA'
      by_cases h2 : A' = Aᶜ
      · rw [h2] at hA'
        exact compl_mem_unroot.1 hA'
      exfalso
      have hlt := hmax A' hA'2 h1 h2
      have hlt' := hmax' A hA2 (fun e => h1 e.symm) (fun e => h2 (by rw [e, compl_compl]))
      rw [h] at hlt
      exact lt_asymm hlt hlt'
    -- the internal edge length is `-log((3/2)(1 - ℙ(T)))` for the most probable gene tree `T`
    obtain ⟨-, hlen'⟩ := fourTaxa_recovery hX σ' hσ' A hAσ' hA2
    refine ⟨?_, fun C hC hC2 hCc2 => ?_⟩
    · ext B
      rw [f1_mem_unroot_iff_of_split hX σ hA hA2, f1_mem_unroot_iff_of_split hX σ' hAσ' hA2]
    · have hC2' : #C = 2 := by
        have := card_compl C
        rw [hX] at this
        omega
      rcases classify_eq_or_eq_compl_of_card_two hX σ hA hC hA2 hC2' with rfl | rfl
      · rw [hlen, hlen', h]
      · rw [SpeciesTree.unrootedLength_compl, SpeciesTree.unrootedLength_compl, hlen, hlen', h]
  · -- `σ⁺` is not identifiable
    obtain ⟨τ, τ', hb, hb', hd, hn⟩ := f1_exists_sameUnrootedDist_not_sameRooted_four
    let e : Fin 4 ≃ X := (Fintype.equivFinOfCardEq hX).symm
    exact ⟨τ.relabel e, τ'.relabel e, (τ.isBinary_relabel_iff e).2 hb,
      (τ'.isBinary_relabel_iff e).2 hb', (SpeciesTree.unrootedDist_relabel_eq_iff τ τ' e).2 hd,
      fun hs => hn ((SpeciesTree.sameRootedMetricTree_relabel_iff τ τ' e).1 hs)⟩

end ADR11
