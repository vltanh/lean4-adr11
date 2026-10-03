module

public import ADR11.Identifiability.FiveTaxaAnalysis
public import ADR11.MSC.MultiSample
public import ADR11.FourTaxa
public import ADR11.MSC.Relabel

/-!
# Proposition 11: nonbinary species trees

Proposition 3, Corollary 6, Propositions 7 and 8, Theorem 9 and Corollary 10 remain valid if the
species tree `σ⁺` is nonbinary.

The binary statements of Section 4 are the special cases of these (`ADR11.Identifiability`). The
proofs assemble the four- and five-taxon analyses with the marginalization of Lemma 5:

* Theorem 9 (`|X| ≥ 5`): by Lemma 5 the distribution of every induced 5-taxon tree is determined,
  hence (Proposition 8) every induced 5-taxon metric tree, hence the metric tree
  (`SpeciesTree.sameRootedMetricTree_of_restrict`, through rooted triples).
* Corollary 6: by Lemma 5 and the four-taxon case every induced quartet metric tree is determined,
  hence the unrooted metric tree (`SpeciesTree.sameUnrootedMetricTree_of_restrict`, after
  [Steel 1992]).
* Proposition 3: the four-taxon case gives `σ⁻`; the rooted trees `(((a,b),c),d)` and
  `(((a,b),d),c)` of Section 4.1 have the same distribution.
* Corollary 10: dropping lineages (Lemma 5's first step) reduces to at most two lineages per
  taxon, which is one lineage per leaf of the extended species tree, on at least five leaves.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Proposition 11** (Proposition 8 for nonbinary species trees). -/
theorem proposition11_proposition8 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' :=
  sameRootedMetricTree_of_unrootedDist_eq_five hX σ σ' h

/-- **Proposition 11** (Proposition 7 for nonbinary species trees). -/
theorem proposition11_proposition7 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.clusters = σ'.clusters :=
  (proposition11_proposition8 hX σ σ' h).1

/-- **Proposition 11** (Theorem 9 for nonbinary species trees, `|X| = 4`). -/
theorem proposition11_theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' :=
  unrootedDist_eq_iff_four hX σ σ'

/-- **Proposition 11** (Corollary 6 for nonbinary species trees). For any `X`, `ℙ_{σ⁺}` determines
`σ⁻`. -/
theorem proposition11_corollary6 (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' :=
  sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h

/-- Two rooted species trees on four taxa with the same unrooted gene tree distribution and
different rooted topologies: `(((a,b):1,c):1,d)` and `(((a,b):1,d):1,c)` (Section 4.1). -/
theorem exists_sameUnrootedDist_not_sameRooted_four :
    ∃ σ σ' : SpeciesTree (Fin 4), σ.IsBinary ∧ σ'.IsBinary ∧
      σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  let σ₁ := SpeciesTree.ofLengths (X := Fin 4) (hierarchyOf {{0, 1}, {0, 1, 2}}) (fun _ => 1) (by decide)
    (by decide) (by decide) (by decide) (fun _ _ _ _ => one_pos)
  let σ₂ := SpeciesTree.ofLengths (X := Fin 4) (hierarchyOf {{0, 1}, {0, 1, 3}}) (fun _ => 1) (by decide)
    (by decide) (by decide) (by decide) (fun _ _ _ _ => one_pos)
  let σ₃ := SpeciesTree.ofLengths (X := Fin 4) (hierarchyOf {{2, 3}, {0, 2, 3}}) (fun _ => 1) (by decide)
    (by decide) (by decide) (by decide) (fun _ _ _ _ => one_pos)
  let σ₄ := SpeciesTree.ofLengths (X := Fin 4) (hierarchyOf {{2, 3}, {1, 2, 3}}) (fun _ => 1) (by decide)
    (by decide) (by decide) (by decide) (fun _ _ _ _ => one_pos)
  let σ₅ := SpeciesTree.ofLengths (X := Fin 4) (hierarchyOf {{0, 1}, {2, 3}}) (fun _ => 1 / 2) (by decide)
    (by decide) (by decide) (by decide) (fun _ _ _ _ => by norm_num)
  have h01 : ¬ #({0, 1} : Finset (Fin 4)) ≤ 1 := by decide
  have h23 : ¬ #({2, 3} : Finset (Fin 4)) ≤ 1 := by decide
  have e₁ : σ₁.length {0, 1} = 1 := by
    show (if #({0, 1} : Finset (Fin 4)) ≤ 1 then (1 : ℝ) else 1) = 1
    rw [if_neg h01]
  have e₂ : σ₂.length {0, 1} = 1 := by
    show (if #({0, 1} : Finset (Fin 4)) ≤ 1 then (1 : ℝ) else 1) = 1
    rw [if_neg h01]
  have e₃ : σ₃.length {2, 3} = 1 := by
    show (if #({2, 3} : Finset (Fin 4)) ≤ 1 then (1 : ℝ) else 1) = 1
    rw [if_neg h23]
  have e₄ : σ₄.length {2, 3} = 1 := by
    show (if #({2, 3} : Finset (Fin 4)) ≤ 1 then (1 : ℝ) else 1) = 1
    rw [if_neg h23]
  have e₅ : σ₅.length {0, 1} + σ₅.length {2, 3} = 1 := by
    show (if #({0, 1} : Finset (Fin 4)) ≤ 1 then (1 : ℝ) else 1 / 2) +
      (if #({2, 3} : Finset (Fin 4)) ≤ 1 then (1 : ℝ) else 1 / 2) = 1
    rw [if_neg h01, if_neg h23]
    norm_num
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

/-- **Proposition 11** (Proposition 3 for nonbinary species trees). For `|X| = 4`, `σ⁻` is
identifiable from `ℙ_{σ⁺}`, but `σ⁺` is not. -/
theorem proposition11_proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.unrootedDist id = σ'.unrootedDist id →
        σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.unrootedDist id = σ'.unrootedDist id ∧
        ¬ σ.SameRootedMetricTree σ' := by
  refine ⟨fun σ σ' h => (proposition11_theorem9_four hX σ σ').1 h, ?_⟩
  obtain ⟨τ, τ', -, -, hd, hn⟩ := exists_sameUnrootedDist_not_sameRooted_four
  let e : Fin 4 ≃ X := (Fintype.equivFinOfCardEq hX).symm
  exact ⟨τ.relabel e, τ'.relabel e, (SpeciesTree.unrootedDist_relabel_eq_iff τ τ' e).2 hd,
    fun hs => hn ((SpeciesTree.sameRootedMetricTree_relabel_iff τ τ' e).1 hs)⟩

/-- **Proposition 11** (Theorem 9 for nonbinary species trees, `|X| ≥ 5`). -/
theorem proposition11_theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' :=
  SpeciesTree.sameRootedMetricTree_of_restrict hX σ σ' fun S hS hS5 =>
    proposition11_proposition8 (by simpa using hS5) _ _ (unrootedDist_restrict_eq h S hS)

/-- The fibre of `Sigma.fst` over `x` in `Σ x, Fin (n x)` has `n x` elements. -/
theorem card_filter_sigma_fst (n : X → ℕ) (x : X) :
    #(univ.filter fun p : (Σ y, Fin (n y)) => p.1 = x) = n x := by
  have : (univ.filter fun p : (Σ y, Fin (n y)) => p.1 = x) =
      (univ : Finset (Fin (n x))).map ⟨Sigma.mk x, sigma_mk_injective⟩ := by
    ext ⟨y, i⟩
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨i, rfl⟩
    · rintro ⟨j, hj⟩
      exact (Sigma.mk.inj_iff.1 hj).1.symm
  rw [this, card_map, card_univ, Fintype.card_fin]

/-- Keeping at most two lineages of each taxon. -/
def keepTwo (ℓ : X → ℕ) : (Σ x, Fin (min (ℓ x) 2)) ↪ (Σ x, Fin (ℓ x)) where
  toFun p := ⟨p.1, Fin.castLE (min_le_left _ _) p.2⟩
  inj' := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    simp only [heq_eq_eq, Fin.castLE_inj] at h
    rw [h]

/-- **Proposition 11** (Corollary 10 for nonbinary species trees). -/
theorem proposition11_corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := by
  -- keep at most two lineages per taxon
  set s' : (Σ x, Fin (min (ℓ x) 2)) → X := Sigma.fst with hs'def
  have hcomp : (Sigma.fst : (Σ x, Fin (ℓ x)) → X) ∘ keepTwo ℓ = s' := rfl
  have h' : σ.unrootedDist s' = σ'.unrootedDist s' := by
    funext T'
    rw [← hcomp, σ.unrootedDist_comp_embedding, σ'.unrootedDist_comp_embedding, h]
  have hsurj : Function.Surjective s' := fun x =>
    ⟨⟨x, ⟨0, lt_min (hℓ x) (by norm_num)⟩⟩, rfl⟩
  have hfib : ∀ x, #(univ.filter fun l => s' l = x) = min (ℓ x) 2 :=
    card_filter_sigma_fst (fun y => min (ℓ y) 2)
  have h2 : ∀ x, #(univ.filter fun l => s' l = x) ≤ 2 := fun x => by
    rw [hfib]; exact min_le_right _ _
  -- the extended species trees
  have hext : (σ.extend s' hsurj).unrootedDist id = (σ'.extend s' hsurj).unrootedDist id := by
    have e1 : ∀ τ : SpeciesTree X, (τ.extend s' hsurj).unrootedDist id = τ.unrootedDist s' := by
      intro τ
      funext T
      unfold SpeciesTree.unrootedDist
      simp_rw [← τ.rootedDist_extend hsurj h2]
    rw [e1, e1, h']
  have hcardX : 3 ≤ Fintype.card X := by omega
  have hcardL : 5 ≤ Fintype.card (Σ x, Fin (min (ℓ x) 2)) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    have hone : ∀ x, 1 ≤ min (ℓ x) 2 := fun x => le_min (hℓ x) (by norm_num)
    rcases hcond with ⟨h4, x, hx⟩ | ⟨h3, x, y, hxy, hx, hy⟩
    · have hx2 : min (ℓ x) 2 = 2 := min_eq_right hx
      calc 5 ≤ ∑ z ∈ univ.erase x, 1 + 2 := by
              rw [sum_const, card_erase_of_mem (mem_univ x), card_univ, smul_eq_mul, mul_one]
              omega
        _ ≤ ∑ z ∈ univ.erase x, min (ℓ z) 2 + min (ℓ x) 2 := by
              rw [hx2]; exact Nat.add_le_add_right (sum_le_sum fun z _ => hone z) 2
        _ = ∑ z, min (ℓ z) 2 := sum_erase_add _ _ (mem_univ x)
    · have hx2 : min (ℓ x) 2 = 2 := min_eq_right hx
      have hy2 : min (ℓ y) 2 = 2 := min_eq_right hy
      have hyx : y ∈ univ.erase x := mem_erase.2 ⟨hxy.symm, mem_univ y⟩
      calc 5 ≤ ∑ z ∈ (univ.erase x).erase y, 1 + 2 + 2 := by
              rw [sum_const, card_erase_of_mem hyx, card_erase_of_mem (mem_univ x), card_univ,
                smul_eq_mul, mul_one]
              omega
        _ ≤ ∑ z ∈ (univ.erase x).erase y, min (ℓ z) 2 + min (ℓ y) 2 + min (ℓ x) 2 := by
              rw [hx2, hy2]
              exact Nat.add_le_add_right (Nat.add_le_add_right (sum_le_sum fun z _ => hone z) 2) 2
        _ = ∑ z, min (ℓ z) 2 := by
              rw [sum_erase_add _ _ hyx, sum_erase_add _ _ (mem_univ x)]
  have hsame := proposition11_theorem9 hcardL _ _ hext
  obtain ⟨hc, hlen⟩ := SpeciesTree.sameRootedMetricTree_of_extend (by omega) σ σ' hsurj hsame
  refine ⟨hc, fun x hx => hlen x ?_⟩
  rw [hfib, min_eq_right hx]

end ADR11
