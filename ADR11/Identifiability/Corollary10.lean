module

public import ADR11.MSC.MultiSample
public import ADR11.Identifiability.Theorem9

/-!
# Corollary 10: several lineages per taxon

With `ℓ_x > 0` lineages sampled from each taxon `x`, the unrooted gene tree distribution
determines the rooted species tree, its internal edge lengths, and the pendant edge lengths of
the taxa sampled at least twice, provided `|X| ≥ 4` and some `ℓ_x ≥ 2`, or `|X| = 3` and two of the
`ℓ_x` are at least `2`.

## Proof (the paper's)

"We may assume all `ℓ_i` are either 1 or 2, by marginalizing over any additional individuals
sampled": dropping lineages (`SpeciesTree.unrootedDist_comp_embedding`, along `c10_keepTwo`).
"Construct an extended species tree" (`SpeciesTree.extend`, on at least five leaves,
`c10_five_le_card`): "a coalescent process on the extended `ℓ`-taxon tree with one sample per leaf
leads to exactly the same distribution of topological gene trees as the multiple-sample process
on the original species tree" (`SpeciesTree.rootedDist_extend`). "Applying Theorem 9 to the
extended tree, we obtain the result" (`SpeciesTree.sameRootedMetricTree_of_extend`).

The argument is written once, in `c10_of_theorem9`, for a class of species trees that the
extension preserves and for which Theorem 9 holds: binary species trees for `corollary10`
(`SpeciesTree.extend_isBinary`), all species trees for Proposition 11.

## Main results

* `c10_of_theorem9`: the proof of Corollary 10, from Theorem 9 for a class of species trees.
* `corollary10`: Corollary 10.
-/

@[expose] public section

namespace ADR11

open Finset

universe u

section General

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- The fibre of `Sigma.fst` over `x` in `Σ x, Fin (n x)` has `n x` elements. -/
theorem c10_card_filter_sigma_fst (n : X → ℕ) (x : X) :
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
def c10_keepTwo (ℓ : X → ℕ) : (Σ x, Fin (min (ℓ x) 2)) ↪ (Σ x, Fin (ℓ x)) where
  toFun p := ⟨p.1, Fin.castLE (min_le_left _ _) p.2⟩
  inj' := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    simp only [heq_eq_eq, Fin.castLE_inj] at h
    rw [h]

/-- Under the hypotheses of Corollary 10, the extended species tree, with one leaf for each of at
most two lineages of each taxon, has at least five leaves. -/
theorem c10_five_le_card (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y)) :
    5 ≤ Fintype.card (Σ x, Fin (min (ℓ x) 2)) := by
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

/-- The proof of Corollary 10, for a class `P` of species trees that is preserved by the
extension of a species tree (when at most two lineages are sampled from each taxon) and for which
Theorem 9 holds (`thm9`: on at least five taxa, the unrooted gene tree distribution with one
lineage per taxon determines the metric species tree in `P`). Then, for species trees in `P`,
the distribution with `ℓ_x` lineages sampled from each taxon `x` determines the rooted species
tree, its internal edge lengths, and the pendant edge length of every taxon `x` with `ℓ_x > 1`. -/
theorem c10_of_theorem9 {P : ∀ {Y : Type u} [Fintype Y] [DecidableEq Y], SpeciesTree Y → Prop}
    (hP : ∀ {L : Type u} [Fintype L] [DecidableEq L] (τ : SpeciesTree X) (s : L → X)
      (hs : Function.Surjective s), (∀ x, #(univ.filter fun l => s l = x) ≤ 2) → P τ →
        P (τ.extend s hs))
    (thm9 : ∀ {Y : Type u} [Fintype Y] [DecidableEq Y], 5 ≤ Fintype.card Y →
      ∀ τ τ' : SpeciesTree Y, P τ → P τ' → τ.unrootedDist id = τ'.unrootedDist id →
        τ.SameRootedMetricTree τ')
    (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X) (hσ : P σ) (hσ' : P σ')
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := by
  -- We may assume all `ℓ_x` are `1` or `2`, by marginalizing over the additional lineages.
  set s' : (Σ x, Fin (min (ℓ x) 2)) → X := Sigma.fst
  have hcomp : (Sigma.fst : (Σ x, Fin (ℓ x)) → X) ∘ c10_keepTwo ℓ = s' := rfl
  have h' : σ.unrootedDist s' = σ'.unrootedDist s' := by
    funext T'
    rw [← hcomp, σ.unrootedDist_comp_embedding, σ'.unrootedDist_comp_embedding, h]
  have hsurj : Function.Surjective s' := fun x =>
    ⟨⟨x, ⟨0, lt_min (hℓ x) (by norm_num)⟩⟩, rfl⟩
  have hfib : ∀ x, #(univ.filter fun l => s' l = x) = min (ℓ x) 2 :=
    c10_card_filter_sigma_fst (fun y => min (ℓ y) 2)
  have h2 : ∀ x, #(univ.filter fun l => s' l = x) ≤ 2 := fun x => by
    rw [hfib]
    exact min_le_right _ _
  -- The extended species trees: the coalescent with one lineage per leaf of the extended tree
  -- gives the same gene tree distribution as the multiple-sample process on the species tree.
  have hext : (σ.extend s' hsurj).unrootedDist id = (σ'.extend s' hsurj).unrootedDist id := by
    have e1 : ∀ τ : SpeciesTree X, (τ.extend s' hsurj).unrootedDist id = τ.unrootedDist s' := by
      intro τ
      funext T
      unfold SpeciesTree.unrootedDist
      simp_rw [← τ.rootedDist_extend hsurj h2]
    rw [e1, e1, h']
  -- Applying Theorem 9 to the extended trees, we obtain the result.
  have hsame := thm9 (c10_five_le_card ℓ hℓ hcond) _ _ (hP σ s' hsurj h2 hσ)
    (hP σ' s' hsurj h2 hσ') hext
  have hcardX : 2 ≤ Fintype.card X := by
    rcases hcond with ⟨h4, -⟩ | ⟨h3, -⟩ <;> omega
  obtain ⟨hc, hlen⟩ := SpeciesTree.sameRootedMetricTree_of_extend hcardX σ σ' hsurj hsame
  refine ⟨hc, fun x hx => hlen x ?_⟩
  rw [hfib, min_eq_right hx]

end General

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Corollary 10** (`cor:intra`). Consider the distribution of unrooted topological gene trees under the
multispecies coalescent with `ℓ_x > 0` lineages sampled from each taxon `x` (lineages
`(x, k)`, `k < ℓ_x`). Suppose that either `|X| ≥ 4` and some `ℓ_x ≥ 2`, or `|X| = 3` and at least
two of the `ℓ_x` are `≥ 2`. Then the gene tree distribution determines the species tree's rooted
topology, its internal edge lengths, and the length of the pendant edge of every taxon `x` with
`ℓ_x > 1`.

The paper's proof (`c10_of_theorem9`), with Theorem 9 applied to the extended species trees, which
are binary (`SpeciesTree.extend_isBinary`). -/
theorem corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X) (hσ : σ.IsBinary) (hσ' : σ'.IsBinary)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} :=
  c10_of_theorem9 (P := fun τ => τ.IsBinary)
    (fun _ _ hs h2 hτ => SpeciesTree.extend_isBinary hτ hs h2)
    (fun hY τ τ' hτ hτ' hd => theorem9 hY τ τ' hτ hτ' hd) ℓ hℓ hcond σ σ' hσ hσ' h

end ADR11
