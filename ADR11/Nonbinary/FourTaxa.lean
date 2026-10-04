module

public import ADR11.Identifiability.FourTaxaAnalysis
public import ADR11.Nonbinary

/-!
# Four taxa, binary or not (Section 5)

Section 5 (l.709–711) obtains the unrooted gene tree probabilities of the nonbinary species trees
on four taxa as limits of the formulas of Section 4.1: `((a,b):x,c,d)` is the limit `y → 0` of the
caterpillar `(((a,b):x,c):y,d)`, whose distribution does not depend on `y`, and `((a,b,c):y,d)` and
`(a,b,c,d)` are the limits `x → 0` (and `y → 0`), with probability `1/3` for each binary unrooted
gene tree (`lim_fourTaxa_quartets`, behind `section5_fourTaxa`). Permuting labels gives the other
labellings (l.319). "These observations lead to the conclusion, as in the binary case, that 4-taxon
unrooted gene tree probabilities identify the unrooted (possibly unresolved) species tree" (l.711):
Proposition 3 holds for nonbinary species trees.

## Main results

* `n4_unrootedDist_of_mem`, `n4_unrootedDist_of_ne`, `four_unrootedDist_of_star`: the gene tree
  distribution of any species tree on four taxa, in terms of its unrooted metric tree: by
  Section 4.1 for a binary species tree (`ADR11.Identifiability.FourTaxaAnalysis`), by Section 5
  for a nonbinary one.
* `unrootedDist_eq_iff_four`: on four taxa the distribution of a species tree, binary or not,
  determines, and is determined by, its unrooted metric tree `σ⁻`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Section 5 on `Fin 4`, with permuted labels -/

/-- A species tree whose clusters satisfy the binary condition is binary. -/
private theorem n4_isBinary_of_clusters {τ : SpeciesTree (Fin 4)} {H : Finset (Finset (Fin 4))}
    (hc : τ.clusters = H)
    (hH : ∀ A ∈ H, 2 ≤ #A → ∃ B ∈ H, ∃ C ∈ H, Disjoint B C ∧ B ∪ C = A) : τ.IsBinary := by
  intro A hA h2
  rw [hc] at hA ⊢
  exact hH A hA h2

/-- The unrooted length of `{0, 1}` when `C` is the only cluster among `{0, 1}` and `{2, 3}`. -/
private theorem n4_unrootedLength (τ : SpeciesTree (Fin 4)) {C : Finset (Fin 4)}
    (hS : τ.clusters.filter (fun D => D ≠ univ ∧ (D = {0, 1} ∨ D = ({0, 1} : Finset (Fin 4))ᶜ)) =
      {C}) :
    τ.unrootedLength {0, 1} = τ.length C := by
  unfold SpeciesTree.unrootedLength
  rw [hS, sum_singleton]

/-- Permuting labels (l.319): the probability of `T` under `τ` is that of the relabelled tree
under the relabelled species tree. -/
private theorem n4_dist_relabel (τ : SpeciesTree (Fin 4)) (g : Fin 4 ≃ Fin 4)
    {T T' : Finset (Finset (Fin 4))} (h : relabelFamily g T = T') :
    τ.unrootedDist id T = (τ.relabel g).unrootedDist id T' := by
  rw [← h, SpeciesTree.unrootedDist_relabel]

/-- The permutation `(a c)(b d)`, which sends `((c,d),a,b)` to `((a,b),c,d)`. -/
private def n4_perm : Fin 4 ≃ Fin 4 := (Equiv.swap 0 2).trans (Equiv.swap 1 3)

/-- **Section 5 on `Fin 4`, one internal edge.** A nonbinary species tree with the unrooted topology
`U4 1 = AB|CD` is `((a,b):t,c,d)` or `((c,d):t,a,b)`. The first is the limit `y → 0` of the
caterpillar `(((a,b):t,c):y,d)` (`lim_fourTaxa_quartets`); the second is the first with the labels
permuted by `(a c)(b d)`. -/
private theorem n4_U4_one (τ : SpeciesTree (Fin 4)) (hτ : ¬ τ.IsBinary)
    (h : unroot τ.clusters = U4 1) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * exp (-τ.unrootedLength {0, 1}) ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 * exp (-τ.unrootedLength {0, 1}) ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 * exp (-τ.unrootedLength {0, 1}) := by
  have hm := mem_rootings4 τ 1 (by decide) h
  simp only [rootings4, mem_insert, mem_singleton] at hm
  rcases hm with hc | hc | hc | hc | hc | hc | hc
  -- the five binary rootings are excluded
  · exact absurd (n4_isBinary_of_clusters hc (by decide)) hτ
  · exact absurd (n4_isBinary_of_clusters hc (by decide)) hτ
  · exact absurd (n4_isBinary_of_clusters hc (by decide)) hτ
  · exact absurd (n4_isBinary_of_clusters hc (by decide)) hτ
  · exact absurd (n4_isBinary_of_clusters hc (by decide)) hτ
  · -- `((a,b):t,c,d)`: the limit `y → 0` of `(((a,b):t,c):y,d)`
    obtain ⟨h1, h2, h3⟩ := lim_fourTaxa_quartets τ (by rw [hc]; decide)
    have h01 : ({0, 1} : Finset (Fin 4)) ∈ τ.clusters := by rw [hc]; decide
    rw [ite_eq_left h01] at h1 h2 h3
    rw [n4_unrootedLength τ (C := {0, 1}) (by rw [hc]; decide)]
    exact ⟨h1, h2, h3⟩
  · -- `((c,d):t,a,b)`: the same with the labels permuted by `(a c)(b d)`
    have hc' : (τ.relabel n4_perm).clusters = hierarchyOf {{0, 1}} := by
      rw [SpeciesTree.relabel_clusters, hc]
      decide
    obtain ⟨h1, h2, h3⟩ := lim_fourTaxa_quartets (τ.relabel n4_perm) (by rw [hc']; decide)
    have h01 : ({0, 1} : Finset (Fin 4)) ∈ (τ.relabel n4_perm).clusters := by rw [hc']; decide
    have hl : (τ.relabel n4_perm).length {0, 1} = τ.length {2, 3} := by
      rw [SpeciesTree.relabel_length,
        show ({0, 1} : Finset (Fin 4)).map n4_perm.symm.toEmbedding = {2, 3} by decide]
    rw [ite_eq_left h01, hl] at h1 h2 h3
    rw [n4_unrootedLength τ (C := {2, 3}) (by rw [hc]; decide),
      n4_dist_relabel τ n4_perm (T' := treeOfClusters {{0, 1}})
        (by decide : relabelFamily n4_perm (treeOfClusters {{0, 1}}) = treeOfClusters {{0, 1}}),
      n4_dist_relabel τ n4_perm (T' := treeOfClusters {{0, 2}})
        (by decide : relabelFamily n4_perm (treeOfClusters {{0, 2}}) = treeOfClusters {{0, 2}}),
      n4_dist_relabel τ n4_perm (T' := treeOfClusters {{0, 3}})
        (by decide : relabelFamily n4_perm (treeOfClusters {{0, 3}}) = treeOfClusters {{0, 3}})]
    exact ⟨h1, h2, h3⟩

/-- **Section 5 on `Fin 4`, no internal edge.** The species trees `(a,b,c,d)` and `((a,b,c):y,d)`
are limits of the caterpillar `(((a,b):x,c):y,d)` as `x → 0` (and `y → 0`), so the three quartet
trees have probability `1/3` (`lim_fourTaxa_quartets` with `x = 0`). -/
private theorem n4_third (τ : SpeciesTree (Fin 4)) (hsub : τ.clusters ⊆ caterpillar4)
    (h01 : ({0, 1} : Finset (Fin 4)) ∉ τ.clusters) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 / 3 ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 := by
  obtain ⟨h1, h2, h3⟩ := lim_fourTaxa_quartets τ hsub
  rw [ite_eq_right h01, neg_zero, exp_zero] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]
    norm_num
  · rw [h2, mul_one]
  · rw [h3, mul_one]

/-- **Section 5 on `Fin 4`, the star.** The rootings of the star `U4 0` are `(a,b,c,d)` and the four
trees `((x,y,z):t,w)`: with permuted labels, `(a,b,c,d)` or `((a,b,c):t,d)` (`n4_third`). -/
private theorem n4_U4_zero (τ : SpeciesTree (Fin 4)) (h : unroot τ.clusters = U4 0) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 / 3 ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 := by
  have hm := mem_rootings4 τ 0 (by decide) h
  simp only [rootings4, mem_insert, mem_singleton] at hm
  rcases hm with hc | hc | hc | hc | hc
  · -- `(a,b,c,d)`
    exact n4_third τ (by rw [hc]; decide) (by rw [hc]; decide)
  · -- `((a,b,c):t,d)`
    exact n4_third τ (by rw [hc]; decide) (by rw [hc]; decide)
  · -- `((a,b,d):t,c)`: the labels permuted by `(c d)`
    obtain ⟨h1, h2, h3⟩ := n4_third (τ.relabel (Equiv.swap 2 3))
      (by rw [SpeciesTree.relabel_clusters, hc]; decide)
      (by rw [SpeciesTree.relabel_clusters, hc]; decide)
    rw [n4_dist_relabel τ (Equiv.swap 2 3) (T' := treeOfClusters {{0, 1}})
        (by decide : relabelFamily (Equiv.swap (2 : Fin 4) 3) (treeOfClusters {{0, 1}}) =
          treeOfClusters {{0, 1}}),
      n4_dist_relabel τ (Equiv.swap 2 3) (T' := treeOfClusters {{0, 3}})
        (by decide : relabelFamily (Equiv.swap (2 : Fin 4) 3) (treeOfClusters {{0, 2}}) =
          treeOfClusters {{0, 3}}),
      n4_dist_relabel τ (Equiv.swap 2 3) (T' := treeOfClusters {{0, 2}})
        (by decide : relabelFamily (Equiv.swap (2 : Fin 4) 3) (treeOfClusters {{0, 3}}) =
          treeOfClusters {{0, 2}})]
    exact ⟨h1, h3, h2⟩
  · -- `((a,c,d):t,b)`: the labels permuted by `(b d)`
    obtain ⟨h1, h2, h3⟩ := n4_third (τ.relabel (Equiv.swap 1 3))
      (by rw [SpeciesTree.relabel_clusters, hc]; decide)
      (by rw [SpeciesTree.relabel_clusters, hc]; decide)
    rw [n4_dist_relabel τ (Equiv.swap 1 3) (T' := treeOfClusters {{0, 3}})
        (by decide : relabelFamily (Equiv.swap (1 : Fin 4) 3) (treeOfClusters {{0, 1}}) =
          treeOfClusters {{0, 3}}),
      n4_dist_relabel τ (Equiv.swap 1 3) (T' := treeOfClusters {{0, 2}})
        (by decide : relabelFamily (Equiv.swap (1 : Fin 4) 3) (treeOfClusters {{0, 2}}) =
          treeOfClusters {{0, 2}}),
      n4_dist_relabel τ (Equiv.swap 1 3) (T' := treeOfClusters {{0, 1}})
        (by decide : relabelFamily (Equiv.swap (1 : Fin 4) 3) (treeOfClusters {{0, 3}}) =
          treeOfClusters {{0, 1}})]
    exact ⟨h3, h2, h1⟩
  · -- `((b,c,d):t,a)`: the labels permuted by `(a d)`
    obtain ⟨h1, h2, h3⟩ := n4_third (τ.relabel (Equiv.swap 0 3))
      (by rw [SpeciesTree.relabel_clusters, hc]; decide)
      (by rw [SpeciesTree.relabel_clusters, hc]; decide)
    rw [n4_dist_relabel τ (Equiv.swap 0 3) (T' := treeOfClusters {{0, 2}})
        (by decide : relabelFamily (Equiv.swap (0 : Fin 4) 3) (treeOfClusters {{0, 1}}) =
          treeOfClusters {{0, 2}}),
      n4_dist_relabel τ (Equiv.swap 0 3) (T' := treeOfClusters {{0, 1}})
        (by decide : relabelFamily (Equiv.swap (0 : Fin 4) 3) (treeOfClusters {{0, 2}}) =
          treeOfClusters {{0, 1}}),
      n4_dist_relabel τ (Equiv.swap 0 3) (T' := treeOfClusters {{0, 3}})
        (by decide : relabelFamily (Equiv.swap (0 : Fin 4) 3) (treeOfClusters {{0, 3}}) =
          treeOfClusters {{0, 3}})]
    exact ⟨h2, h1, h3⟩

/-! ### Any species tree on four taxa -/

/-- The quartet tree with the split `A | Aᶜ` of the species tree has probability
`1 - (2/3) e^{-t}`, where `t` is the length of the internal edge, for any species tree on four
taxa: by Section 4.1 if it is binary (`four_unrootedDist_of_mem`), by Section 5 if not. -/
theorem n4_unrootedDist_of_mem (hX : Fintype.card X = 4) (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    σ.unrootedDist id (treeOfClusters {A}) = 1 - 2 / 3 * exp (-σ.unrootedLength A) := by
  by_cases hσ : σ.IsBinary
  · exact four_unrootedDist_of_mem hX σ hσ hA hA2
  · exact four_unrootedDist_of_mem_of_U4 hX σ hA hA2 fun e he =>
      (n4_U4_one _ (fun hb => hσ ((SpeciesTree.isBinary_relabel_iff σ e.symm).1 hb)) he).1

/-- The two quartet trees other than the one with the split `A | Aᶜ` of the species tree have
probability `(1/3) e^{-t}`, where `t` is the length of the internal edge, for any species tree on
four taxa: by Section 4.1 if it is binary (`four_unrootedDist_of_ne_of_isBinary`), by Section 5 if
not. -/
theorem n4_unrootedDist_of_ne (hX : Fintype.card X = 4) (σ : SpeciesTree X) {A B : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) (hB2 : #B = 2) (hBA : B ≠ A) (hBA' : B ≠ Aᶜ) :
    σ.unrootedDist id (treeOfClusters {B}) = 1 / 3 * exp (-σ.unrootedLength A) := by
  by_cases hσ : σ.IsBinary
  · exact four_unrootedDist_of_ne_of_isBinary hX σ hσ hA hA2 hB2 hBA hBA'
  · exact four_unrootedDist_of_ne_of_U4 hX σ hA hA2 hB2 hBA hBA' fun e he =>
      (n4_U4_one _ (fun hb => hσ ((SpeciesTree.isBinary_relabel_iff σ e.symm).1 hb)) he).2

/-- If the species tree has no internal edge, the three quartet trees have probability `1/3`.

Such a species tree is not binary: by Section 5 it is `(a,b,c,d)` or `((a,b,c):y,d)` with permuted
labels (`n4_U4_zero`). -/
theorem four_unrootedDist_of_star (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (hσ : ∀ A ∈ unroot σ.clusters, #A ≠ 2) {B : Finset X} (hB2 : #B = 2) :
    σ.unrootedDist id (treeOfClusters {B}) = 1 / 3 :=
  four_unrootedDist_of_star_of_U4 hX σ hσ hB2 fun _ he => n4_U4_zero _ he

/-! ### The distribution determines `σ⁻`, and conversely -/

/-- On four taxa, a set of taxa that is not of size `2` is a side of a split of the species tree
exactly when it is a single taxon or the complement of one. -/
private theorem n4_mem_unroot_iff (hX : Fintype.card X = 4) (σ : SpeciesTree X) {A : Finset X}
    (hA : #A ≠ 2) : A ∈ unroot σ.clusters ↔ #A = 1 ∨ #A = 3 := by
  have hAc : #Aᶜ = 4 - #A := by rw [card_compl, hX]
  have hle : #A ≤ 4 := hX ▸ card_le_univ A
  have hne : ∀ C : Finset X, C ≠ univ → #C ≠ 4 := fun C hC h4 =>
    hC ((card_eq_iff_eq_univ C).1 (h4.trans hX.symm))
  have hne' : ∀ C : Finset X, #C ≠ 4 → C ≠ univ := fun C h hu =>
    h (by rw [hu, card_univ, hX])
  rw [mem_unroot]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have := (σ.nonempty_of_mem A h1).card_pos
      have := hne A h2
      omega
    · have := (σ.nonempty_of_mem _ h1).card_pos
      have := hne _ h2
      omega
  · rintro (h | h)
    · obtain ⟨x, rfl⟩ := card_eq_one.1 h
      exact Or.inl ⟨σ.singleton_mem x, hne' _ (by rw [card_singleton]; omega)⟩
    · obtain ⟨x, hx⟩ := card_eq_one.1 (show #Aᶜ = 1 by omega)
      exact Or.inr ⟨hx ▸ σ.singleton_mem x, hne' _ (by omega)⟩

/-- If two species trees on four taxa have the same gene tree distribution, every nontrivial
split of the first is a split of the second, of the same length. -/
private theorem n4_mem_unroot_of_unrootedDist_eq (hX : Fintype.card X = 4)
    {σ σ' : SpeciesTree X} (h : σ.unrootedDist id = σ'.unrootedDist id) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    A ∈ unroot σ'.clusters ∧ σ.unrootedLength A = σ'.unrootedLength A := by
  have h1 := n4_unrootedDist_of_mem hX σ hA hA2
  have hlt : exp (-σ.unrootedLength A) < 1 :=
    exp_lt_one_iff.2 (neg_lt_zero.2 (four_unrootedLength_pos σ hA))
  rw [h] at h1
  by_cases hA' : A ∈ unroot σ'.clusters
  · refine ⟨hA', ?_⟩
    rw [n4_unrootedDist_of_mem hX σ' hA' hA2] at h1
    have : exp (-σ'.unrootedLength A) = exp (-σ.unrootedLength A) := by linarith
    rw [exp_eq_exp, neg_inj] at this
    exact this.symm
  · exfalso
    by_cases hex : ∃ A' ∈ unroot σ'.clusters, #A' = 2
    · obtain ⟨A', hA'm, hA'2⟩ := hex
      have hne1 : A ≠ A' := fun e => hA' (e ▸ hA'm)
      have hne2 : A ≠ A'ᶜ := fun e => hA' (e ▸ compl_mem_unroot.2 hA'm)
      rw [n4_unrootedDist_of_ne hX σ' hA'm hA'2 hA2 hne1 hne2] at h1
      have : exp (-σ'.unrootedLength A') < 1 :=
        exp_lt_one_iff.2 (neg_lt_zero.2 (four_unrootedLength_pos σ' hA'm))
      linarith
    · push Not at hex
      rw [four_unrootedDist_of_star hX σ' hex hA2] at h1
      linarith

/-- On four taxa, two species trees have the same unrooted gene tree distribution exactly when
they have the same unrooted metric tree.

This holds for binary and nonbinary species trees alike (Section 5, l.709–711): the quartet
probabilities are those of Section 4.1 for a binary tree and their limits of Section 5 for a
nonbinary one (`n4_unrootedDist_of_mem`, `n4_unrootedDist_of_ne`, `four_unrootedDist_of_star`). -/
theorem unrootedDist_eq_iff_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  have hcard : ∀ A : Finset X, #Aᶜ = 4 - #A := fun A => by rw [card_compl, hX]
  have hle : ∀ A : Finset X, #A ≤ 4 := fun A => hX ▸ card_le_univ A
  constructor
  · intro h
    refine ⟨?_, fun A hA h2 h2' => (n4_mem_unroot_of_unrootedDist_eq hX h hA
      (by have := hcard A; have := hle A; omega)).2⟩
    ext A
    by_cases hA2 : #A = 2
    · exact ⟨fun hA => (n4_mem_unroot_of_unrootedDist_eq hX h hA hA2).1,
        fun hA => (n4_mem_unroot_of_unrootedDist_eq hX h.symm hA hA2).1⟩
    · rw [n4_mem_unroot_iff hX σ hA2, n4_mem_unroot_iff hX σ' hA2]
  · rintro ⟨hU, hL⟩
    have hlen : ∀ A ∈ unroot σ.clusters, #A = 2 → σ.unrootedLength A = σ'.unrootedLength A :=
      fun A hA hA2 => hL A hA (by omega) (by rw [hcard]; omega)
    refine four_unrootedDist_ext hX fun B hB2 => ?_
    by_cases hB : B ∈ unroot σ.clusters
    · rw [n4_unrootedDist_of_mem hX σ hB hB2, n4_unrootedDist_of_mem hX σ' (hU ▸ hB) hB2,
        hlen B hB hB2]
    · by_cases hex : ∃ A ∈ unroot σ.clusters, #A = 2
      · obtain ⟨A, hA, hA2⟩ := hex
        have hne1 : B ≠ A := fun e => hB (e ▸ hA)
        have hne2 : B ≠ Aᶜ := fun e => hB (e ▸ compl_mem_unroot.2 hA)
        rw [n4_unrootedDist_of_ne hX σ hA hA2 hB2 hne1 hne2,
          n4_unrootedDist_of_ne hX σ' (hU ▸ hA) hA2 hB2 hne1 hne2, hlen A hA hA2]
      · push Not at hex
        rw [four_unrootedDist_of_star hX σ hex hB2,
          four_unrootedDist_of_star hX σ' (hU ▸ hex) hB2]

end ADR11
