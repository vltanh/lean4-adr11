module

public import ADR11.Rootings.Statements
public import ADR11.Trees.Classify

/-!
# The five-taxon analysis: common helpers

Helpers for `ADR11.Identifiability.FiveTaxaAnalysis`:

* `five_exp_bounds`: `0 < exp (-ℓ) < 1` for the length `ℓ` of an edge of a species tree;
* `five_unrootedLength_mem`, `five_unrootedLength_compl_mem`, `five_unrootedLength_both`: the
  length of a split `S | T` of the unrooted tree, when exactly one of `S`, `T`, or both, are
  clusters of the rooted tree;
* `five_length_eq`: a length is recovered from an affine relation in a power of `exp (-ℓ)`;
* `five_sameRootedMetricTree_of_lengths`: two species trees with the same hierarchy
  `hierarchyOf C` and the same lengths above the clusters of `C` have the same rooted metric
  tree.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `exp (-ℓ)` lies in `(0, 1)` for the length `ℓ` of an edge of a species tree. -/
theorem five_exp_bounds (τ : SpeciesTree X) {A : Finset X} (hA : A ∈ τ.clusters)
    (hAu : A ≠ univ) : 0 < exp (-τ.length A) ∧ exp (-τ.length A) < 1 :=
  ⟨exp_pos _, Real.exp_lt_one_iff.2 (neg_lt_zero.2 (τ.length_pos A hA hAu))⟩

/-- The length of the split `S | T` (`T = Sᶜ`) when `S` is a cluster and `T` is not. -/
theorem five_unrootedLength_mem (τ : SpeciesTree X) {S T : Finset X} (hST : Sᶜ = T)
    (hS : S ∈ τ.clusters) (hSu : S ≠ univ) (hT : T ∉ τ.clusters) :
    τ.unrootedLength S = τ.length S := by
  unfold SpeciesTree.unrootedLength
  rw [Finset.sum_eq_single_of_mem S (mem_filter.2 ⟨hS, hSu, Or.inl rfl⟩)]
  intro C hCf hCS
  obtain ⟨hC, -, hC'⟩ := mem_filter.1 hCf
  rcases hC' with rfl | rfl
  · exact absurd rfl hCS
  · exact absurd (hST ▸ hC) hT

/-- The length of the split `S | T` (`T = Sᶜ`) when `T` is a cluster and `S` is not. -/
theorem five_unrootedLength_compl_mem (τ : SpeciesTree X) {S T : Finset X} (hST : Sᶜ = T)
    (hT : T ∈ τ.clusters) (hTu : T ≠ univ) (hS : S ∉ τ.clusters) :
    τ.unrootedLength S = τ.length T := by
  unfold SpeciesTree.unrootedLength
  rw [Finset.sum_eq_single_of_mem T (mem_filter.2 ⟨hT, hTu, Or.inr hST.symm⟩)]
  intro C hCf hCT
  obtain ⟨hC, -, hC'⟩ := mem_filter.1 hCf
  rcases hC' with rfl | rfl
  · exact absurd hC hS
  · exact absurd hST hCT

/-- The length of the split `S | T` (`T = Sᶜ`) when both `S` and `T` are clusters (the root lies
on the edge of the split). -/
theorem five_unrootedLength_both (τ : SpeciesTree X) {S T : Finset X} (hST : Sᶜ = T)
    (hS : S ∈ τ.clusters) (hSu : S ≠ univ) (hT : T ∈ τ.clusters) (hTu : T ≠ univ) :
    τ.unrootedLength S = τ.length S + τ.length T := by
  have hne : S ≠ T := by
    intro hST'
    obtain ⟨x, hx⟩ := τ.nonempty_of_mem S hS
    have hx' : x ∈ T := hST' ▸ hx
    rw [← hST, mem_compl] at hx'
    exact hx' hx
  unfold SpeciesTree.unrootedLength
  rw [← Finset.sum_pair hne]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext C
  simp only [mem_filter, mem_insert, mem_singleton, hST]
  constructor
  · rintro ⟨-, -, hC⟩
    exact hC
  · rintro (rfl | rfl)
    · exact ⟨hS, hSu, Or.inl rfl⟩
    · exact ⟨hT, hTu, Or.inr rfl⟩

/-- A length is determined by an affine relation `v = A * exp (-ℓ) ^ n + B` with `A ≠ 0`,
`n ≠ 0`. -/
theorem five_length_eq {x y A B v : ℝ} {n : ℕ} (hn : n ≠ 0) (hA : A ≠ 0)
    (hx : v = A * exp (-x) ^ n + B) (hy : v = A * exp (-y) ^ n + B) : x = y := by
  have h1 : exp (-x) ^ n = exp (-y) ^ n := mul_left_cancel₀ hA (by linarith)
  have h2 := Real.exp_injective ((pow_left_inj₀ (exp_pos _).le (exp_pos _).le hn).1 h1)
  linarith

/-- A member of `hierarchyOf C` with at least two elements, other than `univ`, lies in `C`. -/
theorem five_mem_of_mem_hierarchyOf {C : Finset (Finset X)} {A : Finset X}
    (hA : A ∈ hierarchyOf C) (h2 : 2 ≤ #A) (hu : A ≠ univ) : A ∈ C := by
  unfold hierarchyOf at hA
  rcases mem_insert.1 hA with rfl | hA
  · exact absurd rfl hu
  rcases mem_union.1 hA with hA | hA
  · exact hA
  obtain ⟨x, -, rfl⟩ := mem_image.1 hA
  simp at h2

/-- Two species trees with the same hierarchy `hierarchyOf C` and the same lengths above the
clusters of `C` have the same rooted metric tree. -/
theorem five_sameRootedMetricTree_of_lengths {τ τ' : SpeciesTree X} {C : Finset (Finset X)}
    (h : τ.clusters = hierarchyOf C) (h' : τ'.clusters = hierarchyOf C)
    (hl : ∀ A ∈ C, τ.length A = τ'.length A) : τ.SameRootedMetricTree τ' :=
  ⟨h.trans h'.symm, fun A hA h2 hu => hl A (five_mem_of_mem_hierarchyOf (h ▸ hA) h2 hu)⟩

end ADR11
