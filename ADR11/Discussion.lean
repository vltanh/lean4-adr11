module

public import ADR11.FiveTaxa.Caterpillar
public import ADR11.Rootings.Statements

/-!
# Section 6 (Discussion)

The Discussion remarks that, for the species tree `((((a,b):x,c):y,d):z,e)` with `y` large,
determining that `e` is the outgroup "would require observing conflicting splits, such as that
`ABD|CE` is more probable than `ABE|CD`". For this species tree the inequality goes the other way
(the split `ABE|CD` of `T₃, T₁₀, T₁₅` is more probable than `ABD|CE` of `T₂, T₇, T₁₄`), as in the
proof of Proposition 7; `discussion_splits` records the correct direction.
-/

@[expose] public section

namespace ADR11

open Finset

/-- The probability that the unrooted gene tree has the split `A | Aᶜ`. -/
noncomputable def splitProb {X : Type*} [Fintype X] [DecidableEq X] (σ : SpeciesTree X)
    (A : Finset X) : ℝ :=
  ∑ T, if A ∈ T then σ.unrootedDist id T else 0

/-- On five taxa, if the split `A | Aᶜ` belongs to exactly the three gene trees `T_a, T_b, T_c`
among `T₁, …, T₁₅`, its probability is `u_a + u_b + u_c`. -/
private theorem splitProb_eq_of_three (σ : SpeciesTree (Fin 5)) (A : Finset (Fin 5)) (a b c : ℕ)
    (hA : ∀ i ∈ Icc 1 15, A ∈ T5 i → i = a ∨ i = b ∨ i = c) (hAa : A ∈ T5 a) (hAb : A ∈ T5 b)
    (hAc : A ∈ T5 c) (hab : T5 a ∉ ({T5 b, T5 c} : Finset (Finset (Finset (Fin 5)))))
    (hbc : T5 b ≠ T5 c) :
    splitProb σ A = u σ a + u σ b + u σ c := by
  unfold splitProb
  rw [← Finset.sum_subset (Finset.subset_univ {T5 a, T5 b, T5 c}) ?_]
  · rw [Finset.sum_insert hab, Finset.sum_insert (by simpa using hbc), Finset.sum_singleton,
      ite_eq_left hAa, ite_eq_left hAb, ite_eq_left hAc, add_assoc]
    rfl
  · intro T _ hT
    by_cases h : ∀ i ∈ Icc 1 15, T ≠ T5 i
    · simp [unrootedDist_eq_zero_five σ T h]
    · push Not at h
      obtain ⟨i, hi, rfl⟩ := h
      rw [ite_eq_right]
      intro hAi
      rcases hA i hi hAi with rfl | rfl | rfl <;> simp at hT

/-- For the caterpillar species tree `((((a,b),c),d),e)`, the split `ABE|CD` is strictly more
probable than the split `ABD|CE`, for all branch lengths. -/
theorem discussion_splits (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    splitProb σ {0, 1, 3} < splitProb σ {0, 1, 4} := by
  rw [splitProb_eq_of_three σ {0, 1, 3} 2 7 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    splitProb_eq_of_three σ {0, 1, 4} 3 10 15 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, e10, -, e14, e15⟩ := equation12 σ hσ
  obtain ⟨-, -, -, -, -, h32, -, -⟩ := equation5 σ hσ
  linarith

end ADR11
