module

public import ADR11.Nonbinary
public import ADR11.Introduction.Proposition1

/-!
# Section 5: polytomies and rooted triples

* `section5_triples`: no cluster of the species tree contains exactly two of three taxa if and only
  if the three rooted triples on them are equiprobable.
* `section5_proposition1`, `section5_corollary2`: Proposition 1 and Corollary 2 for species trees
  that need not be binary.

The rooted triples on three distinct taxa `a, b, c` have the probabilities of the rooted gene trees
under the induced species tree on `{a, b, c}` (`triple_exists_fin3`). When no cluster contains
exactly two of `a, b, c`, the induced tree is the unresolved tree `(a,b,c)`, and the three
probabilities are `1/3`, the limits of equation (1) as the internal branch length tends to `0`
(`lim_threeTaxa_unresolved`, as in `section5_threeTaxa`); otherwise exactly one exceeds `1/3`
(`triple_rootedTripleProb_of_resolved`). So in any species tree a cluster contains `a` and `b` but
not `c` exactly when `ℙ(ab|c) > 1/3` (`triple_resolved_iff`), and the proof of Proposition 1
(`triple_sameRootedMetricTree`) applies.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- On `Fin 3`, a hierarchy without 2-element clusters is the unresolved tree. -/
private theorem triple_fin3_eq_hierarchyOf_empty {H : Finset (Finset (Fin 3))}
    (hH : IsHierarchy H) (h01 : ({0, 1} : Finset (Fin 3)) ∉ H)
    (h02 : ({0, 2} : Finset (Fin 3)) ∉ H) (h12 : ({1, 2} : Finset (Fin 3)) ∉ H) :
    H = hierarchyOf ∅ := by
  have key : ∀ D : Finset (Fin 3), D.Nonempty → D ≠ {0, 1} → D ≠ {0, 2} → D ≠ {1, 2} →
      D ∈ hierarchyOf (∅ : Finset (Finset (Fin 3))) := by
    decide
  ext D
  constructor
  · intro hD
    refine key D (hH.2.2.1 D hD) ?_ ?_ ?_
    · rintro rfl
      exact h01 hD
    · rintro rfl
      exact h02 hD
    · rintro rfl
      exact h12 hD
  · intro hD
    simp only [hierarchyOf, empty_union, mem_insert, mem_image, mem_univ, true_and] at hD
    rcases hD with rfl | ⟨x, rfl⟩
    exacts [hH.1, hH.2.1 x]

/-- **The unresolved triple.** If no cluster contains exactly two of the distinct taxa `a, b, c`,
then the three rooted triples on them have probability `1/3`: the induced species tree on
`{a, b, c}` is the unresolved tree `(a,b,c)`, whose rooted gene trees have probability `1/3` as the
limits of equation (1) (`lim_threeTaxa_unresolved`). -/
theorem triple_rootedTripleProb_of_unresolved (σ : SpeciesTree X) {a b c : X} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (h₁ : ¬ ∃ C ∈ σ.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C)
    (h₂ : ¬ ∃ C ∈ σ.clusters, a ∈ C ∧ c ∈ C ∧ b ∉ C)
    (h₃ : ¬ ∃ C ∈ σ.clusters, b ∈ C ∧ c ∈ C ∧ a ∉ C) :
    σ.rootedTripleProb a b c = 1 / 3 ∧ σ.rootedTripleProb a c b = 1 / 3 ∧
      σ.rootedTripleProb b c a = 1 / 3 := by
  obtain ⟨τ, e₁, e₂, e₃, h01, h02, h12, -⟩ := triple_exists_fin3 σ hab hac hbc
  have hτ : τ.clusters = hierarchyOf ∅ :=
    triple_fin3_eq_hierarchyOf_empty τ.isHierarchy (mt h01.1 h₁) (mt h02.1 h₂) (mt h12.1 h₃)
  rw [e₁, e₂, e₃]
  exact lim_threeTaxa_unresolved τ hτ

/-- In any species tree, a cluster contains `a` and `b` but not `c` if and only if the probability
of the rooted triple `ab|c` exceeds `1/3`. -/
theorem triple_resolved_iff (σ : SpeciesTree X) {a b c : X} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    (∃ C ∈ σ.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C) ↔ 1 / 3 < σ.rootedTripleProb a b c := by
  refine ⟨triple_one_third_lt_of_resolved σ hab hac hbc, fun hp => ?_⟩
  by_contra h₁
  by_cases h₂ : ∃ C ∈ σ.clusters, a ∈ C ∧ c ∈ C ∧ b ∉ C
  · exact absurd hp (not_lt.2 (triple_lt_one_third_of_resolved_left σ hab hac hbc h₂).le)
  by_cases h₃ : ∃ C ∈ σ.clusters, b ∈ C ∧ c ∈ C ∧ a ∉ C
  · exact absurd hp (not_lt.2 (triple_lt_one_third_of_resolved_right σ hab hac hbc h₃).le)
  rw [(triple_rootedTripleProb_of_unresolved σ hab hac hbc h₁ h₂ h₃).1] at hp
  exact lt_irrefl _ hp

/-- Section 5: polytomies are identified by rooted triples. For distinct taxa `a, b, c`, no cluster
of the species tree contains exactly two of them if and only if the three rooted triples on them
are equiprobable. -/
theorem section5_triples (σ : SpeciesTree X) (a b c : X) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    (∀ C ∈ σ.clusters, ¬ ((a ∈ C ∧ b ∈ C ∧ c ∉ C) ∨ (a ∈ C ∧ c ∈ C ∧ b ∉ C) ∨
        (b ∈ C ∧ c ∈ C ∧ a ∉ C))) ↔
      (σ.rootedTripleProb a b c = σ.rootedTripleProb a c b ∧
        σ.rootedTripleProb a b c = σ.rootedTripleProb b c a) := by
  constructor
  · intro h
    obtain ⟨e₁, e₂, e₃⟩ := triple_rootedTripleProb_of_unresolved σ hab hac hbc
      (fun ⟨C, hC, hC'⟩ => h C hC (Or.inl hC'))
      (fun ⟨C, hC, hC'⟩ => h C hC (Or.inr (Or.inl hC')))
      (fun ⟨C, hC, hC'⟩ => h C hC (Or.inr (Or.inr hC')))
    rw [e₁, e₂, e₃]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h₁, h₂⟩ C hC (hC' | hC' | hC')
    · -- `ab|c` is displayed: `ℙ(ab|c) > 1/3 > ℙ(ac|b)`
      have := triple_one_third_lt_of_resolved σ hab hac hbc ⟨C, hC, hC'⟩
      have := triple_lt_one_third_of_resolved_left σ hac hab hbc.symm ⟨C, hC, hC'⟩
      linarith
    · -- `ac|b` is displayed: `ℙ(ac|b) > 1/3 > ℙ(ab|c)`
      have := triple_one_third_lt_of_resolved σ hac hab hbc.symm ⟨C, hC, hC'⟩
      have := triple_lt_one_third_of_resolved_left σ hab hac hbc ⟨C, hC, hC'⟩
      linarith
    · -- `bc|a` is displayed: `ℙ(bc|a) > 1/3 > ℙ(ab|c)`
      have := triple_one_third_lt_of_resolved σ hbc hab.symm hac.symm ⟨C, hC, hC'⟩
      have := triple_lt_one_third_of_resolved_right σ hab hac hbc ⟨C, hC, hC'⟩
      linarith

/-- Section 5: polytomies are identified by rooted triples, so Proposition 1 holds for species trees
that need not be binary: the probabilities of rooted triples determine the species tree topology
and its internal branch lengths. -/
theorem section5_proposition1 (σ σ' : SpeciesTree X)
    (h : ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c → σ.rootedTripleProb a b c = σ'.rootedTripleProb a b c) :
    σ.SameRootedMetricTree σ' :=
  triple_sameRootedMetricTree σ σ' (fun _ _ _ hab hac hbc => triple_resolved_iff σ hab hac hbc)
    (fun _ _ _ hab hac hbc => triple_resolved_iff σ' hab hac hbc) h

/-- Section 5: Corollary 2 for species trees that need not be binary. -/
theorem section5_corollary2 (σ σ' : SpeciesTree X)
    (h : σ.rootedDist id = σ'.rootedDist id) : σ.SameRootedMetricTree σ' := by
  refine section5_proposition1 σ σ' fun a b c _ _ _ => ?_
  unfold SpeciesTree.rootedTripleProb
  rw [h]

end ADR11
