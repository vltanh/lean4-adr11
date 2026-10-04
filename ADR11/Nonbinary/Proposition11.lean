module

public import ADR11.Nonbinary.FiveTaxa
public import ADR11.Nonbinary.FourTaxa
public import ADR11.Nonbinary.Theorem9
public import ADR11.Identifiability.Proposition3
public import ADR11.Identifiability.Unrooted

/-!
# Proposition 11: nonbinary species trees

Proposition 3, Corollary 6, Propositions 7 and 8, Theorem 9 and Corollary 10 remain valid if the
species tree `σ⁺` is nonbinary. The proofs follow Section 5 and Appendix C:

* Proposition 3 (Section 5, l.709–711): on four taxa the distribution of a species tree, binary or
  not, depends only on its unrooted metric tree and determines it (`unrootedDist_eq_iff_four`, the
  four-taxon formulas for every rooting); two of the rooted trees of Section 4.1 share their
  distribution.
* Corollary 6 (Appendix C, l.940–941): by Lemma 5 and the four-taxon case every induced quartet
  tree, resolved or not, is determined, hence the unrooted metric tree, by the reconstruction of
  trees from their quartets [Bandelt–Dress 1986; Semple–Steel 2003, Theorem 6.3.5]
  (`sameUnrootedMetricTree_of_unrootedDist_eq`).
* Propositions 7 and 8 (Appendix C, l.943–993): the class sizes, the labelling rules and the
  equations of Table 7 (`appC_sameRootedMetricTree`); for two binary trees, Proposition 8.
* Theorem 9 (l.995): the argument of Theorem 9, in which a root of degree greater than 2 is
  located by a five-taxon set meeting three of its children (`rl_nb_theorem9`).
* Corollary 10 (l.996): "The proof of Corollary 10 did not use the assumption that `σ⁺` is
  binary" (`c10_nb_corollary10`, the argument of `corollary10`).
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Proposition 11** (`prop:nonbinary`), Proposition 8 for nonbinary species trees. -/
theorem proposition11_proposition8 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' :=
  appC_sameRootedMetricTree hX σ σ' h

/-- **Proposition 11** (`prop:nonbinary`), Proposition 7 for nonbinary species trees. As in
Appendix C, the rooted topology is determined together with the lengths: the cases `P₄`/`P₈` and
balanced/`P₆` are told apart by solving for a branch length. -/
theorem proposition11_proposition7 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.clusters = σ'.clusters :=
  (proposition11_proposition8 hX σ σ' h).1

/-- **Proposition 11** (`prop:nonbinary`), Theorem 9 for nonbinary species trees, `|X| = 4`. -/
theorem proposition11_theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' :=
  unrootedDist_eq_iff_four hX σ σ'

/-- **Proposition 11** (`prop:nonbinary`), Corollary 6 for nonbinary species trees. For any `X`,
`ℙ_{σ⁺}` determines `σ⁻`. -/
theorem proposition11_corollary6 (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' :=
  sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h

/-- **Proposition 11** (`prop:nonbinary`), Proposition 3 for nonbinary species trees. For
`|X| = 4`, `σ⁻` is identifiable from `ℙ_{σ⁺}`, but `σ⁺` is not. -/
theorem proposition11_proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.unrootedDist id = σ'.unrootedDist id →
        σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.unrootedDist id = σ'.unrootedDist id ∧
        ¬ σ.SameRootedMetricTree σ' := by
  refine ⟨fun σ σ' h => (proposition11_theorem9_four hX σ σ').1 h, ?_⟩
  obtain ⟨τ, τ', -, -, hd, hn⟩ := f1_exists_sameUnrootedDist_not_sameRooted_four
  let e : Fin 4 ≃ X := (Fintype.equivFinOfCardEq hX).symm
  exact ⟨τ.relabel e, τ'.relabel e, (SpeciesTree.unrootedDist_relabel_eq_iff τ τ' e).2 hd,
    fun hs => hn ((SpeciesTree.sameRootedMetricTree_relabel_iff τ τ' e).1 hs)⟩

/-- **Proposition 11** (`prop:nonbinary`), Theorem 9 for nonbinary species trees, `|X| ≥ 5`.

Departure from the paper: as in `theorem9`, no quartet distinguishes a pendant edge, so for a
pendant edge the five-taxon set that locates the root is chosen differently
(`rl_nb_theorem9`, audit item E4). -/
theorem proposition11_theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' :=
  rl_nb_theorem9 hX σ σ' h fun _ _ hS5 hd => proposition11_proposition8 (by simpa using hS5) _ _ hd

/-- **Proposition 11** (`prop:nonbinary`), Corollary 10 for nonbinary species trees. -/
theorem proposition11_corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} :=
  c10_nb_corollary10 (fun hY τ τ' hd => proposition11_proposition8 hY τ τ' hd) ℓ hℓ hcond σ σ' h

end ADR11
