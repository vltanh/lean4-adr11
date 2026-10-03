module

public import ADR11.FiveTaxa.Balanced
public import ADR11.FiveTaxa.Caterpillar
public import ADR11.FiveTaxa.Pseudocaterpillar
public import ADR11.Nonbinary

/-!
# Appendix C: nonbinary 5-taxon species trees

* `table6`, `table7`: the inequalities and the unrooted gene tree distributions of the nine
  nonbinary 5-taxon representatives `P₁, …, P₉` (`ADR11.polytomy5`).
* `appendixC_leastClass`: the least probable class `𝒞` of gene trees is well defined, with the
  sizes listed in the proof of Proposition 11 for the twelve rooted 5-taxon shapes, and the sizes
  of the next class used there.
* `table7_classes`: the equivalence classes of Table 7.
* `appendixC_degenerate`: the two 2-element classes of `P₅` and of `P₇` can merge.

`table7` is obtained as in the paper (l.944), from the equations (11)–(13) for the resolved trees
by setting one or more branch lengths to `0`. Each `Pₖ` is the contraction of a binary
representative with the same labels: `P₁, P₂, P₄, P₆, P₈` of the balanced tree, `P₃, P₉` of the
caterpillar, `P₅, P₇` of the pseudocaterpillar. By `section5_limit` its distribution is the limit
of the representative's as the contracted lengths tend to `0`; the formulas are continuous in
`X, Y, Z`, so the limit is the formula with `X`, `Y` or `Z` equal to `1` (`lim_u_bal`,
`lim_u_cat`, `lim_u_pse`).

Everything else is derived from the formulas of `table7` (for the resolved shapes, from
(11)–(13) and the inequalities (4)–(6)): each `u_i` equals `u` of the name of its class, the
differences between the classes are explicit positive polynomials in `X, Y, Z ∈ (0, 1)`, and the
separating or degenerate examples are species trees `SpeciesTree.ofLengths` with rational
`X, Y, Z`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Table 7: the formulas (11)–(13) with branch lengths set to `0` -/

/-- Equation (11): `u_i` of the balanced species tree `(((a,b):x,c):y,(d,e):z)` as a polynomial in
`X = e^{-x}`, `Y = e^{-y}`, `Z = e^{-z}`. -/
private noncomputable def lim_balF (i : ℕ) (X Y Z : ℝ) : ℝ :=
  if i = 1 then 1 - 2 / 3 * X - 2 / 3 * Y * Z + 1 / 3 * X * Y * Z + 1 / 15 * X * Y ^ 3 * Z
  else if i ∈ ({2, 3} : Finset ℕ) then 1 / 3 * Y * Z - 1 / 6 * X * Y * Z - 1 / 10 * X * Y ^ 3 * Z
  else if i ∈ ({4, 13} : Finset ℕ) then 1 / 3 * X - 1 / 3 * X * Y * Z + 1 / 15 * X * Y ^ 3 * Z
  else if i ∈ ({5, 6, 9, 12} : Finset ℕ) then 1 / 6 * X * Y * Z - 1 / 10 * X * Y ^ 3 * Z
  else 1 / 15 * X * Y ^ 3 * Z

/-- Equation (12): `u_i` of the caterpillar species tree `((((a,b):x,c):y,d):z,e)` as a polynomial
in `X = e^{-x}`, `Y = e^{-y}`, `Z = e^{-z}`. -/
private noncomputable def lim_catF (i : ℕ) (X Y Z : ℝ) : ℝ :=
  if i = 1 then
    1 - 2 / 3 * X - 2 / 3 * Y + 1 / 3 * X * Y + 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6
  else if i = 2 then 1 / 3 * Y - 1 / 6 * X * Y - 1 / 9 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6
  else if i = 3 then 1 / 3 * Y - 1 / 6 * X * Y - 1 / 18 * X * Y ^ 3 - 2 / 45 * X * Y ^ 3 * Z ^ 6
  else if i ∈ ({4, 13} : Finset ℕ) then
    1 / 3 * X - 1 / 3 * X * Y + 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6
  else if i ∈ ({5, 12} : Finset ℕ) then
    1 / 6 * X * Y - 1 / 9 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6
  else if i ∈ ({6, 9} : Finset ℕ) then
    1 / 6 * X * Y - 1 / 18 * X * Y ^ 3 - 2 / 45 * X * Y ^ 3 * Z ^ 6
  else 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6

/-- Equation (13): `u_i` of the pseudocaterpillar species tree `(((a,b):x,(d,e):y):z,c)` as a
polynomial in `X = e^{-x}`, `Y = e^{-y}`, `Z = e^{-z}`. -/
private noncomputable def lim_pseF (i : ℕ) (X Y Z : ℝ) : ℝ :=
  if i = 1 then 1 - 2 / 3 * X - 2 / 3 * Y + 4 / 9 * X * Y - 2 / 45 * X * Y * Z ^ 6
  else if i ∈ ({2, 3} : Finset ℕ) then 1 / 3 * Y - 5 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6
  else if i ∈ ({4, 13} : Finset ℕ) then 1 / 3 * X - 5 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6
  else if i ∈ ({8, 11} : Finset ℕ) then 1 / 9 * X * Y - 2 / 45 * X * Y * Z ^ 6
  else 1 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6

/-- Equation (11) in the form `u_i = lim_balF i X Y Z`. -/
private theorem lim_balF_eq (τ : SpeciesTree (Fin 5)) (hτ : τ.clusters = balanced5) {i : ℕ}
    (hi : i ∈ Icc 1 15) :
    u τ i = lim_balF i (exp (-τ.length {0, 1})) (exp (-τ.length {0, 1, 2}))
      (exp (-τ.length {3, 4})) := by
  obtain ⟨h1, h2, h3, h4, h13, h5, h6, h9, h12, h7, h8, h10, h11, h14, h15⟩ := equation11 τ hτ
  obtain ⟨hi1, hi15⟩ := mem_Icc.1 hi
  interval_cases i <;>
    simp only [lim_balF, h1, h2, h3, h4, h13, h5, h6, h9, h12, h7, h8, h10, h11, h14, h15,
      Finset.mem_insert, Finset.mem_singleton, Nat.reduceEqDiff, or_false, or_true, ↓reduceIte]

/-- Equation (12) in the form `u_i = lim_catF i X Y Z`. -/
private theorem lim_catF_eq (τ : SpeciesTree (Fin 5)) (hτ : τ.clusters = caterpillar5) {i : ℕ}
    (hi : i ∈ Icc 1 15) :
    u τ i = lim_catF i (exp (-τ.length {0, 1})) (exp (-τ.length {0, 1, 2}))
      (exp (-τ.length {0, 1, 2, 3})) := by
  obtain ⟨h1, h2, h3, h4, h13, h5, h12, h6, h9, h7, h8, h10, h11, h14, h15⟩ := equation12 τ hτ
  obtain ⟨hi1, hi15⟩ := mem_Icc.1 hi
  interval_cases i <;>
    simp only [lim_catF, h1, h2, h3, h4, h13, h5, h12, h6, h9, h7, h8, h10, h11, h14, h15,
      Finset.mem_insert, Finset.mem_singleton, Nat.reduceEqDiff, or_false, or_true, ↓reduceIte]

/-- Equation (13) in the form `u_i = lim_pseF i X Y Z`. -/
private theorem lim_pseF_eq (τ : SpeciesTree (Fin 5)) (hτ : τ.clusters = pseudocaterpillar5)
    {i : ℕ} (hi : i ∈ Icc 1 15) :
    u τ i = lim_pseF i (exp (-τ.length {0, 1})) (exp (-τ.length {3, 4}))
      (exp (-τ.length {0, 1, 3, 4})) := by
  obtain ⟨h1, h2, h3, h4, h13, h5, h6, h7, h9, h10, h12, h14, h15, h8, h11⟩ := equation13 τ hτ
  obtain ⟨hi1, hi15⟩ := mem_Icc.1 hi
  interval_cases i <;>
    simp only [lim_pseF, h1, h2, h3, h4, h13, h5, h6, h7, h9, h10, h12, h14, h15, h8, h11,
      Finset.mem_insert, Finset.mem_singleton, Nat.reduceEqDiff, or_false, or_true, ↓reduceIte]

/-- **Setting branch lengths to `0` in the formula of a binary representative.** If every species
tree with the clusters `H` has `u_i = F(e^{-ℓ(A)}, e^{-ℓ(B)}, e^{-ℓ(C)})` with `F` continuous, then
a species tree whose clusters are among those of `H` has `u_i` given by `F` at the lengths of its
edges, with the length `0` on the edges of `H` that it contracts: its distribution is the limit of
those of `H` as the contracted lengths tend to `0` (`section5_limit`, `lim_unrootedDist_eq`). -/
private theorem lim_u_eq (σ : SpeciesTree (Fin 5)) {H : Finset (Finset (Fin 5))}
    (hH : IsHierarchy H) (hsub : σ.clusters ⊆ H) (i : ℕ) (A B C : Finset (Fin 5))
    (F : ℝ → ℝ → ℝ → ℝ) (hF : Continuous fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2)
    (hτ : ∀ τ : SpeciesTree (Fin 5), τ.clusters = H →
      u τ i = F (exp (-τ.length A)) (exp (-τ.length B)) (exp (-τ.length C))) :
    u σ i = F (exp (-if A ∈ σ.clusters then σ.length A else 0))
      (exp (-if B ∈ σ.clusters then σ.length B else 0))
      (exp (-if C ∈ σ.clusters then σ.length C else 0)) :=
  lim_unrootedDist_eq σ hH hsub (T5 i) (fun ℓ => F (exp (-ℓ A)) (exp (-ℓ B)) (exp (-ℓ C))) hτ
    (hF.comp ((lim_continuous_length σ A).neg.rexp.prodMk
      ((lim_continuous_length σ B).neg.rexp.prodMk
        (lim_continuous_length σ C).neg.rexp))).continuousAt

/-- The species trees obtained from the balanced tree `(((a,b):x,c):y,(d,e):z)` by contracting
edges: equation (11) with the lengths of the contracted edges set to `0`. -/
private theorem lim_u_bal (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters ⊆ balanced5) {i : ℕ}
    (hi : i ∈ Icc 1 15) :
    u σ i = lim_balF i
      (exp (-if ({0, 1} : Finset (Fin 5)) ∈ σ.clusters then σ.length {0, 1} else 0))
      (exp (-if ({0, 1, 2} : Finset (Fin 5)) ∈ σ.clusters then σ.length {0, 1, 2} else 0))
      (exp (-if ({3, 4} : Finset (Fin 5)) ∈ σ.clusters then σ.length {3, 4} else 0)) :=
  lim_u_eq σ ⟨by decide, by decide, by decide, by decide⟩ hσ i _ _ _ (lim_balF i)
    (by unfold lim_balF; split_ifs <;> fun_prop) fun τ hτ => lim_balF_eq τ hτ hi

/-- The species trees obtained from the caterpillar `((((a,b):x,c):y,d):z,e)` by contracting
edges: equation (12) with the lengths of the contracted edges set to `0`. -/
private theorem lim_u_cat (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters ⊆ caterpillar5) {i : ℕ}
    (hi : i ∈ Icc 1 15) :
    u σ i = lim_catF i
      (exp (-if ({0, 1} : Finset (Fin 5)) ∈ σ.clusters then σ.length {0, 1} else 0))
      (exp (-if ({0, 1, 2} : Finset (Fin 5)) ∈ σ.clusters then σ.length {0, 1, 2} else 0))
      (exp (-if ({0, 1, 2, 3} : Finset (Fin 5)) ∈ σ.clusters then σ.length {0, 1, 2, 3}
        else 0)) :=
  lim_u_eq σ ⟨by decide, by decide, by decide, by decide⟩ hσ i _ _ _ (lim_catF i)
    (by unfold lim_catF; split_ifs <;> fun_prop) fun τ hτ => lim_catF_eq τ hτ hi

/-- The species trees obtained from the pseudocaterpillar `(((a,b):x,(d,e):y):z,c)` by contracting
edges: equation (13) with the lengths of the contracted edges set to `0`. -/
private theorem lim_u_pse (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters ⊆ pseudocaterpillar5)
    {i : ℕ} (hi : i ∈ Icc 1 15) :
    u σ i = lim_pseF i
      (exp (-if ({0, 1} : Finset (Fin 5)) ∈ σ.clusters then σ.length {0, 1} else 0))
      (exp (-if ({3, 4} : Finset (Fin 5)) ∈ σ.clusters then σ.length {3, 4} else 0))
      (exp (-if ({0, 1, 3, 4} : Finset (Fin 5)) ∈ σ.clusters then σ.length {0, 1, 3, 4}
        else 0)) :=
  lim_u_eq σ ⟨by decide, by decide, by decide, by decide⟩ hσ i _ _ _ (lim_pseF i)
    (by unfold lim_pseF; split_ifs <;> fun_prop) fun τ hτ => lim_pseF_eq τ hτ hi

/-- **Table 7**: the equivalence classes of equiprobable gene trees and the unrooted gene tree
distributions of the nonbinary 5-taxon representatives `P₁, …, P₉`, in terms of the transformed
lengths of their internal edges. For each representative the value of `u_i` is given for every
`i`; `X`, `Y`, `Z` denote `e^{-x}`, `e^{-y}`, `e^{-z}` for the edges labelled `x`, `y`, `z` in
Table 6.

As in the paper (l.944), the formulas are those of Appendix B for a resolved tree with one or more
branch lengths set to `0`: each `Pₖ` is the contraction of a binary representative with the same
labels, `P₁, P₂, P₄, P₆, P₈` of the balanced tree `(((a,b):x,c):y,(d,e):z)`, `P₃, P₉` of the
caterpillar `((((a,b):x,c):y,d):z,e)` and `P₅, P₇` of the pseudocaterpillar
`(((a,b):x,(d,e):y):z,c)`, and its distribution is the limit of the representative's as the
contracted lengths tend to `0` (`lim_u_bal`, `lim_u_cat`, `lim_u_pse`). -/
theorem table7 (σ : SpeciesTree (Fin 5)) (i : ℕ) (hi : i ∈ Icc 1 15) :
    (σ.clusters = polytomy5 1 → u σ i = 1 / 15) ∧
    (σ.clusters = polytomy5 2 →
      let Z := exp (-σ.length {3, 4})
      u σ i = if i ∈ ({1, 4, 13} : Finset ℕ) then 1 / 3 - 4 / 15 * Z else 1 / 15 * Z) ∧
    (σ.clusters = polytomy5 3 →
      let Z := exp (-σ.length {0, 1, 2, 3})
      u σ i = if i ∈ ({3, 6, 9} : Finset ℕ) then 1 / 9 - 2 / 45 * Z ^ 6
        else 1 / 18 + 1 / 90 * Z ^ 6) ∧
    (σ.clusters = polytomy5 4 →
      let Y := exp (-σ.length {0, 1, 2})
      u σ i = if i ∈ ({1, 4, 13} : Finset ℕ) then 1 / 3 - 1 / 3 * Y + 1 / 15 * Y ^ 3
        else if i ∈ ({2, 3, 5, 6, 9, 12} : Finset ℕ) then 1 / 6 * Y - 1 / 10 * Y ^ 3
        else 1 / 15 * Y ^ 3) ∧
    (σ.clusters = polytomy5 5 →
      let X := exp (-σ.length {0, 1})
      let Y := exp (-σ.length {3, 4})
      u σ i = if i = 1 then 1 - 2 / 3 * X - 2 / 3 * Y + 2 / 5 * X * Y
        else if i ∈ ({2, 3} : Finset ℕ) then 1 / 3 * Y - 4 / 15 * X * Y
        else if i ∈ ({4, 13} : Finset ℕ) then 1 / 3 * X - 4 / 15 * X * Y
        else 1 / 15 * X * Y) ∧
    (σ.clusters = polytomy5 6 →
      let X := exp (-σ.length {0, 1})
      let Y := exp (-σ.length {0, 1, 2})
      u σ i = if i = 1 then 1 - 2 / 3 * X - 2 / 3 * Y + 1 / 3 * X * Y + 1 / 15 * X * Y ^ 3
        else if i ∈ ({2, 3} : Finset ℕ) then 1 / 3 * Y - 1 / 6 * X * Y - 1 / 10 * X * Y ^ 3
        else if i ∈ ({4, 13} : Finset ℕ) then 1 / 3 * X - 1 / 3 * X * Y + 1 / 15 * X * Y ^ 3
        else if i ∈ ({5, 6, 9, 12} : Finset ℕ) then 1 / 6 * X * Y - 1 / 10 * X * Y ^ 3
        else 1 / 15 * X * Y ^ 3) ∧
    (σ.clusters = polytomy5 7 →
      let X := exp (-σ.length {0, 1})
      let Z := exp (-σ.length {0, 1, 3, 4})
      u σ i = if i = 1 then 1 / 3 - 2 / 9 * X - 2 / 45 * X * Z ^ 6
        else if i ∈ ({2, 3} : Finset ℕ) then 1 / 3 - 5 / 18 * X + 1 / 90 * X * Z ^ 6
        else if i ∈ ({8, 11} : Finset ℕ) then 1 / 9 * X - 2 / 45 * X * Z ^ 6
        else 1 / 18 * X + 1 / 90 * X * Z ^ 6) ∧
    (σ.clusters = polytomy5 8 →
      let Y := exp (-σ.length {0, 1, 2})
      let Z := exp (-σ.length {3, 4})
      u σ i = if i ∈ ({1, 4, 13} : Finset ℕ) then 1 / 3 - 1 / 3 * Y * Z + 1 / 15 * Y ^ 3 * Z
        else if i ∈ ({2, 3, 5, 6, 9, 12} : Finset ℕ) then 1 / 6 * Y * Z - 1 / 10 * Y ^ 3 * Z
        else 1 / 15 * Y ^ 3 * Z) ∧
    (σ.clusters = polytomy5 9 →
      let Y := exp (-σ.length {0, 1, 2})
      let Z := exp (-σ.length {0, 1, 2, 3})
      u σ i = if i ∈ ({1, 4, 13} : Finset ℕ) then
          1 / 3 - 1 / 3 * Y + 1 / 18 * Y ^ 3 + 1 / 90 * Y ^ 3 * Z ^ 6
        else if i ∈ ({2, 5, 12} : Finset ℕ) then
          1 / 6 * Y - 1 / 9 * Y ^ 3 + 1 / 90 * Y ^ 3 * Z ^ 6
        else if i ∈ ({3, 6, 9} : Finset ℕ) then
          1 / 6 * Y - 1 / 18 * Y ^ 3 - 2 / 45 * Y ^ 3 * Z ^ 6
        else 1 / 18 * Y ^ 3 + 1 / 90 * Y ^ 3 * Z ^ 6) := by
  obtain ⟨hi1, hi15⟩ := Finset.mem_Icc.1 hi
  -- `Pₖ` contracts edges of a binary representative with the same labels: (11)–(13) with the
  -- contracted lengths set to `0`, that is with `X`, `Y` or `Z` equal to `1`
  refine ⟨fun hσ => ?_, fun hσ => ?_, fun hσ => ?_, fun hσ => ?_, fun hσ => ?_, fun hσ => ?_,
    fun hσ => ?_, fun hσ => ?_, fun hσ => ?_⟩ <;> (try dsimp only)
  on_goal 1 => -- `P₁ = (a,b,c,d,e)`: the balanced tree with `x, y, z → 0`
    rw [lim_u_bal σ (by rw [hσ]; decide) hi, hσ]
    simp only [show ({0, 1} : Finset (Fin 5)) ∉ polytomy5 1 by decide,
      show ({0, 1, 2} : Finset (Fin 5)) ∉ polytomy5 1 by decide,
      show ({3, 4} : Finset (Fin 5)) ∉ polytomy5 1 by decide, ↓reduceIte, neg_zero,
      exp_zero]
  on_goal 2 => -- `P₂ = (a,b,c,(d,e))`: the balanced tree with `x, y → 0`
    rw [lim_u_bal σ (by rw [hσ]; decide) hi, hσ]
    simp only [show ({0, 1} : Finset (Fin 5)) ∉ polytomy5 2 by decide,
      show ({0, 1, 2} : Finset (Fin 5)) ∉ polytomy5 2 by decide,
      show ({3, 4} : Finset (Fin 5)) ∈ polytomy5 2 by decide, ↓reduceIte, neg_zero,
      exp_zero]
  on_goal 3 => -- `P₃ = ((a,b,c,d),e)`: the caterpillar with `x, y → 0`
    rw [lim_u_cat σ (by rw [hσ]; decide) hi, hσ]
    simp only [show ({0, 1} : Finset (Fin 5)) ∉ polytomy5 3 by decide,
      show ({0, 1, 2} : Finset (Fin 5)) ∉ polytomy5 3 by decide,
      show ({0, 1, 2, 3} : Finset (Fin 5)) ∈ polytomy5 3 by decide, ↓reduceIte, neg_zero,
      exp_zero]
  on_goal 4 => -- `P₄ = ((a,b,c),d,e)`: the balanced tree with `x, z → 0`
    rw [lim_u_bal σ (by rw [hσ]; decide) hi, hσ]
    simp only [show ({0, 1} : Finset (Fin 5)) ∉ polytomy5 4 by decide,
      show ({0, 1, 2} : Finset (Fin 5)) ∈ polytomy5 4 by decide,
      show ({3, 4} : Finset (Fin 5)) ∉ polytomy5 4 by decide, ↓reduceIte, neg_zero,
      exp_zero]
  on_goal 5 => -- `P₅ = ((a,b),(d,e),c)`: the pseudocaterpillar with `z → 0`
    rw [lim_u_pse σ (by rw [hσ]; decide) hi, hσ]
    simp only [show ({0, 1} : Finset (Fin 5)) ∈ polytomy5 5 by decide,
      show ({3, 4} : Finset (Fin 5)) ∈ polytomy5 5 by decide,
      show ({0, 1, 3, 4} : Finset (Fin 5)) ∉ polytomy5 5 by decide, ↓reduceIte, neg_zero,
      exp_zero]
  on_goal 6 => -- `P₆ = (((a,b),c),d,e)`: the balanced tree with `z → 0`
    rw [lim_u_bal σ (by rw [hσ]; decide) hi, hσ]
    simp only [show ({0, 1} : Finset (Fin 5)) ∈ polytomy5 6 by decide,
      show ({0, 1, 2} : Finset (Fin 5)) ∈ polytomy5 6 by decide,
      show ({3, 4} : Finset (Fin 5)) ∉ polytomy5 6 by decide, ↓reduceIte, neg_zero,
      exp_zero]
  on_goal 7 => -- `P₇ = (((a,b),d,e),c)`: the pseudocaterpillar with `y → 0`
    rw [lim_u_pse σ (by rw [hσ]; decide) hi, hσ]
    simp only [show ({0, 1} : Finset (Fin 5)) ∈ polytomy5 7 by decide,
      show ({3, 4} : Finset (Fin 5)) ∉ polytomy5 7 by decide,
      show ({0, 1, 3, 4} : Finset (Fin 5)) ∈ polytomy5 7 by decide, ↓reduceIte, neg_zero,
      exp_zero]
  on_goal 8 => -- `P₈ = ((a,b,c),(d,e))`: the balanced tree with `x → 0`
    rw [lim_u_bal σ (by rw [hσ]; decide) hi, hσ]
    simp only [show ({0, 1} : Finset (Fin 5)) ∉ polytomy5 8 by decide,
      show ({0, 1, 2} : Finset (Fin 5)) ∈ polytomy5 8 by decide,
      show ({3, 4} : Finset (Fin 5)) ∈ polytomy5 8 by decide, ↓reduceIte, neg_zero,
      exp_zero]
  on_goal 9 => -- `P₉ = (((a,b,c),d),e)`: the caterpillar with `x → 0`
    rw [lim_u_cat σ (by rw [hσ]; decide) hi, hσ]
    simp only [show ({0, 1} : Finset (Fin 5)) ∉ polytomy5 9 by decide,
      show ({0, 1, 2} : Finset (Fin 5)) ∈ polytomy5 9 by decide,
      show ({0, 1, 2, 3} : Finset (Fin 5)) ∈ polytomy5 9 by decide, ↓reduceIte, neg_zero,
      exp_zero]
  -- the formulas with `X`, `Y` or `Z` equal to `1` are those of Table 7
  all_goals
    interval_cases i <;>
      simp only [lim_balF, lim_catF, lim_pseF, Finset.mem_insert, Finset.mem_singleton,
        Nat.reduceEqDiff, or_false, or_true, ↓reduceIte] <;>
      ring

/-- The class of `T_i` for the nonbinary representative `P_k` in Table 7, named by its smallest
index. -/
def polytomyClass : ℕ → ℕ → ℕ
  | 1, _ => 1
  | 2, i => if i ∈ ({1, 4, 13} : Finset ℕ) then 1 else 2
  | 3, i => if i ∈ ({3, 6, 9} : Finset ℕ) then 3 else 1
  | 4, i => if i ∈ ({1, 4, 13} : Finset ℕ) then 1
      else if i ∈ ({2, 3, 5, 6, 9, 12} : Finset ℕ) then 2 else 7
  | 5, i => if i = 1 then 1 else if i ∈ ({2, 3} : Finset ℕ) then 2
      else if i ∈ ({4, 13} : Finset ℕ) then 4 else 5
  | 6, i => if i = 1 then 1 else if i ∈ ({2, 3} : Finset ℕ) then 2
      else if i ∈ ({4, 13} : Finset ℕ) then 4 else if i ∈ ({5, 6, 9, 12} : Finset ℕ) then 5 else 7
  | 7, i => if i = 1 then 1 else if i ∈ ({2, 3} : Finset ℕ) then 2
      else if i ∈ ({8, 11} : Finset ℕ) then 8 else 4
  | 8, i => if i ∈ ({1, 4, 13} : Finset ℕ) then 1
      else if i ∈ ({2, 3, 5, 6, 9, 12} : Finset ℕ) then 2 else 7
  | 9, i => if i ∈ ({1, 4, 13} : Finset ℕ) then 1 else if i ∈ ({2, 5, 12} : Finset ℕ) then 2
      else if i ∈ ({3, 6, 9} : Finset ℕ) then 3 else 7
  | _, i => i

/-! ### Helpers: the formulas of Table 7 on the representatives of the classes -/

/-- For a non-root cluster `A` of a species tree, `0 < e^{-ℓ(A)} < 1`. -/
private theorem appc_bounds (σ : SpeciesTree (Fin 5)) {A : Finset (Fin 5)}
    (hA : A ∈ σ.clusters) (hne : A ≠ univ) : 0 < exp (-σ.length A) ∧ exp (-σ.length A) < 1 :=
  ⟨exp_pos _, Real.exp_lt_one_iff.2 (neg_lt_zero.2 (σ.length_pos A hA hne))⟩

/-- A species tree with the clusters `H` on which `e^{-ℓ(A)} = a` and `e^{-ℓ(B)} = b`, for two
distinct sets `A`, `B` of at least two taxa (`B` need not be a cluster). -/
private theorem appc_exists (H : Finset (Finset (Fin 5))) (h₁ : univ ∈ H)
    (h₂ : ∀ x : Fin 5, {x} ∈ H) (h₃ : ∀ A ∈ H, A.Nonempty)
    (h₄ : ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) (A B : Finset (Fin 5))
    (hA : 2 ≤ #A) (hB : 2 ≤ #B) (hAB : A ≠ B) (a b : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) :
    ∃ σ : SpeciesTree (Fin 5), σ.clusters = H ∧ exp (-σ.length A) = a ∧
      exp (-σ.length B) = b := by
  refine ⟨SpeciesTree.ofLengths H (fun C => if C = A then -log a else -log b) h₁ h₂ h₃ h₄
    (fun C _ _ _ => ?_), rfl, ?_, ?_⟩
  · split_ifs
    exacts [neg_pos.2 (log_neg ha ha1), neg_pos.2 (log_neg hb hb1)]
  · simp [SpeciesTree.ofLengths, show ¬ #A ≤ 1 by omega, exp_log ha]
  · simp [SpeciesTree.ofLengths, show ¬ #B ≤ 1 by omega, hAB.symm, exp_log hb]

/-- Table 7 for `P₂` on the representatives of the classes. -/
private theorem appc_vals2 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = polytomy5 2) :
    let Z := exp (-σ.length {3, 4})
    0 < Z ∧ Z < 1 ∧ u σ 1 = 1 / 3 - 4 / 15 * Z ∧ u σ 2 = 1 / 15 * Z := by
  obtain ⟨hZ, hZ1⟩ := appc_bounds σ (A := {3, 4}) (by rw [h]; decide) (by decide)
  have e1 := (table7 σ 1 (by decide)).2.1 h
  have e2 := (table7 σ 2 (by decide)).2.1 h
  simp only at e1 e2 ⊢
  norm_num at e1 e2
  exact ⟨hZ, hZ1, by linarith, by linarith⟩

/-- Table 7 for `P₃` on the representatives of the classes. -/
private theorem appc_vals3 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = polytomy5 3) :
    let Z := exp (-σ.length {0, 1, 2, 3})
    0 < Z ∧ Z < 1 ∧ u σ 1 = 1 / 18 + 1 / 90 * Z ^ 6 ∧ u σ 3 = 1 / 9 - 2 / 45 * Z ^ 6 := by
  obtain ⟨hZ, hZ1⟩ := appc_bounds σ (A := {0, 1, 2, 3}) (by rw [h]; decide) (by decide)
  have e1 := (table7 σ 1 (by decide)).2.2.1 h
  have e3 := (table7 σ 3 (by decide)).2.2.1 h
  simp only at e1 e3 ⊢
  norm_num at e1 e3
  exact ⟨hZ, hZ1, by linarith, by linarith⟩

/-- Table 7 for `P₄` on the representatives of the classes. -/
private theorem appc_vals4 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = polytomy5 4) :
    let Y := exp (-σ.length {0, 1, 2})
    0 < Y ∧ Y < 1 ∧ u σ 1 = 1 / 3 - 1 / 3 * Y + 1 / 15 * Y ^ 3 ∧
      u σ 2 = 1 / 6 * Y - 1 / 10 * Y ^ 3 ∧ u σ 7 = 1 / 15 * Y ^ 3 := by
  obtain ⟨hY, hY1⟩ := appc_bounds σ (A := {0, 1, 2}) (by rw [h]; decide) (by decide)
  have e1 := (table7 σ 1 (by decide)).2.2.2.1 h
  have e2 := (table7 σ 2 (by decide)).2.2.2.1 h
  have e7 := (table7 σ 7 (by decide)).2.2.2.1 h
  simp only at e1 e2 e7 ⊢
  norm_num at e1 e2 e7
  exact ⟨hY, hY1, by linarith, by linarith, by linarith⟩

/-- Table 7 for `P₅` on the representatives of the classes. -/
private theorem appc_vals5 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = polytomy5 5) :
    let X := exp (-σ.length {0, 1})
    let Y := exp (-σ.length {3, 4})
    0 < X ∧ X < 1 ∧ 0 < Y ∧ Y < 1 ∧ u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y + 2 / 5 * X * Y ∧
      u σ 2 = 1 / 3 * Y - 4 / 15 * X * Y ∧ u σ 4 = 1 / 3 * X - 4 / 15 * X * Y ∧
      u σ 5 = 1 / 15 * X * Y := by
  obtain ⟨hX, hX1⟩ := appc_bounds σ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨hY, hY1⟩ := appc_bounds σ (A := {3, 4}) (by rw [h]; decide) (by decide)
  have e1 := (table7 σ 1 (by decide)).2.2.2.2.1 h
  have e2 := (table7 σ 2 (by decide)).2.2.2.2.1 h
  have e4 := (table7 σ 4 (by decide)).2.2.2.2.1 h
  have e5 := (table7 σ 5 (by decide)).2.2.2.2.1 h
  simp only at e1 e2 e4 e5 ⊢
  norm_num at e1 e2 e4 e5
  exact ⟨hX, hX1, hY, hY1, by linarith, by linarith, by linarith, by linarith⟩

/-- Table 7 for `P₆` on the representatives of the classes. -/
private theorem appc_vals6 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = polytomy5 6) :
    let X := exp (-σ.length {0, 1})
    let Y := exp (-σ.length {0, 1, 2})
    0 < X ∧ X < 1 ∧ 0 < Y ∧ Y < 1 ∧
      u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y + 1 / 3 * X * Y + 1 / 15 * X * Y ^ 3 ∧
      u σ 2 = 1 / 3 * Y - 1 / 6 * X * Y - 1 / 10 * X * Y ^ 3 ∧
      u σ 4 = 1 / 3 * X - 1 / 3 * X * Y + 1 / 15 * X * Y ^ 3 ∧
      u σ 5 = 1 / 6 * X * Y - 1 / 10 * X * Y ^ 3 ∧ u σ 7 = 1 / 15 * X * Y ^ 3 := by
  obtain ⟨hX, hX1⟩ := appc_bounds σ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨hY, hY1⟩ := appc_bounds σ (A := {0, 1, 2}) (by rw [h]; decide) (by decide)
  have e1 := (table7 σ 1 (by decide)).2.2.2.2.2.1 h
  have e2 := (table7 σ 2 (by decide)).2.2.2.2.2.1 h
  have e4 := (table7 σ 4 (by decide)).2.2.2.2.2.1 h
  have e5 := (table7 σ 5 (by decide)).2.2.2.2.2.1 h
  have e7 := (table7 σ 7 (by decide)).2.2.2.2.2.1 h
  simp only at e1 e2 e4 e5 e7 ⊢
  norm_num at e1 e2 e4 e5 e7
  exact ⟨hX, hX1, hY, hY1, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Table 7 for `P₇` on the representatives of the classes. -/
private theorem appc_vals7 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = polytomy5 7) :
    let X := exp (-σ.length {0, 1})
    let Z := exp (-σ.length {0, 1, 3, 4})
    0 < X ∧ X < 1 ∧ 0 < Z ∧ Z < 1 ∧ u σ 1 = 1 / 3 - 2 / 9 * X - 2 / 45 * X * Z ^ 6 ∧
      u σ 2 = 1 / 3 - 5 / 18 * X + 1 / 90 * X * Z ^ 6 ∧
      u σ 4 = 1 / 18 * X + 1 / 90 * X * Z ^ 6 ∧ u σ 8 = 1 / 9 * X - 2 / 45 * X * Z ^ 6 := by
  obtain ⟨hX, hX1⟩ := appc_bounds σ (A := {0, 1}) (by rw [h]; decide) (by decide)
  obtain ⟨hZ, hZ1⟩ := appc_bounds σ (A := {0, 1, 3, 4}) (by rw [h]; decide) (by decide)
  have e1 := (table7 σ 1 (by decide)).2.2.2.2.2.2.1 h
  have e2 := (table7 σ 2 (by decide)).2.2.2.2.2.2.1 h
  have e4 := (table7 σ 4 (by decide)).2.2.2.2.2.2.1 h
  have e8 := (table7 σ 8 (by decide)).2.2.2.2.2.2.1 h
  simp only at e1 e2 e4 e8 ⊢
  norm_num at e1 e2 e4 e8
  exact ⟨hX, hX1, hZ, hZ1, by linarith, by linarith, by linarith, by linarith⟩

/-- Table 7 for `P₈` on the representatives of the classes. -/
private theorem appc_vals8 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = polytomy5 8) :
    let Y := exp (-σ.length {0, 1, 2})
    let Z := exp (-σ.length {3, 4})
    0 < Y ∧ Y < 1 ∧ 0 < Z ∧ Z < 1 ∧ u σ 1 = 1 / 3 - 1 / 3 * Y * Z + 1 / 15 * Y ^ 3 * Z ∧
      u σ 2 = 1 / 6 * Y * Z - 1 / 10 * Y ^ 3 * Z ∧ u σ 7 = 1 / 15 * Y ^ 3 * Z := by
  obtain ⟨hY, hY1⟩ := appc_bounds σ (A := {0, 1, 2}) (by rw [h]; decide) (by decide)
  obtain ⟨hZ, hZ1⟩ := appc_bounds σ (A := {3, 4}) (by rw [h]; decide) (by decide)
  have e1 := (table7 σ 1 (by decide)).2.2.2.2.2.2.2.1 h
  have e2 := (table7 σ 2 (by decide)).2.2.2.2.2.2.2.1 h
  have e7 := (table7 σ 7 (by decide)).2.2.2.2.2.2.2.1 h
  simp only at e1 e2 e7 ⊢
  norm_num at e1 e2 e7
  exact ⟨hY, hY1, hZ, hZ1, by linarith, by linarith, by linarith⟩

/-- Table 7 for `P₉` on the representatives of the classes. -/
private theorem appc_vals9 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = polytomy5 9) :
    let Y := exp (-σ.length {0, 1, 2})
    let Z := exp (-σ.length {0, 1, 2, 3})
    0 < Y ∧ Y < 1 ∧ 0 < Z ∧ Z < 1 ∧
      u σ 1 = 1 / 3 - 1 / 3 * Y + 1 / 18 * Y ^ 3 + 1 / 90 * Y ^ 3 * Z ^ 6 ∧
      u σ 2 = 1 / 6 * Y - 1 / 9 * Y ^ 3 + 1 / 90 * Y ^ 3 * Z ^ 6 ∧
      u σ 3 = 1 / 6 * Y - 1 / 18 * Y ^ 3 - 2 / 45 * Y ^ 3 * Z ^ 6 ∧
      u σ 7 = 1 / 18 * Y ^ 3 + 1 / 90 * Y ^ 3 * Z ^ 6 := by
  obtain ⟨hY, hY1⟩ := appc_bounds σ (A := {0, 1, 2}) (by rw [h]; decide) (by decide)
  obtain ⟨hZ, hZ1⟩ := appc_bounds σ (A := {0, 1, 2, 3}) (by rw [h]; decide) (by decide)
  have e1 := (table7 σ 1 (by decide)).2.2.2.2.2.2.2.2 h
  have e2 := (table7 σ 2 (by decide)).2.2.2.2.2.2.2.2 h
  have e3 := (table7 σ 3 (by decide)).2.2.2.2.2.2.2.2 h
  have e7 := (table7 σ 7 (by decide)).2.2.2.2.2.2.2.2 h
  simp only at e1 e2 e3 e7 ⊢
  norm_num at e1 e2 e3 e7
  exact ⟨hY, hY1, hZ, hZ1, by linarith, by linarith, by linarith, by linarith⟩

/-! ### Helpers: the classes of Table 7 -/

private theorem appc_cls_mem : ∀ k ∈ Icc 1 9, ∀ i ∈ Icc 1 15, polytomyClass k i ∈ Icc 1 15 := by
  decide

/-- Each `u_i` equals `u` of the name of the class of `T_i` in Table 7. -/
private theorem appc_cls (k : ℕ) (hk : k ∈ Icc 1 9) (σ : SpeciesTree (Fin 5))
    (hσ : σ.clusters = polytomy5 k) (i : ℕ) (hi : i ∈ Icc 1 15) :
    u σ i = u σ (polytomyClass k i) := by
  have a := table7 σ i hi
  have b := table7 σ _ (appc_cls_mem k hk i hi)
  obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
  obtain ⟨hk1, hk2⟩ := mem_Icc.1 hk
  interval_cases k
  · rw [a.1 hσ, b.1 hσ]
  · rw [a.2.1 hσ, b.2.1 hσ]
    interval_cases i <;> simp [polytomyClass]
  · rw [a.2.2.1 hσ, b.2.2.1 hσ]
    interval_cases i <;> simp [polytomyClass]
  · rw [a.2.2.2.1 hσ, b.2.2.2.1 hσ]
    interval_cases i <;> simp [polytomyClass]
  · rw [a.2.2.2.2.1 hσ, b.2.2.2.2.1 hσ]
    interval_cases i <;> simp [polytomyClass]
  · rw [a.2.2.2.2.2.1 hσ, b.2.2.2.2.2.1 hσ]
    interval_cases i <;> simp [polytomyClass]
  · rw [a.2.2.2.2.2.2.1 hσ, b.2.2.2.2.2.2.1 hσ]
    interval_cases i <;> simp [polytomyClass]
  · rw [a.2.2.2.2.2.2.2.1 hσ, b.2.2.2.2.2.2.2.1 hσ]
    interval_cases i <;> simp [polytomyClass]
  · rw [a.2.2.2.2.2.2.2.2 hσ, b.2.2.2.2.2.2.2.2 hσ]
    interval_cases i <;> simp [polytomyClass]

/-- For each nonbinary representative `P_k`, a species tree on which the classes of Table 7 have
distinct probabilities (all internal edges with `e^{-ℓ} = 1/2`, except the edge `{d,e}` of `P₅`
and the edge `{a,b,c}` of `P₆` with `e^{-ℓ} = 1/4`). -/
private theorem appc_distinct (k : ℕ) (hk : k ∈ Icc 1 9) :
    ∃ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 k ∧
      ∀ a ∈ (Icc 1 15).image (polytomyClass k), ∀ b ∈ (Icc 1 15).image (polytomyClass k),
        u σ a = u σ b → a = b := by
  obtain ⟨hk1, hk2⟩ := mem_Icc.1 hk
  interval_cases k
  · obtain ⟨σ, hσ, -, -⟩ := appc_exists (polytomy5 1) (by decide) (by decide) (by decide)
      (by decide) {0, 1} {0, 1, 2} (by decide) (by decide) (by decide) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨σ, hσ, ?_⟩
    rw [show (Icc 1 15).image (polytomyClass 1) = {1} by decide]
    intro a ha b hb _
    rw [mem_singleton.1 ha, mem_singleton.1 hb]
  · obtain ⟨σ, hσ, hz, -⟩ := appc_exists (polytomy5 2) (by decide) (by decide) (by decide)
      (by decide) {3, 4} {0, 1} (by decide) (by decide) (by decide) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, -, e1, e2⟩ := appc_vals2 σ hσ
    rw [hz] at e1 e2
    norm_num at e1 e2
    refine ⟨σ, hσ, ?_⟩
    rw [show (Icc 1 15).image (polytomyClass 2) = {1, 2} by decide]
    intro a ha b hb e
    fin_cases ha <;> fin_cases hb <;> first | rfl | (exfalso; linarith)
  · obtain ⟨σ, hσ, hz, -⟩ := appc_exists (polytomy5 3) (by decide) (by decide) (by decide)
      (by decide) {0, 1, 2, 3} {0, 1} (by decide) (by decide) (by decide) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, -, e1, e3⟩ := appc_vals3 σ hσ
    rw [hz] at e1 e3
    norm_num at e1 e3
    refine ⟨σ, hσ, ?_⟩
    rw [show (Icc 1 15).image (polytomyClass 3) = {1, 3} by decide]
    intro a ha b hb e
    fin_cases ha <;> fin_cases hb <;> first | rfl | (exfalso; linarith)
  · obtain ⟨σ, hσ, hy, -⟩ := appc_exists (polytomy5 4) (by decide) (by decide) (by decide)
      (by decide) {0, 1, 2} {0, 1} (by decide) (by decide) (by decide) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, -, e1, e2, e7⟩ := appc_vals4 σ hσ
    rw [hy] at e1 e2 e7
    norm_num at e1 e2 e7
    refine ⟨σ, hσ, ?_⟩
    rw [show (Icc 1 15).image (polytomyClass 4) = {1, 2, 7} by decide]
    intro a ha b hb e
    fin_cases ha <;> fin_cases hb <;> first | rfl | (exfalso; linarith)
  · obtain ⟨σ, hσ, hx, hy⟩ := appc_exists (polytomy5 5) (by decide) (by decide) (by decide)
      (by decide) {0, 1} {3, 4} (by decide) (by decide) (by decide) (1 / 2) (1 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, -, -, -, e1, e2, e4, e5⟩ := appc_vals5 σ hσ
    rw [hx, hy] at e1 e2 e4 e5
    norm_num at e1 e2 e4 e5
    refine ⟨σ, hσ, ?_⟩
    rw [show (Icc 1 15).image (polytomyClass 5) = {1, 2, 4, 5} by decide]
    intro a ha b hb e
    fin_cases ha <;> fin_cases hb <;> first | rfl | (exfalso; linarith)
  · obtain ⟨σ, hσ, hx, hy⟩ := appc_exists (polytomy5 6) (by decide) (by decide) (by decide)
      (by decide) {0, 1} {0, 1, 2} (by decide) (by decide) (by decide) (1 / 2) (1 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, -, -, -, e1, e2, e4, e5, e7⟩ := appc_vals6 σ hσ
    rw [hx, hy] at e1 e2 e4 e5 e7
    norm_num at e1 e2 e4 e5 e7
    refine ⟨σ, hσ, ?_⟩
    rw [show (Icc 1 15).image (polytomyClass 6) = {1, 2, 4, 5, 7} by decide]
    intro a ha b hb e
    fin_cases ha <;> fin_cases hb <;> first | rfl | (exfalso; linarith)
  · obtain ⟨σ, hσ, hx, hz⟩ := appc_exists (polytomy5 7) (by decide) (by decide) (by decide)
      (by decide) {0, 1} {0, 1, 3, 4} (by decide) (by decide) (by decide) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, -, -, -, e1, e2, e4, e8⟩ := appc_vals7 σ hσ
    rw [hx, hz] at e1 e2 e4 e8
    norm_num at e1 e2 e4 e8
    refine ⟨σ, hσ, ?_⟩
    rw [show (Icc 1 15).image (polytomyClass 7) = {1, 2, 4, 8} by decide]
    intro a ha b hb e
    fin_cases ha <;> fin_cases hb <;> first | rfl | (exfalso; linarith)
  · obtain ⟨σ, hσ, hy, hz⟩ := appc_exists (polytomy5 8) (by decide) (by decide) (by decide)
      (by decide) {0, 1, 2} {3, 4} (by decide) (by decide) (by decide) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, -, -, -, e1, e2, e7⟩ := appc_vals8 σ hσ
    rw [hy, hz] at e1 e2 e7
    norm_num at e1 e2 e7
    refine ⟨σ, hσ, ?_⟩
    rw [show (Icc 1 15).image (polytomyClass 8) = {1, 2, 7} by decide]
    intro a ha b hb e
    fin_cases ha <;> fin_cases hb <;> first | rfl | (exfalso; linarith)
  · obtain ⟨σ, hσ, hy, hz⟩ := appc_exists (polytomy5 9) (by decide) (by decide) (by decide)
      (by decide) {0, 1, 2} {0, 1, 2, 3} (by decide) (by decide) (by decide) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, -, -, -, e1, e2, e3, e7⟩ := appc_vals9 σ hσ
    rw [hy, hz] at e1 e2 e3 e7
    norm_num at e1 e2 e3 e7
    refine ⟨σ, hσ, ?_⟩
    rw [show (Icc 1 15).image (polytomyClass 9) = {1, 2, 3, 7} by decide]
    intro a ha b hb e
    fin_cases ha <;> fin_cases hb <;> first | rfl | (exfalso; linarith)

/-! ### Helpers: the least probable classes -/

/-- If `f` is constant on the classes of `cls` and the class named `m` has a strictly smaller
value than every other class (named in `R`), then the least probable gene trees are those of the
class `m`. -/
private theorem appc_C_eq (f : ℕ → ℝ) (cls : ℕ → ℕ) (m : ℕ) (R : Finset ℕ)
    (hcls : ∀ i ∈ Icc 1 15, f i = f (cls i)) (hm : m ∈ Icc 1 15)
    (hR : ∀ i ∈ Icc 1 15, cls i = m ∨ cls i ∈ R) (hmin : ∀ r ∈ R, f m < f r)
    (C : Finset ℕ) (hC : ∀ i, i ∈ C ↔ i ∈ Icc 1 15 ∧ ∀ j ∈ Icc 1 15, f i ≤ f j) :
    C = {i ∈ Icc 1 15 | cls i = m} := by
  have key : ∀ j ∈ Icc 1 15, cls j ≠ m → f m < f j := by
    intro j hj hne
    rw [hcls j hj]
    exact hmin _ ((hR j hj).resolve_left hne)
  ext i
  rw [hC, mem_filter]
  constructor
  · rintro ⟨hi, h⟩
    exact ⟨hi, by_contra fun hne => absurd (h m hm) (not_le.2 (key i hi hne))⟩
  · rintro ⟨hi, hc⟩
    refine ⟨hi, fun j hj => ?_⟩
    rw [hcls i hi, hc]
    by_cases hj' : cls j = m
    · rw [hcls j hj, hj']
    · exact (key j hj hj').le

/-- If moreover the class named `m₂` has a strictly smaller value than every class other than `m`
and `m₂` (named in `R`), then the gene trees with the second smallest probability are those of the
class `m₂`. -/
private theorem appc_C2_eq (f : ℕ → ℝ) (cls : ℕ → ℕ) (m m₂ : ℕ) (R : Finset ℕ)
    (hcls : ∀ i ∈ Icc 1 15, f i = f (cls i)) (hm₂ : m₂ ∈ Icc 1 15) (hcm₂ : cls m₂ = m₂)
    (hne : m₂ ≠ m) (hR : ∀ i ∈ Icc 1 15, cls i = m ∨ cls i = m₂ ∨ cls i ∈ R)
    (hmin : ∀ r ∈ R, f m₂ < f r) (C C₂ : Finset ℕ) (hC : C = {i ∈ Icc 1 15 | cls i = m})
    (hC₂ : ∀ i, i ∈ C₂ ↔ i ∈ Icc 1 15 ∧ i ∉ C ∧ ∀ j ∈ Icc 1 15, j ∉ C → f i ≤ f j) :
    C₂ = {i ∈ Icc 1 15 | cls i = m₂} := by
  subst hC
  have key : ∀ j ∈ Icc 1 15, cls j ≠ m → cls j ≠ m₂ → f m₂ < f j := by
    intro j hj h1 h2
    rw [hcls j hj]
    exact hmin _ (((hR j hj).resolve_left h1).resolve_left h2)
  ext i
  simp only [hC₂, mem_filter, not_and]
  constructor
  · rintro ⟨hi, hiC, h⟩
    refine ⟨hi, by_contra fun hne₂ => ?_⟩
    exact absurd (h m₂ hm₂ (fun _ => by rw [hcm₂]; exact hne))
      (not_le.2 (key i hi (hiC hi) hne₂))
  · rintro ⟨hi, hc⟩
    refine ⟨hi, fun _ => by rw [hc]; exact hne, fun j hj hjC => ?_⟩
    rw [hcls i hi, hc]
    by_cases hj' : cls j = m₂
    · rw [hcls j hj, hj']
    · exact (key j hj (hjC hj) hj').le

/-- Each `u_k` equals `u` of the name of its class, for the caterpillar (by (12)). -/
private theorem appc_cat_cls (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    ∀ k ∈ Icc 1 15, u σ k = u σ (caterpillarClass k) := by
  obtain ⟨-, -, -, -, e13, -, e12, -, e9, -, e8, e10, e11, e14, e15⟩ := equation12 σ hσ
  intro k hk
  obtain ⟨hk1, hk2⟩ := mem_Icc.1 hk
  interval_cases k <;> simp only [caterpillarClass, e13, e12, e9, e8, e10, e11, e14, e15]

/-- Each `u_k` equals `u` of the name of its class, for the balanced tree (by (11)). -/
private theorem appc_bal_cls (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = balanced5) :
    ∀ k ∈ Icc 1 15, u σ k = u σ (balancedClass k) := by
  obtain ⟨-, -, e3, -, e13, -, e6, e9, e12, -, e8, e10, e11, e14, e15⟩ := equation11 σ hσ
  intro k hk
  obtain ⟨hk1, hk2⟩ := mem_Icc.1 hk
  interval_cases k <;> simp only [balancedClass, e3, e13, e6, e9, e12, e8, e10, e11, e14, e15]

/-- Each `u_k` equals `u` of the name of its class, for the pseudocaterpillar (by (13)). -/
private theorem appc_pse_cls (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) :
    ∀ k ∈ Icc 1 15, u σ k = u σ (pseudocaterpillarClass k) := by
  obtain ⟨-, -, e3, -, e13, -, e6, e7, e9, e10, e12, e14, e15, -, e11⟩ := equation13 σ hσ
  intro k hk
  obtain ⟨hk1, hk2⟩ := mem_Icc.1 hk
  interval_cases k <;>
    simp only [pseudocaterpillarClass, e3, e13, e6, e7, e9, e10, e12, e14, e15, e11]

/-- **Table 6**: the inequalities between unrooted gene tree probabilities for the nonbinary
5-taxon representatives (`u₁ > u₂` for `P₂`; `u₃ > u₁` for `P₃`; `u₁ > u₂ > u₇` for `P₄` and
`P₈`; `u₁ > u₂, u₄ > u₅` for `P₅`; `u₁ > u₂, u₄ > u₅ > u₇` for `P₆`; `u₁ > u₂, u₈ > u₄` for `P₇`;
`u₁, u₃ > u₂ > u₇` for `P₉`). -/
theorem table6 (σ : SpeciesTree (Fin 5)) :
    (σ.clusters = polytomy5 2 → u σ 1 > u σ 2) ∧
    (σ.clusters = polytomy5 3 → u σ 3 > u σ 1) ∧
    (σ.clusters = polytomy5 4 → u σ 1 > u σ 2 ∧ u σ 2 > u σ 7) ∧
    (σ.clusters = polytomy5 5 → u σ 1 > u σ 2 ∧ u σ 1 > u σ 4 ∧ u σ 2 > u σ 5 ∧ u σ 4 > u σ 5) ∧
    (σ.clusters = polytomy5 6 → u σ 1 > u σ 2 ∧ u σ 1 > u σ 4 ∧ u σ 2 > u σ 5 ∧ u σ 4 > u σ 5 ∧
      u σ 5 > u σ 7) ∧
    (σ.clusters = polytomy5 7 → u σ 1 > u σ 2 ∧ u σ 1 > u σ 8 ∧ u σ 2 > u σ 4 ∧ u σ 8 > u σ 4) ∧
    (σ.clusters = polytomy5 8 → u σ 1 > u σ 2 ∧ u σ 2 > u σ 7) ∧
    (σ.clusters = polytomy5 9 → u σ 1 > u σ 2 ∧ u σ 3 > u σ 2 ∧ u σ 2 > u σ 7) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_⟩
  · -- `P₂`: `u₁ - u₂ = (1 - Z)/3`
    obtain ⟨hZ, hZ1, e1, e2⟩ := appc_vals2 σ h
    linarith
  · -- `P₃`: `u₃ - u₁ = (1 - Z⁶)/18`
    obtain ⟨hZ, hZ1, e1, e3⟩ := appc_vals3 σ h
    have hZ6 := pow_lt_one₀ hZ.le hZ1 (by norm_num : (6 : ℕ) ≠ 0)
    linarith
  · -- `P₄`: `u₁ - u₂ = (1 - Y)²(2 + Y)/6`, `u₂ - u₇ = Y(1 - Y²)/6`
    obtain ⟨hY, hY1, e1, e2, e7⟩ := appc_vals4 σ h
    generalize exp (-σ.length {0, 1, 2}) = Y at hY hY1 e1 e2 e7
    have k1 : 0 < (1 - Y) ^ 2 * (2 + Y) := mul_pos (pow_pos (by linarith) 2) (by linarith)
    have k2 : 0 < Y * (1 - Y ^ 2) := mul_pos hY (by nlinarith)
    exact ⟨by linarith, by linarith⟩
  · -- `P₅`: `u₁ - u₂ = (1 - Y)(1 - 2X/3)`, `u₁ - u₄ = (1 - X)(1 - 2Y/3)`, `u₂ - u₅ = Y(1 - X)/3`,
    -- `u₄ - u₅ = X(1 - Y)/3`
    obtain ⟨hX, hX1, hY, hY1, e1, e2, e4, e5⟩ := appc_vals5 σ h
    generalize exp (-σ.length {0, 1}) = X at hX hX1 e1 e2 e4 e5
    generalize exp (-σ.length {3, 4}) = Y at hY hY1 e1 e2 e4 e5
    have k1 : 0 < (1 - Y) * (1 - 2 / 3 * X) := mul_pos (by linarith) (by linarith)
    have k2 : 0 < (1 - X) * (1 - 2 / 3 * Y) := mul_pos (by linarith) (by linarith)
    have k3 : 0 < Y * (1 - X) := mul_pos hY (by linarith)
    have k4 : 0 < X * (1 - Y) := mul_pos hX (by linarith)
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · -- `P₆` (the balanced tree with `Z = 1`): `u₁ - u₂ = (k₁ + k₂)/6`, `u₁ - u₄ = k₃`,
    -- `u₂ - u₅ = k₄/3`, `u₄ - u₅ = k₅/6`, `u₅ - u₇ = k₆/6`
    obtain ⟨hX, hX1, hY, hY1, e1, e2, e4, e5, e7⟩ := appc_vals6 σ h
    generalize exp (-σ.length {0, 1}) = X at hX hX1 e1 e2 e4 e5 e7
    generalize exp (-σ.length {0, 1, 2}) = Y at hY hY1 e1 e2 e4 e5 e7
    have hY3 : Y ^ 3 < 1 := pow_lt_one₀ hY.le hY1 (by norm_num)
    have hY2 : 0 < 1 - Y ^ 2 := by nlinarith
    have k1 : 0 < (1 - X) * (4 - 3 * Y - Y ^ 3) := mul_pos (by linarith) (by linarith)
    have k2 : 0 < (1 - Y) ^ 2 * (2 + Y) := mul_pos (pow_pos (by linarith) 2) (by linarith)
    have k3 : 0 < (1 - X) * (1 - 2 / 3 * Y) := mul_pos (by linarith) (by linarith)
    have k4 : 0 < Y * (1 - X) := mul_pos hY (by linarith)
    have k5 : 0 < X * ((1 - Y) ^ 2 * (2 + Y)) := mul_pos hX k2
    have k6 : 0 < X * Y * (1 - Y ^ 2) := mul_pos (mul_pos hX hY) hY2
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · -- `P₇`: `u₁ - u₂ = u₈ - u₄ = X(1 - Z⁶)/18`, `u₁ - u₈ = u₂ - u₄ = (1 - X)/3`
    obtain ⟨hX, hX1, hZ, hZ1, e1, e2, e4, e8⟩ := appc_vals7 σ h
    generalize exp (-σ.length {0, 1}) = X at hX hX1 e1 e2 e4 e8
    generalize exp (-σ.length {0, 1, 3, 4}) = Z at hZ hZ1 e1 e2 e4 e8
    have hZ6 : Z ^ 6 < 1 := pow_lt_one₀ hZ.le hZ1 (by norm_num)
    have k1 : 0 < X * (1 - Z ^ 6) := mul_pos hX (by linarith)
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · -- `P₈`: `u₁ - u₂ = (1 - Z)/3 + Z(1 - Y)²(2 + Y)/6`, `u₂ - u₇ = YZ(1 - Y²)/6`
    obtain ⟨hY, hY1, hZ, hZ1, e1, e2, e7⟩ := appc_vals8 σ h
    generalize exp (-σ.length {0, 1, 2}) = Y at hY hY1 e1 e2 e7
    generalize exp (-σ.length {3, 4}) = Z at hZ hZ1 e1 e2 e7
    have hY2 : 0 < 1 - Y ^ 2 := by nlinarith
    have k1 : 0 < Z * ((1 - Y) ^ 2 * (2 + Y)) :=
      mul_pos hZ (mul_pos (pow_pos (by linarith) 2) (by linarith))
    have k2 : 0 < Y * Z * (1 - Y ^ 2) := mul_pos (mul_pos hY hZ) hY2
    exact ⟨by linarith, by linarith⟩
  · -- `P₉`: `u₁ - u₂ = (1 - Y)²(2 + Y)/6`, `u₃ - u₂ = Y³(1 - Z⁶)/18`, `u₂ - u₇ = Y(1 - Y²)/6`
    obtain ⟨hY, hY1, hZ, hZ1, e1, e2, e3, e7⟩ := appc_vals9 σ h
    generalize exp (-σ.length {0, 1, 2}) = Y at hY hY1 e1 e2 e3 e7
    generalize exp (-σ.length {0, 1, 2, 3}) = Z at hZ hZ1 e1 e2 e3 e7
    have hZ6 : Z ^ 6 < 1 := pow_lt_one₀ hZ.le hZ1 (by norm_num)
    have hY2 : 0 < 1 - Y ^ 2 := by nlinarith
    have k1 : 0 < (1 - Y) ^ 2 * (2 + Y) := mul_pos (pow_pos (by linarith) 2) (by linarith)
    have k2 : 0 < Y ^ 3 * (1 - Z ^ 6) := mul_pos (pow_pos hY 3) (by linarith)
    have k3 : 0 < Y * (1 - Y ^ 2) := mul_pos hY hY2
    exact ⟨by linarith, by linarith, by linarith⟩

/-- **Table 7**, equivalence classes: for each nonbinary representative `P_k`, two gene trees have
the same probability for all branch lengths exactly when they lie in the same class of Table 7. -/
theorem table7_classes (k : ℕ) (hk : k ∈ Icc 1 9) (i j : ℕ) (hi : i ∈ Icc 1 15)
    (hj : j ∈ Icc 1 15) :
    (∀ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 k → u σ i = u σ j) ↔
      polytomyClass k i = polytomyClass k j := by
  constructor
  · intro h
    obtain ⟨σ, hσ, hd⟩ := appc_distinct k hk
    refine hd _ (mem_image_of_mem _ hi) _ (mem_image_of_mem _ hj) ?_
    rw [← appc_cls k hk σ hσ i hi, ← appc_cls k hk σ hσ j hj]
    exact h σ hσ
  · intro h σ hσ
    rw [appc_cls k hk σ hσ i hi, appc_cls k hk σ hσ j hj, h]

open scoped Classical in
/-- Appendix C (proof of Proposition 11): for every rooted 5-taxon species tree shape the least
probable class `𝒞` of gene trees has probability strictly smaller than all others, and
`|𝒞| = 15` for `P₁`, `12` for `P₂` and `P₃`, `10` for `P₅` and `P₇`, `8` for the resolved
pseudocaterpillar, and `6` for the resolved caterpillar and balanced trees and for `P₄`, `P₆`,
`P₈`, `P₉`. When `|𝒞| = 6`, the class with the second smallest probability has cardinality `2`
only for the caterpillar, `3` only for `P₉`, `6` only for `P₄` and `P₈`, and `4` for the balanced
tree and `P₆`. -/
theorem appendixC_leastClass (σ : SpeciesTree (Fin 5)) :
    let C := {i ∈ Icc 1 15 | ∀ j ∈ Icc 1 15, u σ i ≤ u σ j}
    let C₂ := {i ∈ Icc 1 15 | i ∉ C ∧ ∀ j ∈ Icc 1 15, j ∉ C → u σ i ≤ u σ j}
    (σ.clusters = polytomy5 1 → #C = 15) ∧
    (σ.clusters = polytomy5 2 → #C = 12) ∧ (σ.clusters = polytomy5 3 → #C = 12) ∧
    (σ.clusters = polytomy5 5 → #C = 10) ∧ (σ.clusters = polytomy5 7 → #C = 10) ∧
    (σ.clusters = pseudocaterpillar5 → #C = 8) ∧
    (σ.clusters = caterpillar5 → #C = 6 ∧ #C₂ = 2) ∧
    (σ.clusters = balanced5 → #C = 6 ∧ #C₂ = 4) ∧
    (σ.clusters = polytomy5 4 → #C = 6 ∧ #C₂ = 6) ∧
    (σ.clusters = polytomy5 6 → #C = 6 ∧ #C₂ = 4) ∧
    (σ.clusters = polytomy5 8 → #C = 6 ∧ #C₂ = 6) ∧
    (σ.clusters = polytomy5 9 → #C = 6 ∧ #C₂ = 3) := by
  intro C C₂
  have hCm : ∀ i, i ∈ C ↔ i ∈ Icc 1 15 ∧ ∀ j ∈ Icc 1 15, u σ i ≤ u σ j := fun _ => by
    simp only [C, mem_filter]
  have hC₂m : ∀ i, i ∈ C₂ ↔ i ∈ Icc 1 15 ∧ i ∉ C ∧ ∀ j ∈ Icc 1 15, j ∉ C → u σ i ≤ u σ j :=
    fun _ => by simp only [C₂, mem_filter]
  obtain ⟨t2, t3, t4, t5, t6, t7, t8, t9⟩ := table6 σ
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · -- `P₁`: one class
    rw [appc_C_eq (u σ) (polytomyClass 1) 1 ∅ (appc_cls 1 (by decide) σ h) (by decide)
      (by decide) (by simp) C hCm]
    decide
  · -- `P₂`: `u₂ < u₁`
    have := t2 h
    rw [appc_C_eq (u σ) (polytomyClass 2) 2 {1} (appc_cls 2 (by decide) σ h) (by decide)
      (by decide) (fun r hr => by rw [mem_singleton.1 hr]; linarith) C hCm]
    decide
  · -- `P₃`: `u₁ < u₃`
    have := t3 h
    rw [appc_C_eq (u σ) (polytomyClass 3) 1 {3} (appc_cls 3 (by decide) σ h) (by decide)
      (by decide) (fun r hr => by rw [mem_singleton.1 hr]; linarith) C hCm]
    decide
  · -- `P₅`: `u₅ < u₂, u₄ < u₁`
    obtain ⟨h12, h14, h25, h45⟩ := t5 h
    rw [appc_C_eq (u σ) (polytomyClass 5) 5 {1, 2, 4} (appc_cls 5 (by decide) σ h) (by decide)
      (by decide) (fun r hr => by fin_cases hr <;> linarith) C hCm]
    decide
  · -- `P₇`: `u₄ < u₂, u₈ < u₁`
    obtain ⟨h12, h18, h24, h84⟩ := t7 h
    rw [appc_C_eq (u σ) (polytomyClass 7) 4 {1, 2, 8} (appc_cls 7 (by decide) σ h) (by decide)
      (by decide) (fun r hr => by fin_cases hr <;> linarith) C hCm]
    decide
  · -- pseudocaterpillar: inequalities (6)
    obtain ⟨h12, h14, h18, h25, h45, h85⟩ := equation6 σ h
    rw [appc_C_eq (u σ) pseudocaterpillarClass 5 {1, 2, 4, 8} (appc_pse_cls σ h) (by decide)
      (by decide) (fun r hr => by fin_cases hr <;> linarith) C hCm]
    decide
  · -- caterpillar: inequalities (5)
    obtain ⟨h12, h14, h25, h45, h57, h32, h36, h65⟩ := equation5 σ h
    have hc := appc_C_eq (u σ) caterpillarClass 7 {1, 2, 3, 4, 5, 6} (appc_cat_cls σ h)
      (by decide) (by decide) (fun r hr => by fin_cases hr <;> linarith) C hCm
    rw [appc_C2_eq (u σ) caterpillarClass 7 5 {1, 2, 3, 4, 6} (appc_cat_cls σ h) (by decide)
      (by decide) (by decide) (by decide) (fun r hr => by fin_cases hr <;> linarith) C C₂ hc
      hC₂m, hc]
    decide
  · -- balanced: inequalities (4)
    obtain ⟨h12, h14, h25, h45, h57⟩ := equation4 σ h
    have hc := appc_C_eq (u σ) balancedClass 7 {1, 2, 4, 5} (appc_bal_cls σ h)
      (by decide) (by decide) (fun r hr => by fin_cases hr <;> linarith) C hCm
    rw [appc_C2_eq (u σ) balancedClass 7 5 {1, 2, 4} (appc_bal_cls σ h) (by decide)
      (by decide) (by decide) (by decide) (fun r hr => by fin_cases hr <;> linarith) C C₂ hc
      hC₂m, hc]
    decide
  · -- `P₄`: `u₇ < u₂ < u₁`
    obtain ⟨h12, h27⟩ := t4 h
    have hc := appc_C_eq (u σ) (polytomyClass 4) 7 {1, 2} (appc_cls 4 (by decide) σ h)
      (by decide) (by decide) (fun r hr => by fin_cases hr <;> linarith) C hCm
    rw [appc_C2_eq (u σ) (polytomyClass 4) 7 2 {1} (appc_cls 4 (by decide) σ h) (by decide)
      (by decide) (by decide) (by decide) (fun r hr => by rw [mem_singleton.1 hr]; linarith) C C₂
      hc hC₂m, hc]
    decide
  · -- `P₆`: `u₇ < u₅ < u₂, u₄ < u₁`
    obtain ⟨h12, h14, h25, h45, h57⟩ := t6 h
    have hc := appc_C_eq (u σ) (polytomyClass 6) 7 {1, 2, 4, 5} (appc_cls 6 (by decide) σ h)
      (by decide) (by decide) (fun r hr => by fin_cases hr <;> linarith) C hCm
    rw [appc_C2_eq (u σ) (polytomyClass 6) 7 5 {1, 2, 4} (appc_cls 6 (by decide) σ h)
      (by decide) (by decide) (by decide) (by decide) (fun r hr => by fin_cases hr <;> linarith)
      C C₂ hc hC₂m, hc]
    decide
  · -- `P₈`: `u₇ < u₂ < u₁`
    obtain ⟨h12, h27⟩ := t8 h
    have hc := appc_C_eq (u σ) (polytomyClass 8) 7 {1, 2} (appc_cls 8 (by decide) σ h)
      (by decide) (by decide) (fun r hr => by fin_cases hr <;> linarith) C hCm
    rw [appc_C2_eq (u σ) (polytomyClass 8) 7 2 {1} (appc_cls 8 (by decide) σ h) (by decide)
      (by decide) (by decide) (by decide) (fun r hr => by rw [mem_singleton.1 hr]; linarith) C C₂
      hc hC₂m, hc]
    decide
  · -- `P₉`: `u₇ < u₂ < u₁, u₃`
    obtain ⟨h12, h32, h27⟩ := t9 h
    have hc := appc_C_eq (u σ) (polytomyClass 9) 7 {1, 2, 3} (appc_cls 9 (by decide) σ h)
      (by decide) (by decide) (fun r hr => by fin_cases hr <;> linarith) C hCm
    rw [appc_C2_eq (u σ) (polytomyClass 9) 7 2 {1, 3} (appc_cls 9 (by decide) σ h) (by decide)
      (by decide) (by decide) (by decide) (fun r hr => by fin_cases hr <;> linarith) C C₂ hc
      hC₂m, hc]
    decide

/-- Appendix C: for `P₅` and `P₇` the two classes of size 2 can degenerate to a single class of
size 4. -/
theorem appendixC_degenerate :
    (∃ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 5 ∧ u σ 2 = u σ 4) ∧
      ∃ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 7 ∧ u σ 2 = u σ 8 := by
  constructor
  · -- `P₅` with `X = Y`
    obtain ⟨σ, hσ, hx, hy⟩ := appc_exists (polytomy5 5) (by decide) (by decide) (by decide)
      (by decide) {0, 1} {3, 4} (by decide) (by decide) (by decide) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, -, -, -, -, e2, e4, -⟩ := appc_vals5 σ hσ
    refine ⟨σ, hσ, ?_⟩
    rw [e2, e4, hx, hy]
  · -- `P₇`: `u₂ - u₈ = 1/3 - 7X/18 + XZ⁶/18` vanishes at `Z = 1/2`, `X = 128/149`
    obtain ⟨σ, hσ, hx, hz⟩ := appc_exists (polytomy5 7) (by decide) (by decide) (by decide)
      (by decide) {0, 1} {0, 1, 3, 4} (by decide) (by decide) (by decide) (128 / 149) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, -, -, -, -, e2, -, e8⟩ := appc_vals7 σ hσ
    refine ⟨σ, hσ, ?_⟩
    rw [e2, e8, hx, hz]
    norm_num

end ADR11
