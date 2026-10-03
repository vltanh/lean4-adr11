module

public import ADR11.FiveTaxa.Basic

/-!
# The rooted caterpillar 5-taxon species tree `((((a,b):x,c):y,d):z,e)`

Appendix B.2 (equation (12)), Table 2, the marginalization invariant, the equivalence classes,
the inequalities (5) and their exhaustiveness (Section 4.2.2). Throughout, `X = e^{-x}`,
`Y = e^{-y}`, `Z = e^{-z}` with `x, y, z` the lengths of the edges above `{a,b}`, `{a,b,c}` and
`{a,b,c,d}`.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-- **Equation (12)** (Appendix B.2): the unrooted gene tree distribution of the rooted caterpillar
species tree `((((a,b):x,c):y,d):z,e)`. -/
theorem equation12 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    let X := exp (-σ.length {0, 1})
    let Y := exp (-σ.length {0, 1, 2})
    let Z := exp (-σ.length {0, 1, 2, 3})
    u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y + 1 / 3 * X * Y + 1 / 18 * X * Y ^ 3 +
        1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
    u σ 2 = 1 / 3 * Y - 1 / 6 * X * Y - 1 / 9 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
    u σ 3 = 1 / 3 * Y - 1 / 6 * X * Y - 1 / 18 * X * Y ^ 3 - 2 / 45 * X * Y ^ 3 * Z ^ 6 ∧
    u σ 4 = 1 / 3 * X - 1 / 3 * X * Y + 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 13 = u σ 4 ∧
    u σ 5 = 1 / 6 * X * Y - 1 / 9 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧ u σ 12 = u σ 5 ∧
    u σ 6 = 1 / 6 * X * Y - 1 / 18 * X * Y ^ 3 - 2 / 45 * X * Y ^ 3 * Z ^ 6 ∧ u σ 9 = u σ 6 ∧
    u σ 7 = 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧ u σ 8 = u σ 7 ∧
      u σ 10 = u σ 7 ∧ u σ 11 = u σ 7 ∧ u σ 14 = u σ 7 ∧ u σ 15 = u σ 7 := by
  sorry

/-- The basis of homogeneous linear invariants listed in Table 2, in the order of the table. -/
def table2Basis : Fin 9 → Fin 15 → ℝ :=
  ![ue 14 - ue 15, ue 11 - ue 15, ue 10 - ue 15, ue 8 - ue 15, ue 7 - ue 15, ue 6 - ue 9,
    ue 5 - ue 12, ue 4 - ue 13, ue 2 - ue 3 + ue 9 - ue 12]

/-! ### Helpers: the formulas (12) on the classes, and caterpillars with given `X, Y, Z` -/

/-- For a caterpillar species tree, `X, Y, Z ∈ (0, 1)`. -/
theorem tables_cat_bounds (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    0 < exp (-σ.length {0, 1}) ∧ exp (-σ.length {0, 1}) < 1 ∧
    0 < exp (-σ.length {0, 1, 2}) ∧ exp (-σ.length {0, 1, 2}) < 1 ∧
    0 < exp (-σ.length {0, 1, 2, 3}) ∧ exp (-σ.length {0, 1, 2, 3}) < 1 := by
  have h : ∀ A ∈ caterpillar5, A ≠ univ → exp (-σ.length A) < 1 := fun A hA hne =>
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (σ.length_pos A (hσ ▸ hA) hne))
  exact ⟨exp_pos _, h _ (by decide) (by decide), exp_pos _, h _ (by decide) (by decide),
    exp_pos _, h _ (by decide) (by decide)⟩

/-- Equation (12) on the names of the classes, with `X, Y, Z ∈ (0, 1)`. -/
private theorem tables_cat_formulas (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    ∃ X Y Z : ℝ, 0 < X ∧ X < 1 ∧ 0 < Y ∧ Y < 1 ∧ 0 < Z ∧ Z < 1 ∧
      u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y + 1 / 3 * X * Y + 1 / 18 * X * Y ^ 3 +
        1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 2 = 1 / 3 * Y - 1 / 6 * X * Y - 1 / 9 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 3 = 1 / 3 * Y - 1 / 6 * X * Y - 1 / 18 * X * Y ^ 3 - 2 / 45 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 4 = 1 / 3 * X - 1 / 3 * X * Y + 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 5 = 1 / 6 * X * Y - 1 / 9 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 6 = 1 / 6 * X * Y - 1 / 18 * X * Y ^ 3 - 2 / 45 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 7 = 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 := by
  obtain ⟨h1, h2, h3, h4, -, h5, -, h6, -, h7, -⟩ := equation12 σ hσ
  obtain ⟨a, b, c, d, e, f⟩ := tables_cat_bounds σ hσ
  exact ⟨_, _, _, a, b, c, d, e, f, h1, h2, h3, h4, h5, h6, h7⟩

/-- A caterpillar species tree with prescribed `X, Y, Z ∈ (0, 1)`, and its probabilities. -/
private theorem tables_cat_at (X Y Z : ℝ) (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1)
    (hZ : 0 < Z) (hZ1 : Z < 1) :
    ∃ σ : SpeciesTree (Fin 5), σ.clusters = caterpillar5 ∧
      u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y + 1 / 3 * X * Y + 1 / 18 * X * Y ^ 3 +
        1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 2 = 1 / 3 * Y - 1 / 6 * X * Y - 1 / 9 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 3 = 1 / 3 * Y - 1 / 6 * X * Y - 1 / 18 * X * Y ^ 3 - 2 / 45 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 4 = 1 / 3 * X - 1 / 3 * X * Y + 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 5 = 1 / 6 * X * Y - 1 / 9 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 6 = 1 / 6 * X * Y - 1 / 18 * X * Y ^ 3 - 2 / 45 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 7 = 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 := by
  have e1 : ({0, 1, 2} : Finset (Fin 5)) ≠ {0, 1} := by decide
  have e2 : ({0, 1, 2, 3} : Finset (Fin 5)) ≠ {0, 1} := by decide
  have e3 : ({0, 1, 2, 3} : Finset (Fin 5)) ≠ {0, 1, 2} := by decide
  let σ : SpeciesTree (Fin 5) := SpeciesTree.ofLengths caterpillar5
    (fun A => if A = {0, 1} then -log X else if A = {0, 1, 2} then -log Y else -log Z)
    (by decide) (by decide) (by decide) (by decide) (fun A _ _ _ => by
      split_ifs
      exacts [neg_pos.2 (log_neg hX hX1), neg_pos.2 (log_neg hY hY1),
        neg_pos.2 (log_neg hZ hZ1)])
  have hx : exp (-σ.length {0, 1}) = X := by simp [σ, SpeciesTree.ofLengths, exp_log hX]
  have hy : exp (-σ.length {0, 1, 2}) = Y := by
    simp [σ, SpeciesTree.ofLengths, e1, exp_log hY]
  have hz : exp (-σ.length {0, 1, 2, 3}) = Z := by
    simp [σ, SpeciesTree.ofLengths, e2, e3, exp_log hZ]
  obtain ⟨h1, h2, h3, h4, -, h5, -, h6, -, h7, -⟩ := equation12 σ rfl
  simp only [hx, hy, hz] at h1 h2 h3 h4 h5 h6 h7
  exact ⟨σ, rfl, h1, h2, h3, h4, h5, h6, h7⟩

/-- The expansion of `∑ cᵢ uᵢ`. -/
private theorem tables_sum15 (c : Fin 15 → ℝ) (σ : SpeciesTree (Fin 5)) :
    ∑ i, c i * uVec σ i = c 0 * u σ 1 + c 1 * u σ 2 + c 2 * u σ 3 + c 3 * u σ 4 + c 4 * u σ 5 +
      c 5 * u σ 6 + c 6 * u σ 7 + c 7 * u σ 8 + c 8 * u σ 9 + c 9 * u σ 10 + c 10 * u σ 11 +
      c 11 * u σ 12 + c 12 * u σ 13 + c 13 * u σ 14 + c 14 * u σ 15 := by
  simp [Fin.sum_univ_succ, uVec]
  ring

private theorem tables_mem_linearInvariants {H : Finset (Finset (Fin 5))} {c : Fin 15 → ℝ} :
    c ∈ linearInvariants H ↔
      ∀ σ : SpeciesTree (Fin 5), σ.clusters = H → ∑ i, c i * uVec σ i = 0 :=
  Iff.rfl

/-- The vectors of Table 2 are linearly independent: each has a coordinate where all the others
vanish. -/
private theorem tables_cat_li : LinearIndependent ℝ table2Basis := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h : ∀ k, (∑ i, g i • table2Basis i) k = 0 := fun k => congrFun hg k
  have h13 := h 13
  have h10 := h 10
  have h9 := h 9
  have h7 := h 7
  have h6 := h 6
  have h5 := h 5
  have h4 := h 4
  have h3 := h 3
  have h1 := h 1
  simp [Fin.sum_univ_succ, table2Basis, ue] at h13 h10 h9 h7 h6 h5 h4 h3 h1
  intro i
  fin_cases i <;> assumption

/-- The vectors of Table 2 are invariants, by (12). -/
private theorem tables_cat_mem (k : Fin 9) : table2Basis k ∈ linearInvariants caterpillar5 := by
  rw [tables_mem_linearInvariants]
  intro σ hσ
  obtain ⟨-, -, -, -, e13, -, e12, -, e9, -, e8, e10, e11, e14, e15⟩ := equation12 σ hσ
  obtain ⟨X, Y, Z, -, -, -, -, -, -, -, h2, h3, -, h5, h6, -⟩ := tables_cat_formulas σ hσ
  rw [tables_sum15]
  fin_cases k <;> simp [table2Basis, ue] <;> linarith

/-- An invariant vanishes on the six trees with `(X, Y, Z)` equal to `(1/4, 1/4, 1/2)`,
`(1/2, 1/4, 1/2)`, `(1/2, 1/2, 1/2)`, `(1/4, 1/2, 1/2)`, `(1/2, 1/2, 1/4)` and `(1/2, 3/4, 1/2)`,
on which the values of `(u₁, …, u₇)` span the relations proportional to
`u₂ - u₃ - u₅ + u₆ = 0`: this gives six linear conditions on the coordinates. -/
private theorem tables_cat_sums {c : Fin 15 → ℝ} (hc : c ∈ linearInvariants caterpillar5) :
    c 0 = 0 ∧ c 1 + c 2 = 0 ∧ c 3 + c 12 = 0 ∧ c 1 + c 4 + c 11 = 0 ∧ c 5 + c 8 - c 1 = 0 ∧
      c 6 + c 7 + c 9 + c 10 + c 13 + c 14 = 0 := by
  rw [tables_mem_linearInvariants] at hc
  have E : ∀ σ : SpeciesTree (Fin 5), σ.clusters = caterpillar5 →
      c 0 * u σ 1 + c 1 * u σ 2 + c 2 * u σ 3 + (c 3 + c 12) * u σ 4 + (c 4 + c 11) * u σ 5 +
        (c 5 + c 8) * u σ 6 + (c 6 + c 7 + c 9 + c 10 + c 13 + c 14) * u σ 7 = 0 := by
    intro σ hσ
    obtain ⟨-, -, -, -, e13, -, e12, -, e9, -, e8, e10, e11, e14, e15⟩ := equation12 σ hσ
    have := hc σ hσ
    rw [tables_sum15, e13, e12, e9, e8, e10, e11, e14, e15] at this
    linear_combination this
  obtain ⟨σ₁, hσ₁, a1, a2, a3, a4, a5, a6, a7⟩ := tables_cat_at (1 / 4) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₂, hσ₂, b1, b2, b3, b4, b5, b6, b7⟩ := tables_cat_at (1 / 2) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₃, hσ₃, d1, d2, d3, d4, d5, d6, d7⟩ := tables_cat_at (1 / 2) (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₄, hσ₄, f1, f2, f3, f4, f5, f6, f7⟩ := tables_cat_at (1 / 4) (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₅, hσ₅, g1, g2, g3, g4, g5, g6, g7⟩ := tables_cat_at (1 / 2) (1 / 2) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₆, hσ₆, k1, k2, k3, k4, k5, k6, k7⟩ := tables_cat_at (1 / 2) (3 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have E₁ := E σ₁ hσ₁
  have E₂ := E σ₂ hσ₂
  have E₃ := E σ₃ hσ₃
  have E₄ := E σ₄ hσ₄
  have E₅ := E σ₅ hσ₅
  have E₆ := E σ₆ hσ₆
  rw [a1, a2, a3, a4, a5, a6, a7] at E₁
  rw [b1, b2, b3, b4, b5, b6, b7] at E₂
  rw [d1, d2, d3, d4, d5, d6, d7] at E₃
  rw [f1, f2, f3, f4, f5, f6, f7] at E₄
  rw [g1, g2, g3, g4, g5, g6, g7] at E₅
  rw [k1, k2, k3, k4, k5, k6, k7] at E₆
  norm_num at E₁ E₂ E₃ E₄ E₅ E₆
  clear E hc a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 d1 d2 d3 d4 d5 d6 d7 f1 f2 f3 f4 f5 f6 f7
    g1 g2 g3 g4 g5 g6 g7 k1 k2 k3 k4 k5 k6 k7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- An invariant is the combination of the vectors of Table 2 with the coefficients of its
coordinates `u₁₄, u₁₁, u₁₀, u₈, u₇, u₆, u₅, u₄, u₂`. -/
private theorem tables_cat_repr {c : Fin 15 → ℝ}
    (h : c 0 = 0 ∧ c 1 + c 2 = 0 ∧ c 3 + c 12 = 0 ∧ c 1 + c 4 + c 11 = 0 ∧ c 5 + c 8 - c 1 = 0 ∧
      c 6 + c 7 + c 9 + c 10 + c 13 + c 14 = 0) :
    ∑ i, ![c 13, c 10, c 9, c 7, c 6, c 5, c 4, c 3, c 1] i • table2Basis i = c := by
  obtain ⟨s1, s2, s4, s5, s6, s7⟩ := h
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases k <;> simp [table2Basis, ue] <;> linarith

/-- **Table 2.** The invariants listed form a basis of the homogeneous linear invariants of the
unrooted gene tree distributions of the species tree `((((a,b),c),d),e)`. -/
theorem table2 :
    LinearIndependent ℝ table2Basis ∧
      Submodule.span ℝ (Set.range table2Basis) = linearInvariants caterpillar5 := by
  refine ⟨tables_cat_li, le_antisymm ?_ fun c hc => ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact tables_cat_mem k
  · rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨_, tables_cat_repr (tables_cat_sums hc)⟩

/-- The marginalization argument of Section 4.2.2: on the taxa `{b,c,d,e}` the two quartets that
disagree with the species tree are equiprobable, which gives
`u₂ + u₆ + u₇ + u₁₁ + u₁₄ = u₃ + u₅ + u₈ + u₁₀ + u₁₅`, and then the last invariant of Table 2. -/
theorem caterpillar_marginalization (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    u σ 2 + u σ 6 + u σ 7 + u σ 11 + u σ 14 = u σ 3 + u σ 5 + u σ 8 + u σ 10 + u σ 15 ∧
      u σ 2 - u σ 3 + u σ 9 - u σ 12 = 0 := by
  obtain ⟨-, -, -, -, -, -, e12, -, e9, -, e8, e10, e11, e14, e15⟩ := equation12 σ hσ
  obtain ⟨X, Y, Z, -, -, -, -, -, -, -, h2, h3, -, h5, h6, -⟩ := tables_cat_formulas σ hσ
  rw [e12, e9, e8, e10, e11, e14, e15, h2, h3, h5, h6]
  constructor <;> ring

/-- The class of `T_i` in the partition of Section 4.2.2, named by its smallest index:
`{T₁}, {T₂}, {T₃}, {T₄,T₁₃}, {T₅,T₁₂}, {T₆,T₉}, {T₇,T₈,T₁₀,T₁₁,T₁₄,T₁₅}`. -/
def caterpillarClass : ℕ → ℕ
  | 13 => 4 | 12 => 5 | 9 => 6
  | 8 => 7 | 10 => 7 | 11 => 7 | 14 => 7 | 15 => 7 | i => i

/-- Each `u_k` equals `u` of the name of the class of `T_k`. -/
private theorem tables_cat_cls (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    ∀ k ∈ Icc 1 15, u σ k = u σ (caterpillarClass k) := by
  obtain ⟨-, -, -, -, e13, -, e12, -, e9, -, e8, e10, e11, e14, e15⟩ := equation12 σ hσ
  intro k hk
  obtain ⟨hk1, hk2⟩ := mem_Icc.1 hk
  interval_cases k <;> simp only [caterpillarClass, e13, e12, e9, e8, e10, e11, e14, e15]

/-- The names of the classes. -/
private theorem tables_cat_rep :
    ∀ k ∈ Icc 1 15, caterpillarClass k ∈ ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ) := by
  decide

/-- A caterpillar species tree on which the seven classes have distinct probabilities. -/
private theorem tables_cat_distinct : ∃ σ : SpeciesTree (Fin 5), σ.clusters = caterpillar5 ∧
    ∀ a ∈ ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ), ∀ b ∈ ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ),
      u σ a = u σ b → a = b := by
  obtain ⟨σ, hσ, a1, a2, a3, a4, a5, a6, a7⟩ := tables_cat_at (1 / 4) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at a1 a2 a3 a4 a5 a6 a7
  refine ⟨σ, hσ, ?_⟩
  intro a ha b hb e
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; linarith)

/-- The equivalence classes of unrooted gene trees according to their probabilities. -/
theorem caterpillar_classes (i j : ℕ) (hi : i ∈ Icc 1 15) (hj : j ∈ Icc 1 15) :
    (∀ σ : SpeciesTree (Fin 5), σ.clusters = caterpillar5 → u σ i = u σ j) ↔
      caterpillarClass i = caterpillarClass j := by
  constructor
  · intro h
    obtain ⟨σ, hσ, hd⟩ := tables_cat_distinct
    refine hd _ (tables_cat_rep i hi) _ (tables_cat_rep j hj) ?_
    rw [← tables_cat_cls σ hσ i hi, ← tables_cat_cls σ hσ j hj]
    exact h σ hσ
  · intro h σ hσ
    rw [tables_cat_cls σ hσ i hi, tables_cat_cls σ hσ j hj, h]

/-- **Inequalities (5)**: for all branch lengths, `u₁ > u₂ > u₅`, `u₁ > u₄ > u₅`, `u₃ > u₂`,
`u₃ > u₆ > u₅` and `u₅ > u₇`. -/
theorem equation5 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    u σ 1 > u σ 2 ∧ u σ 1 > u σ 4 ∧ u σ 2 > u σ 5 ∧ u σ 4 > u σ 5 ∧ u σ 5 > u σ 7 ∧
      u σ 3 > u σ 2 ∧ u σ 3 > u σ 6 ∧ u σ 6 > u σ 5 := by
  obtain ⟨X, Y, Z, hX, hX1, hY, hY1, hZ, hZ1, h1, h2, h3, h4, h5, h6, h7⟩ :=
    tables_cat_formulas σ hσ
  rw [h1, h2, h3, h4, h5, h6, h7]
  have hX' : 0 < 1 - X := by linarith
  have hY' : 0 < 1 - Y := by linarith
  have hY3 : Y ^ 3 < 1 := pow_lt_one₀ hY.le hY1 (by norm_num)
  have hZ6 : Z ^ 6 < 1 := pow_lt_one₀ hZ.le hZ1 (by norm_num)
  have hY2 : 0 < 1 - Y ^ 2 := by nlinarith
  -- `u₁ - u₂ = k₁/6 + k₂/6`
  have k1 : 0 < (1 - X) * (4 - 3 * Y - Y ^ 3) := mul_pos hX' (by linarith)
  have k2 : 0 < (1 - Y) ^ 2 * (2 + Y) := by positivity
  -- `u₁ - u₄ = k₃`
  have k3 : 0 < (1 - X) * (1 - 2 / 3 * Y) := mul_pos hX' (by linarith)
  -- `u₂ - u₅ = u₃ - u₆ = k₄/3`
  have k4 : 0 < Y * (1 - X) := by positivity
  -- `u₄ - u₅ = k₅/6`
  have k5 : 0 < X * ((1 - Y) ^ 2 * (2 + Y)) := by positivity
  -- `u₅ - u₇ = k₆/6`
  have k6 : 0 < X * Y * (1 - Y ^ 2) := by positivity
  -- `u₃ - u₂ = u₆ - u₅ = k₇/18`
  have k7 : 0 < X * Y ^ 3 * (1 - Z ^ 6) := mul_pos (by positivity) (by linarith)
  exact ⟨by linarith only [k1, k2], by linarith only [k3], by linarith only [k4],
    by linarith only [k5], by linarith only [k6], by linarith only [k7], by linarith only [k4],
    by linarith only [k7]⟩

/-- The strict order between classes generated by the inequalities (5). -/
def caterpillarOrder : Finset (ℕ × ℕ) :=
  {(1, 2), (1, 4), (1, 5), (1, 7), (3, 2), (3, 6), (3, 5), (3, 7), (2, 5), (2, 7), (4, 5), (4, 7),
    (6, 5), (6, 7), (5, 7)}

/-- Between the names of the classes, the inequalities holding for all branch lengths are those of
`caterpillarOrder`: the other ones fail on one of the trees with `(X, Y, Z)` equal to
`(1/4, 1/4, 1/2)`, `(1/2, 1/4, 1/2)` or `(19/20, 19/20, 1/2)`. -/
private theorem tables_cat_order : ∀ a ∈ ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ),
    ∀ b ∈ ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ),
      ((∀ σ : SpeciesTree (Fin 5), σ.clusters = caterpillar5 → u σ a > u σ b) ↔
        (a, b) ∈ caterpillarOrder) := by
  obtain ⟨σ₁, hσ₁, a1, a2, a3, a4, a5, a6, a7⟩ := tables_cat_at (1 / 4) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₂, hσ₂, b1, b2, b3, b4, b5, b6, b7⟩ := tables_cat_at (1 / 2) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₃, hσ₃, d1, d2, d3, d4, d5, d6, d7⟩ := tables_cat_at (19 / 20) (19 / 20) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 d1 d2 d3 d4 d5 d6 d7
  intro a ha b hb
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;>
    first
      | (intro _; decide)
      | (intro hm; exact absurd hm (by decide))
      | (intro h; have h₁ := h σ₁ hσ₁; have h₂ := h σ₂ hσ₂; have h₃ := h σ₃ hσ₃; exfalso;
          linarith)
      | (intro _ σ hσ; obtain ⟨_, _, _, _, _, _, _, _⟩ := equation5 σ hσ; linarith)

/-- Section 4.2.2: there are no inequalities `u_i > u_j` holding for all branch lengths other than
those implied by (5) and the equalities of Table 2. -/
theorem equation5_exhaustive (i j : ℕ) (hi : i ∈ Icc 1 15) (hj : j ∈ Icc 1 15) :
    (∀ σ : SpeciesTree (Fin 5), σ.clusters = caterpillar5 → u σ i > u σ j) ↔
      (caterpillarClass i, caterpillarClass j) ∈ caterpillarOrder := by
  rw [← tables_cat_order _ (tables_cat_rep i hi) _ (tables_cat_rep j hj)]
  refine forall_congr' fun σ => imp_congr_right fun hσ => ?_
  rw [← tables_cat_cls σ hσ i hi, ← tables_cat_cls σ hσ j hj]

open scoped Classical in
/-- From the inequalities (5): the 6-element class always has the strictly smallest probability
and the class `{T₅, T₁₂}` the next smallest (used in the proof of Proposition 7). -/
theorem caterpillar_extremeClasses (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    {i ∈ Icc 1 15 | ∀ j ∈ Icc 1 15, u σ i ≤ u σ j} = {7, 8, 10, 11, 14, 15} ∧
    {i ∈ Icc 1 15 | u σ 7 < u σ i ∧ ∀ j ∈ Icc 1 15, u σ 7 < u σ j → u σ i ≤ u σ j} =
      {5, 12} := by
  obtain ⟨h12, h14, h25, h45, h57, h32, h36, h65⟩ := equation5 σ hσ
  obtain ⟨-, -, -, -, e13, -, e12, -, e9, -, e8, e10, e11, e14, e15⟩ := equation12 σ hσ
  have K1 : ∀ j ∈ Icc 1 15, u σ 7 ≤ u σ j := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_Icc.1 hj
    interval_cases j <;> linarith
  have K2 : ∀ j ∈ Icc 1 15, u σ 7 < u σ j → u σ 5 ≤ u σ j := by
    intro j hj hj7
    obtain ⟨hj1, hj2⟩ := mem_Icc.1 hj
    interval_cases j <;> linarith
  refine ⟨?_, ?_⟩
  · ext i
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hi, h⟩
      have h7 := h 7 (by simp)
      obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
      interval_cases i <;> first | (exfalso; linarith) | simp
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;>
        exact ⟨by simp, fun j hj => by linarith [K1 j hj]⟩
  · ext i
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hi, hlt, h⟩
      have h5 := h 5 (by simp) h57
      obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
      interval_cases i <;> first | (exfalso; linarith) | simp
    · rintro (rfl | rfl) <;>
        exact ⟨by simp, by linarith, fun j hj hj7 => by linarith [K2 j hj hj7]⟩

end ADR11
