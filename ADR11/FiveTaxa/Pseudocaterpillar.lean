module

public import ADR11.FiveTaxa.Basic

/-!
# The pseudocaterpillar 5-taxon species tree `(((a,b):x,(d,e):y):z,c)`

Appendix B.3 (equation (13)), Table 3, the equivalence classes, the inequalities (6) and their
exhaustiveness (Section 4.2.3). Throughout, `X = e^{-x}`, `Y = e^{-y}`, `Z = e^{-z}` with
`x, y, z` the lengths of the edges above `{a,b}`, `{d,e}` and `{a,b,d,e}`.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-- **Equation (13)** (Appendix B.3): the unrooted gene tree distribution of the pseudocaterpillar
species tree `(((a,b):x,(d,e):y):z,c)`. -/
theorem equation13 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) :
    let X := exp (-σ.length {0, 1})
    let Y := exp (-σ.length {3, 4})
    let Z := exp (-σ.length {0, 1, 3, 4})
    u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y + 4 / 9 * X * Y - 2 / 45 * X * Y * Z ^ 6 ∧
    u σ 2 = 1 / 3 * Y - 5 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧ u σ 3 = u σ 2 ∧
    u σ 4 = 1 / 3 * X - 5 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧ u σ 13 = u σ 4 ∧
    u σ 5 = 1 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧ u σ 6 = u σ 5 ∧ u σ 7 = u σ 5 ∧
      u σ 9 = u σ 5 ∧ u σ 10 = u σ 5 ∧ u σ 12 = u σ 5 ∧ u σ 14 = u σ 5 ∧ u σ 15 = u σ 5 ∧
    u σ 8 = 1 / 9 * X * Y - 2 / 45 * X * Y * Z ^ 6 ∧ u σ 11 = u σ 8 := by
  sorry

/-- The basis of homogeneous linear invariants listed in Table 3, in the order of the table. -/
def table3Basis : Fin 10 → Fin 15 → ℝ :=
  ![ue 14 - ue 15, ue 12 - ue 15, ue 10 - ue 15, ue 9 - ue 15, ue 8 - ue 11, ue 7 - ue 15,
    ue 6 - ue 15, ue 5 - ue 15, ue 4 - ue 13, ue 2 - ue 3]

/-! ### Helpers: the formulas (13) on the classes, and pseudocaterpillars with given `X, Y, Z` -/

/-- For a pseudocaterpillar species tree, `X, Y, Z ∈ (0, 1)`. -/
theorem tables_pse_bounds (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) :
    0 < exp (-σ.length {0, 1}) ∧ exp (-σ.length {0, 1}) < 1 ∧
    0 < exp (-σ.length {3, 4}) ∧ exp (-σ.length {3, 4}) < 1 ∧
    0 < exp (-σ.length {0, 1, 3, 4}) ∧ exp (-σ.length {0, 1, 3, 4}) < 1 := by
  have h : ∀ A ∈ pseudocaterpillar5, A ≠ univ → exp (-σ.length A) < 1 := fun A hA hne =>
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (σ.length_pos A (hσ ▸ hA) hne))
  exact ⟨exp_pos _, h _ (by decide) (by decide), exp_pos _, h _ (by decide) (by decide),
    exp_pos _, h _ (by decide) (by decide)⟩

/-- Equation (13) on the names of the classes, with `X, Y, Z ∈ (0, 1)`. -/
private theorem tables_pse_formulas (σ : SpeciesTree (Fin 5))
    (hσ : σ.clusters = pseudocaterpillar5) :
    ∃ X Y Z : ℝ, 0 < X ∧ X < 1 ∧ 0 < Y ∧ Y < 1 ∧ 0 < Z ∧ Z < 1 ∧
      u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y + 4 / 9 * X * Y - 2 / 45 * X * Y * Z ^ 6 ∧
      u σ 2 = 1 / 3 * Y - 5 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧
      u σ 4 = 1 / 3 * X - 5 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧
      u σ 5 = 1 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧
      u σ 8 = 1 / 9 * X * Y - 2 / 45 * X * Y * Z ^ 6 := by
  obtain ⟨h1, h2, -, h4, -, h5, -, -, -, -, -, -, -, h8, -⟩ := equation13 σ hσ
  obtain ⟨a, b, c, d, e, f⟩ := tables_pse_bounds σ hσ
  exact ⟨_, _, _, a, b, c, d, e, f, h1, h2, h4, h5, h8⟩

/-- A pseudocaterpillar species tree with prescribed `X, Y, Z ∈ (0, 1)`, and its probabilities. -/
private theorem tables_pse_at (X Y Z : ℝ) (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1)
    (hZ : 0 < Z) (hZ1 : Z < 1) :
    ∃ σ : SpeciesTree (Fin 5), σ.clusters = pseudocaterpillar5 ∧
      u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y + 4 / 9 * X * Y - 2 / 45 * X * Y * Z ^ 6 ∧
      u σ 2 = 1 / 3 * Y - 5 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧
      u σ 4 = 1 / 3 * X - 5 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧
      u σ 5 = 1 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧
      u σ 8 = 1 / 9 * X * Y - 2 / 45 * X * Y * Z ^ 6 := by
  have e1 : ({3, 4} : Finset (Fin 5)) ≠ {0, 1} := by decide
  have e2 : ({0, 1, 3, 4} : Finset (Fin 5)) ≠ {0, 1} := by decide
  have e3 : ({0, 1, 3, 4} : Finset (Fin 5)) ≠ {3, 4} := by decide
  let σ : SpeciesTree (Fin 5) := SpeciesTree.ofLengths pseudocaterpillar5
    (fun A => if A = {0, 1} then -log X else if A = {3, 4} then -log Y else -log Z)
    (by decide) (by decide) (by decide) (by decide) (fun A _ _ _ => by
      split_ifs
      exacts [neg_pos.2 (log_neg hX hX1), neg_pos.2 (log_neg hY hY1),
        neg_pos.2 (log_neg hZ hZ1)])
  have hx : exp (-σ.length {0, 1}) = X := by simp [σ, SpeciesTree.ofLengths, exp_log hX]
  have hy : exp (-σ.length {3, 4}) = Y := by
    simp [σ, SpeciesTree.ofLengths, e1, exp_log hY]
  have hz : exp (-σ.length {0, 1, 3, 4}) = Z := by
    simp [σ, SpeciesTree.ofLengths, e2, e3, exp_log hZ]
  obtain ⟨h1, h2, -, h4, -, h5, -, -, -, -, -, -, -, h8, -⟩ := equation13 σ rfl
  simp only [hx, hy, hz] at h1 h2 h4 h5 h8
  exact ⟨σ, rfl, h1, h2, h4, h5, h8⟩

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

/-- The vectors of Table 3 are linearly independent: each has a coordinate where all the others
vanish. -/
private theorem tables_pse_li : LinearIndependent ℝ table3Basis := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h : ∀ k, (∑ i, g i • table3Basis i) k = 0 := fun k => congrFun hg k
  have h13 := h 13
  have h11 := h 11
  have h9 := h 9
  have h8 := h 8
  have h7 := h 7
  have h6 := h 6
  have h5 := h 5
  have h4 := h 4
  have h3 := h 3
  have h1 := h 1
  simp [Fin.sum_univ_succ, table3Basis, ue] at h13 h11 h9 h8 h7 h6 h5 h4 h3 h1
  intro i
  fin_cases i <;> assumption

/-- The vectors of Table 3 are invariants, by (13). -/
private theorem tables_pse_mem (k : Fin 10) :
    table3Basis k ∈ linearInvariants pseudocaterpillar5 := by
  rw [tables_mem_linearInvariants]
  intro σ hσ
  obtain ⟨-, -, e3, -, e13, -, e6, e7, e9, e10, e12, e14, e15, -, e11⟩ := equation13 σ hσ
  rw [tables_sum15]
  fin_cases k <;> simp [table3Basis, ue] <;> linarith

/-- An invariant vanishes on the five trees with `(X, Y, Z)` equal to `(1/4, 1/4, 1/2)`,
`(1/2, 1/4, 1/2)`, `(1/4, 1/2, 1/2)`, `(1/2, 1/2, 1/2)` and `(1/2, 1/2, 1/4)`, on which the values
of `(u₁, u₂, u₄, u₅, u₈)` are linearly independent: the sums of its coordinates over the classes
vanish. -/
private theorem tables_pse_sums {c : Fin 15 → ℝ} (hc : c ∈ linearInvariants pseudocaterpillar5) :
    c 0 = 0 ∧ c 1 + c 2 = 0 ∧ c 3 + c 12 = 0 ∧
      c 4 + c 5 + c 6 + c 8 + c 9 + c 11 + c 13 + c 14 = 0 ∧ c 7 + c 10 = 0 := by
  rw [tables_mem_linearInvariants] at hc
  have E : ∀ σ : SpeciesTree (Fin 5), σ.clusters = pseudocaterpillar5 →
      c 0 * u σ 1 + (c 1 + c 2) * u σ 2 + (c 3 + c 12) * u σ 4 +
        (c 4 + c 5 + c 6 + c 8 + c 9 + c 11 + c 13 + c 14) * u σ 5 + (c 7 + c 10) * u σ 8 =
          0 := by
    intro σ hσ
    obtain ⟨-, -, e3, -, e13, -, e6, e7, e9, e10, e12, e14, e15, -, e11⟩ := equation13 σ hσ
    have := hc σ hσ
    rw [tables_sum15, e3, e13, e6, e7, e9, e10, e12, e14, e15, e11] at this
    linear_combination this
  obtain ⟨σ₁, hσ₁, a1, a2, a4, a5, a8⟩ := tables_pse_at (1 / 4) (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₂, hσ₂, b1, b2, b4, b5, b8⟩ := tables_pse_at (1 / 2) (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₃, hσ₃, d1, d2, d4, d5, d8⟩ := tables_pse_at (1 / 4) (1 / 2) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₄, hσ₄, f1, f2, f4, f5, f8⟩ := tables_pse_at (1 / 2) (1 / 2) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₅, hσ₅, g1, g2, g4, g5, g8⟩ := tables_pse_at (1 / 2) (1 / 2) (1 / 4) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have E₁ := E σ₁ hσ₁
  have E₂ := E σ₂ hσ₂
  have E₃ := E σ₃ hσ₃
  have E₄ := E σ₄ hσ₄
  have E₅ := E σ₅ hσ₅
  rw [a1, a2, a4, a5, a8] at E₁
  rw [b1, b2, b4, b5, b8] at E₂
  rw [d1, d2, d4, d5, d8] at E₃
  rw [f1, f2, f4, f5, f8] at E₄
  rw [g1, g2, g4, g5, g8] at E₅
  norm_num at E₁ E₂ E₃ E₄ E₅
  clear E hc a1 a2 a4 a5 a8 b1 b2 b4 b5 b8 d1 d2 d4 d5 d8 f1 f2 f4 f5 f8 g1 g2 g4 g5 g8
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- An invariant is the combination of the vectors of Table 3 with the coefficients of its
coordinates `u₁₄, u₁₂, u₁₀, u₉, u₈, u₇, u₆, u₅, u₄, u₂`. -/
private theorem tables_pse_repr {c : Fin 15 → ℝ}
    (h : c 0 = 0 ∧ c 1 + c 2 = 0 ∧ c 3 + c 12 = 0 ∧
      c 4 + c 5 + c 6 + c 8 + c 9 + c 11 + c 13 + c 14 = 0 ∧ c 7 + c 10 = 0) :
    ∑ i, ![c 13, c 11, c 9, c 8, c 7, c 6, c 5, c 4, c 3, c 1] i • table3Basis i = c := by
  obtain ⟨s1, s2, s4, s5, s8⟩ := h
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases k <;> simp [table3Basis, ue] <;> linarith

/-- **Table 3.** The invariants listed form a basis of the homogeneous linear invariants of the
unrooted gene tree distributions of the species tree `(((a,b),(d,e)),c)`. -/
theorem table3 :
    LinearIndependent ℝ table3Basis ∧
      Submodule.span ℝ (Set.range table3Basis) = linearInvariants pseudocaterpillar5 := by
  refine ⟨tables_pse_li, le_antisymm ?_ fun c hc => ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact tables_pse_mem k
  · rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨_, tables_pse_repr (tables_pse_sums hc)⟩

/-- The class of `T_i` in the partition of Section 4.2.3, named by its smallest index:
`{T₁}, {T₂,T₃}, {T₄,T₁₃}, {T₈,T₁₁}, {T₅,T₆,T₇,T₉,T₁₀,T₁₂,T₁₄,T₁₅}`. -/
def pseudocaterpillarClass : ℕ → ℕ
  | 3 => 2 | 13 => 4 | 11 => 8
  | 6 => 5 | 7 => 5 | 9 => 5 | 10 => 5 | 12 => 5 | 14 => 5 | 15 => 5 | i => i

/-- Each `u_k` equals `u` of the name of the class of `T_k`. -/
private theorem tables_pse_cls (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) :
    ∀ k ∈ Icc 1 15, u σ k = u σ (pseudocaterpillarClass k) := by
  obtain ⟨-, -, e3, -, e13, -, e6, e7, e9, e10, e12, e14, e15, -, e11⟩ := equation13 σ hσ
  intro k hk
  obtain ⟨hk1, hk2⟩ := mem_Icc.1 hk
  interval_cases k <;>
    simp only [pseudocaterpillarClass, e3, e13, e6, e7, e9, e10, e12, e14, e15, e11]

/-- The names of the classes. -/
private theorem tables_pse_rep :
    ∀ k ∈ Icc 1 15, pseudocaterpillarClass k ∈ ({1, 2, 4, 5, 8} : Finset ℕ) := by
  decide

/-- A pseudocaterpillar species tree on which the five classes have distinct probabilities. -/
private theorem tables_pse_distinct :
    ∃ σ : SpeciesTree (Fin 5), σ.clusters = pseudocaterpillar5 ∧
      ∀ a ∈ ({1, 2, 4, 5, 8} : Finset ℕ), ∀ b ∈ ({1, 2, 4, 5, 8} : Finset ℕ),
        u σ a = u σ b → a = b := by
  obtain ⟨σ, hσ, a1, a2, a4, a5, a8⟩ := tables_pse_at (9 / 10) (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at a1 a2 a4 a5 a8
  refine ⟨σ, hσ, ?_⟩
  intro a ha b hb e
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; linarith)

/-- The equivalence classes of unrooted gene trees according to their probabilities. -/
theorem pseudocaterpillar_classes (i j : ℕ) (hi : i ∈ Icc 1 15) (hj : j ∈ Icc 1 15) :
    (∀ σ : SpeciesTree (Fin 5), σ.clusters = pseudocaterpillar5 → u σ i = u σ j) ↔
      pseudocaterpillarClass i = pseudocaterpillarClass j := by
  constructor
  · intro h
    obtain ⟨σ, hσ, hd⟩ := tables_pse_distinct
    refine hd _ (tables_pse_rep i hi) _ (tables_pse_rep j hj) ?_
    rw [← tables_pse_cls σ hσ i hi, ← tables_pse_cls σ hσ j hj]
    exact h σ hσ
  · intro h σ hσ
    rw [tables_pse_cls σ hσ i hi, tables_pse_cls σ hσ j hj, h]

/-- **Inequalities (6)**: for all branch lengths, `u₁ > u₂ > u₅`, `u₁ > u₄ > u₅` and
`u₁ > u₈ > u₅`. -/
theorem equation6 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) :
    u σ 1 > u σ 2 ∧ u σ 1 > u σ 4 ∧ u σ 1 > u σ 8 ∧ u σ 2 > u σ 5 ∧ u σ 4 > u σ 5 ∧
      u σ 8 > u σ 5 := by
  obtain ⟨X, Y, Z, hX, hX1, hY, hY1, hZ, hZ1, h1, h2, h4, h5, h8⟩ := tables_pse_formulas σ hσ
  rw [h1, h2, h4, h5, h8]
  have hX' : 0 < 1 - X := by linarith
  have hY' : 0 < 1 - Y := by linarith
  have hZ6 : Z ^ 6 < 1 := pow_lt_one₀ hZ.le hZ1 (by norm_num)
  -- `u₁ - u₂ = k₁ + k₈/18`, `u₁ - u₄ = k₂ + k₈/18`, `u₁ - u₈ = k₃ + (k₄ + k₅)/3`,
  -- `u₂ - u₅ = k₄/3`, `u₄ - u₅ = k₅/3`, `u₈ - u₅ = k₈/18`
  have k1 : 0 < (1 - Y) * (1 - 2 / 3 * X) := mul_pos hY' (by linarith)
  have k2 : 0 < (1 - X) * (1 - 2 / 3 * Y) := mul_pos hX' (by linarith)
  have k3 : 0 < (1 - X) * (1 - Y) := mul_pos hX' hY'
  have k4 : 0 < Y * (1 - X) := mul_pos hY hX'
  have k5 : 0 < X * (1 - Y) := mul_pos hX hY'
  have k8 : 0 < X * Y * (1 - Z ^ 6) := mul_pos (mul_pos hX hY) (by linarith)
  exact ⟨by linarith only [k1, k8], by linarith only [k2, k8], by linarith only [k3, k4, k5],
    by linarith only [k4], by linarith only [k5], by linarith only [k8]⟩

/-- The strict order between classes generated by the inequalities (6). -/
def pseudocaterpillarOrder : Finset (ℕ × ℕ) :=
  {(1, 2), (1, 4), (1, 8), (1, 5), (2, 5), (4, 5), (8, 5)}

/-- Between the names of the classes, the inequalities holding for all branch lengths are those of
`pseudocaterpillarOrder`: the other ones fail on one of the trees with `(X, Y, Z)` equal to
`(1/4, 1/4, 1/2)`, `(9/10, 1/4, 1/2)` or `(1/4, 9/10, 1/2)`. -/
private theorem tables_pse_order : ∀ a ∈ ({1, 2, 4, 5, 8} : Finset ℕ),
    ∀ b ∈ ({1, 2, 4, 5, 8} : Finset ℕ),
      ((∀ σ : SpeciesTree (Fin 5), σ.clusters = pseudocaterpillar5 → u σ a > u σ b) ↔
        (a, b) ∈ pseudocaterpillarOrder) := by
  obtain ⟨σ₁, hσ₁, a1, a2, a4, a5, a8⟩ := tables_pse_at (1 / 4) (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₂, hσ₂, b1, b2, b4, b5, b8⟩ := tables_pse_at (9 / 10) (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ₃, hσ₃, d1, d2, d4, d5, d8⟩ := tables_pse_at (1 / 4) (9 / 10) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at a1 a2 a4 a5 a8 b1 b2 b4 b5 b8 d1 d2 d4 d5 d8
  intro a ha b hb
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    constructor <;>
    first
      | (intro _; decide)
      | (intro hm; exact absurd hm (by decide))
      | (intro h; have h₁ := h σ₁ hσ₁; have h₂ := h σ₂ hσ₂; have h₃ := h σ₃ hσ₃; exfalso;
          linarith)
      | (intro _ σ hσ; obtain ⟨_, _, _, _, _, _⟩ := equation6 σ hσ; linarith)

/-- Section 4.2.3: there are no inequalities `u_i > u_j` holding for all branch lengths other than
those implied by (6) and the equalities of Table 3. -/
theorem equation6_exhaustive (i j : ℕ) (hi : i ∈ Icc 1 15) (hj : j ∈ Icc 1 15) :
    (∀ σ : SpeciesTree (Fin 5), σ.clusters = pseudocaterpillar5 → u σ i > u σ j) ↔
      (pseudocaterpillarClass i, pseudocaterpillarClass j) ∈ pseudocaterpillarOrder := by
  rw [← tables_pse_order _ (tables_pse_rep i hi) _ (tables_pse_rep j hj)]
  refine forall_congr' fun σ => imp_congr_right fun hσ => ?_
  rw [← tables_pse_cls σ hσ i hi, ← tables_pse_cls σ hσ j hj]

open scoped Classical in
/-- Section 4.2.3: the 8-element class always has the strictly smallest probability. -/
theorem pseudocaterpillar_minClass (σ : SpeciesTree (Fin 5))
    (hσ : σ.clusters = pseudocaterpillar5) :
    {i ∈ Icc 1 15 | ∀ j ∈ Icc 1 15, u σ i ≤ u σ j} = {5, 6, 7, 9, 10, 12, 14, 15} := by
  obtain ⟨h12, h14, h18, h25, h45, h85⟩ := equation6 σ hσ
  obtain ⟨-, -, e3, -, e13, -, e6, e7, e9, e10, e12, e14, e15, -, e11⟩ := equation13 σ hσ
  have K : ∀ j ∈ Icc 1 15, u σ 5 ≤ u σ j := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_Icc.1 hj
    interval_cases j <;> linarith
  ext i
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hi, h⟩
    have h5 := h 5 (by simp)
    obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
    interval_cases i <;> first | (exfalso; linarith) | simp
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨by simp, fun j hj => by linarith [K j hj]⟩

end ADR11
