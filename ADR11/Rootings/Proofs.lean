module

public import ADR11.Computation.Toolkit
public import ADR11.Rootings.Support

/-!
# Machinery for the closed forms of `ADR11.Rootings.Statements`

The gene tree distributions of the rootings of the standard unrooted trees are computed by the
verified engine of `ADR11.Computation.Engine`: for a tree shape `T` of the species tree,
`root_u5` (five taxa) and `root_q4` (four taxa) give the probabilities of all the gene trees
`T5 i` (resp. the three quartets) as polynomials `evalPoly τ.length Pᵢ`, from one certificate
`root_certsB … = true` checked by `decide +kernel`. The tactic `root_finish` then turns these
polynomials into the closed forms in the variables `exp (-τ.length C)`.

`root_certsB` is a cheaper variant of `ADR11.Computation.certB` for several gene trees at once:
families of clusters are compared through their bitmasks (`root_collect`), and polynomials by
combining like terms of their difference (`root_polyEqB`).
-/
@[expose] public section

namespace ADR11

open Finset _root_.ADR11.Computation

/-! ### Comparing families of clusters by their bitmasks -/

theorem root_famMask_eq_iff (a b : List ℕ) :
    root_famMask a = root_famMask b ↔ sameSet a b = true := by
  rw [root_famMask_eq_iff_sameSet]
  rfl

/-- `collect`, comparing families by their bitmasks. -/
def root_collect (M : List CTerm) (u : List ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  (M.filter fun τ => root_famMask τ.forest == root_famMask u).map fun τ =>
    (τ.coef, normKey τ.key)

theorem root_collect_eq (M : List CTerm) (u : List ℕ) : root_collect M u = collect M u := by
  unfold root_collect collect
  congr 1
  apply List.filter_congr
  intro τ _
  rw [Bool.eq_iff_iff, beq_iff_eq, root_famMask_eq_iff]

/-! ### Comparing polynomials by combining like terms -/

/-- Adds a term to a polynomial, combining it with the term of the same monomial if there is
one. -/
def root_addTerm (t : ℚ × List (ℕ × ℕ)) : List (ℚ × List (ℕ × ℕ)) → List (ℚ × List (ℕ × ℕ))
  | [] => [t]
  | s :: l => if s.2 = t.2 then (s.1 + t.1, s.2) :: l else s :: root_addTerm t l

theorem root_evalPoly_addTerm {n : ℕ} (len : Finset (Fin n) → ℝ) (t : ℚ × List (ℕ × ℕ)) :
    ∀ l, evalPoly len (root_addTerm t l) = t.1 * monoVal len t.2 + evalPoly len l
  | [] => by simp [root_addTerm]
  | s :: l => by
    unfold root_addTerm
    split_ifs with h
    · simp only [evalPoly_cons, h]
      push_cast
      ring
    · simp only [evalPoly_cons, root_evalPoly_addTerm len t l]
      ring

/-- The polynomial with like terms combined. -/
def root_normPoly (P : List (ℚ × List (ℕ × ℕ))) : List (ℚ × List (ℕ × ℕ)) :=
  P.foldr root_addTerm []

theorem root_evalPoly_normPoly {n : ℕ} (len : Finset (Fin n) → ℝ) :
    ∀ P, evalPoly len (root_normPoly P) = evalPoly len P
  | [] => rfl
  | t :: P => by
    rw [root_normPoly, List.foldr_cons, ← root_normPoly, root_evalPoly_addTerm,
      root_evalPoly_normPoly len P, evalPoly_cons]

/-- Whether two polynomials are equal: the coefficients of their difference all vanish once like
terms are combined. -/
def root_polyEqB (P Q : List (ℚ × List (ℕ × ℕ))) : Bool :=
  (root_normPoly (P ++ Q.map fun t => (-t.1, t.2))).all fun t => t.1 == 0

theorem root_evalPoly_append {n : ℕ} (len : Finset (Fin n) → ℝ)
    (P Q : List (ℚ × List (ℕ × ℕ))) : evalPoly len (P ++ Q) = evalPoly len P + evalPoly len Q := by
  simp [evalPoly, List.sum_append]

theorem root_evalPoly_neg {n : ℕ} (len : Finset (Fin n) → ℝ) :
    ∀ Q : List (ℚ × List (ℕ × ℕ)), evalPoly len (Q.map fun t => (-t.1, t.2)) = -evalPoly len Q
  | [] => by simp
  | t :: Q => by
    rw [List.map_cons, evalPoly_cons, evalPoly_cons, root_evalPoly_neg len Q]
    push_cast
    ring

theorem root_evalPoly_eq_of_polyEqB {n : ℕ} (len : Finset (Fin n) → ℝ)
    {P Q : List (ℚ × List (ℕ × ℕ))} (h : root_polyEqB P Q = true) :
    evalPoly len P = evalPoly len Q := by
  have h0 : ∀ L : List (ℚ × List (ℕ × ℕ)), (L.all fun t => t.1 == 0) = true →
      evalPoly len L = 0 := by
    intro L hL
    induction L with
    | nil => rfl
    | cons t L ih =>
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hL
      rw [evalPoly_cons, hL.1, ih hL.2]
      simp
  have e := h0 _ h
  rw [root_evalPoly_normPoly, root_evalPoly_append, root_evalPoly_neg] at e
  linarith

/-! ### Certificates for several gene trees at once -/

/-- Checks that the computation `R` succeeded with valid codes, and that for each target
`(u, P)` the probability of the family with codes `u` is the polynomial `P`. -/
def root_certsB (m : ℕ) (R : Option (List CTerm))
    (targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))) : Bool :=
  match R with
  | some M => M.all (fun τ => decide (Valid m τ.forest)) &&
      targets.all fun t => decide (Valid m t.1) && root_polyEqB (root_collect M t.1) t.2
  | none => false

theorem root_eq_evalPoly_of_certsB {m n : ℕ} (len : Finset (Fin n) → ℝ)
    {R : Option (List CTerm)} {targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))}
    (h : root_certsB m R targets = true) {t : List ℕ × List (ℚ × List (ℕ × ℕ))}
    (ht : t ∈ targets) :
    ∃ M, R = some M ∧
      (M.map fun τ => if decF m τ.forest = decF m t.1 then τ.val len else 0).sum =
        evalPoly len t.2 := by
  cases R with
  | none => simp [root_certsB] at h
  | some M =>
    simp only [root_certsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    refine ⟨M, rfl, ?_⟩
    rw [sum_eq_evalPoly_collect len M t.1 h.1 (h.2 t ht).1, ← root_collect_eq]
    exact root_evalPoly_eq_of_polyEqB len (h.2 t ht).2

/-- The probability of an unrooted gene tree, from a certificate for several gene trees. -/
theorem root_unrootedDist_eq_evalPoly {n : ℕ} (σ : SpeciesTree (Fin n))
    {H : Finset (Finset (Fin n))} (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB n H = true)
    (htop : T.code = 2 ^ n - 1) {targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))}
    (hc : root_certsB n (T.unrootedL n n id) targets = true)
    {t : List ℕ × List (ℚ × List (ℕ × ℕ))} (ht : t ∈ targets) {U : Finset (Finset (Fin n))}
    (hu : decF n t.1 = U) : σ.unrootedDist id U = evalPoly σ.length t.2 := by
  obtain ⟨M, hM, hval⟩ := root_eq_evalPoly_of_certsB σ.length hc ht
  rw [SpeciesTree.unrootedDist_eq_unrootedDistOf, hσ,
    T.unrootedL_spec H σ.length hwf htop M hM U, ← hu, hval]

/-- The fifteen gene tree probabilities `u τ i` of a species tree on `Fin 5` with tree shape `T`,
from one certificate. -/
theorem root_u5 (τ : SpeciesTree (Fin 5)) {H : Finset (Finset (Fin 5))} (hτ : τ.clusters = H)
    (T : PTree) (hwf : T.wfB 5 H = true) (htop : T.code = 31)
    {P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ P₁₀ P₁₁ P₁₂ P₁₃ P₁₄ P₁₅ : List (ℚ × List (ℕ × ℕ))}
    (hc : root_certsB 5 (T.unrootedL 5 5 id)
      [(root_T5code 1, P₁), (root_T5code 2, P₂), (root_T5code 3, P₃), (root_T5code 4, P₄),
       (root_T5code 5, P₅), (root_T5code 6, P₆), (root_T5code 7, P₇), (root_T5code 8, P₈),
       (root_T5code 9, P₉), (root_T5code 10, P₁₀), (root_T5code 11, P₁₁),
       (root_T5code 12, P₁₂), (root_T5code 13, P₁₃), (root_T5code 14, P₁₄),
       (root_T5code 15, P₁₅)] = true) :
    u τ 1 = evalPoly τ.length P₁ ∧ u τ 2 = evalPoly τ.length P₂ ∧
    u τ 3 = evalPoly τ.length P₃ ∧ u τ 4 = evalPoly τ.length P₄ ∧
    u τ 5 = evalPoly τ.length P₅ ∧ u τ 6 = evalPoly τ.length P₆ ∧
    u τ 7 = evalPoly τ.length P₇ ∧ u τ 8 = evalPoly τ.length P₈ ∧
    u τ 9 = evalPoly τ.length P₉ ∧ u τ 10 = evalPoly τ.length P₁₀ ∧
    u τ 11 = evalPoly τ.length P₁₁ ∧ u τ 12 = evalPoly τ.length P₁₂ ∧
    u τ 13 = evalPoly τ.length P₁₃ ∧ u τ 14 = evalPoly τ.length P₁₄ ∧
    u τ 15 = evalPoly τ.length P₁₅ := by
  have key : ∀ i ∈ Icc 1 15, ∀ P, (root_T5code i, P) ∈
      [(root_T5code 1, P₁), (root_T5code 2, P₂), (root_T5code 3, P₃), (root_T5code 4, P₄),
       (root_T5code 5, P₅), (root_T5code 6, P₆), (root_T5code 7, P₇), (root_T5code 8, P₈),
       (root_T5code 9, P₉), (root_T5code 10, P₁₀), (root_T5code 11, P₁₁),
       (root_T5code 12, P₁₂), (root_T5code 13, P₁₃), (root_T5code 14, P₁₄),
       (root_T5code 15, P₁₅)] → u τ i = evalPoly τ.length P :=
    fun i hi P hm => root_unrootedDist_eq_evalPoly τ hτ T hwf htop hc hm (root_decF_T5code hi)
  refine ⟨key 1 (by decide) _ (by simp), key 2 (by decide) _ (by simp),
    key 3 (by decide) _ (by simp), key 4 (by decide) _ (by simp), key 5 (by decide) _ (by simp),
    key 6 (by decide) _ (by simp), key 7 (by decide) _ (by simp), key 8 (by decide) _ (by simp),
    key 9 (by decide) _ (by simp), key 10 (by decide) _ (by simp),
    key 11 (by decide) _ (by simp), key 12 (by decide) _ (by simp),
    key 13 (by decide) _ (by simp), key 14 (by decide) _ (by simp),
    key 15 (by decide) _ (by simp)⟩

theorem root_decC5_3 : decC 5 3 = {0, 1} := by decide +kernel
theorem root_decC5_7 : decC 5 7 = {0, 1, 2} := by decide +kernel
theorem root_decC5_15 : decC 5 15 = {0, 1, 2, 3} := by decide +kernel
theorem root_decC5_23 : decC 5 23 = {0, 1, 2, 4} := by decide +kernel
theorem root_decC5_24 : decC 5 24 = {3, 4} := by decide +kernel
theorem root_decC5_27 : decC 5 27 = {0, 1, 3, 4} := by decide +kernel
theorem root_decC5_28 : decC 5 28 = {2, 3, 4} := by decide +kernel
theorem root_decC5_29 : decC 5 29 = {0, 2, 3, 4} := by decide +kernel
theorem root_decC5_30 : decC 5 30 = {1, 2, 3, 4} := by decide +kernel

/-! ### Four taxa -/

/-- The three quartet probabilities of a species tree on `Fin 4` with tree shape `T`, from one
certificate. -/
theorem root_q4 (τ : SpeciesTree (Fin 4)) {H : Finset (Finset (Fin 4))} (hτ : τ.clusters = H)
    (T : PTree) (hwf : T.wfB 4 H = true) (htop : T.code = 15)
    {P₁ P₂ P₃ : List (ℚ × List (ℕ × ℕ))}
    (hc : root_certsB 4 (T.unrootedL 4 4 id)
      [(root_Q4code 3, P₁), (root_Q4code 5, P₂), (root_Q4code 9, P₃)] = true) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = evalPoly τ.length P₁ ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = evalPoly τ.length P₂ ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = evalPoly τ.length P₃ :=
  ⟨root_unrootedDist_eq_evalPoly τ hτ T hwf htop hc (t := (root_Q4code 3, P₁))
      List.mem_cons_self root_decF_Q4code_3,
    root_unrootedDist_eq_evalPoly τ hτ T hwf htop hc (t := (root_Q4code 5, P₂))
      (List.mem_cons_of_mem _ List.mem_cons_self) root_decF_Q4code_5,
    root_unrootedDist_eq_evalPoly τ hτ T hwf htop hc (t := (root_Q4code 9, P₃))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      root_decF_Q4code_9⟩

theorem root_decC4_3 : decC 4 3 = {0, 1} := by decide +kernel
theorem root_decC4_12 : decC 4 12 = {2, 3} := by decide +kernel

/-! ### Closing the goals -/

/-- Proves a conjunction of equations `p = e`, where `e` is a closed form in the variables
`exp (-τ.length C)` (possibly introduced by `let`), from hypotheses `p = evalPoly τ.length P` in
the context. -/
macro "root_finish" : tactic => `(tactic| (
  try dsimp only
  simp only [*, evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, root_decC5_3,
    root_decC5_7, root_decC5_15, root_decC5_23, root_decC5_24, root_decC5_27, root_decC5_28,
    root_decC5_29, root_decC5_30, root_decC4_3, root_decC4_12]
  push_cast
  repeat' apply And.intro
  all_goals ring))

end ADR11
