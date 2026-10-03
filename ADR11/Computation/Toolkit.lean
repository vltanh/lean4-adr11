module

public import ADR11.Computation.Engine
public import ADR11.SmallTrees

/-!
# A toolkit for explicit gene tree distributions of small species trees

This file packages the verified computation of `ADR11.Computation.Engine` into statements about
species trees. To compute the probability of a gene tree under a concrete species tree `σ` with
`σ.clusters = H` on taxa `Fin n` (one lineage per taxon):

1. describe the shape of `H` by a `PTree`: `PTree.node a cs` where `a` is the bitmask code of a
   cluster (`{0, 1} ↦ 3`, `{0, 1, 2} ↦ 7`, the root `univ ↦ 2 ^ n - 1`, a leaf `{x} ↦ 2 ^ x`,
   see `PTree.leaf`) and `cs` its children, in any order;
2. give the target gene tree by a list of codes `g` (rooted: the codes of its clusters; unrooted:
   `unrootL n` of the codes of any rooted version), with `decF n g = G` (by `decide +kernel`);
3. give the expected probability as a polynomial `P`: a list of pairs (rational coefficient,
   monomial), a monomial being a list of pairs (code of a cluster `A`, exponent `e`) standing for
   `∏ (e^{-len A})^e`; the factors of a monomial must be listed in the order of a post-order
   traversal of the tree shape (children before parents, in the order of the lists `cs`), and
   factors with exponent `0` omitted (`normKey`);
4. apply `rootedDist_eq_evalPoly` or `unrootedDist_eq_evalPoly`, proving the well-formedness
   `T.wfB n H = true` and the certificate `certB … = true` by `decide +kernel`; or, for the whole
   distribution at once, `rootedDist_eq_sum_targets` / `unrootedDist_eq_sum_targets` with
   `certAllB`, which also checks that every gene tree produced is one of the listed targets (so
   that all other gene trees have probability `0`);
5. evaluate `evalPoly` with `simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil]`,
   rewrite the codes `decC n a` into clusters (`decide +kernel`), `push_cast` and `ring`.

A wrong polynomial makes the certificate evaluate to `false` (and `decide` fail). On `Fin 5` the
full computation of the unrooted distribution of a species tree takes at most a few seconds in
the kernel.

## Organization of `ADR11.Computation`

* `ADR11.Computation.Codes`: bitmask codes of clusters (`decC`, `decF`) and their dictionary with
  roots, merges, `unroot`, the jump chain (`jumpL`, `jumpMatrix_pow_decF`).
* `ADR11.Computation.Engine`: the program (`PTree.rootedL`, `PTree.unrootedL`) and its
  correctness (`PTree.rootedL_spec`, `PTree.unrootedL_spec`); `forestDist_eq_iterSum` unfolds
  `forestDist` at a cluster with any list of children.
* this file: certificates and the statements about species trees.
* `ADR11.Computation.ThreeTaxa`, `ADR11.Computation.FourTaxa`: complete gene tree distributions
  of the 3- and 4-taxon species trees; `ADR11.Computation.Caterpillar5`: the rooted examples of
  Section 3; `ADR11.Computation.FiveTaxa`: `u σ i` for the twelve 5-taxon shapes.

## Main results

* `rootedDist_eq_evalPoly`, `unrootedDist_eq_evalPoly`: one gene tree.
* `rootedDist_eq_sum_targets`, `unrootedDist_eq_sum_targets`: the whole distribution, as a
  function of the gene tree; `rootedDist_eq_ite₃`, `unrootedDist_eq_ite₃`: the same as nested
  `if`s when three gene trees have positive probability.
* `forestDist_univ_eq_sum_targets`, `unrootedDistOf_eq_sum_targets`: the same for raw data and
  any sampling map `s : Fin m → Fin n` (several lineages per taxon).
* `ite₃_eq_first`, `ite₃_eq_second`, `ite₃_eq_third`: evaluating such nested `if`s.
-/

@[expose] public section

namespace ADR11.Computation

open Finset

/-- The tree shape of a leaf `{x}`. -/
def PTree.leaf (x : ℕ) : PTree := .node (2 ^ x) []

/-! ### Certificates -/

/-- Whether two code lists have the same elements. -/
def sameSet (a b : List ℕ) : Bool := a.all (· ∈ b) && b.all (· ∈ a)

theorem decF_eq_iff_sameSet {n : ℕ} {a b : List ℕ} (ha : Valid n a) (hb : Valid n b) :
    decF n a = decF n b ↔ sameSet a b = true := by
  rw [decF_eq_iff ha hb]
  simp [sameSet, List.all_eq_true]

/-- The monomial without its trivial factors. -/
def normKey (k : List (ℕ × ℕ)) : List (ℕ × ℕ) := k.filter (·.2 != 0)

theorem monoVal_normKey {n : ℕ} (len : Finset (Fin n) → ℝ) (k : List (ℕ × ℕ)) :
    monoVal len (normKey k) = monoVal len k := by
  induction k with
  | nil => rfl
  | cons ae k ih =>
    by_cases h : ae.2 = 0
    · simp [normKey, h] at ih ⊢; exact ih
    · simp [normKey, h] at ih ⊢; rw [ih]

/-- The total coefficient of the monomial `k` in a list of (coefficient, monomial). -/
def coefSum (P : List (ℚ × List (ℕ × ℕ))) (k : List (ℕ × ℕ)) : ℚ :=
  ((P.filter fun p => decide (p.2 = k)).map (·.1)).sum

/-- Whether two lists of (coefficient, monomial) define the same polynomial. -/
def polyEqB (P Q : List (ℚ × List (ℕ × ℕ))) : Bool :=
  (P.map (·.2) ++ Q.map (·.2)).all fun k => decide (coefSum P k = coefSum Q k)

/-- The value of a polynomial given as a list of (coefficient, monomial). -/
noncomputable def evalPoly {n : ℕ} (len : Finset (Fin n) → ℝ) (P : List (ℚ × List (ℕ × ℕ))) :
    ℝ :=
  (P.map fun p => (p.1 : ℝ) * monoVal len p.2).sum

@[simp] theorem evalPoly_nil {n : ℕ} (len : Finset (Fin n) → ℝ) : evalPoly len [] = 0 := rfl

@[simp] theorem evalPoly_cons {n : ℕ} (len : Finset (Fin n) → ℝ) (p : ℚ × List (ℕ × ℕ))
    (P : List (ℚ × List (ℕ × ℕ))) :
    evalPoly len (p :: P) = (p.1 : ℝ) * monoVal len p.2 + evalPoly len P := rfl

theorem evalPoly_eq_sum_coefSum {n : ℕ} (len : Finset (Fin n) → ℝ) (P : List (ℚ × List (ℕ × ℕ)))
    (S : Finset (List (ℕ × ℕ))) (hS : ∀ p ∈ P, p.2 ∈ S) :
    evalPoly len P = ∑ k ∈ S, (coefSum P k : ℝ) * monoVal len k := by
  induction P with
  | nil => simp [evalPoly, coefSum]
  | cons p P ih =>
    rw [evalPoly_cons, ih fun q hq => hS q (List.mem_cons_of_mem _ hq)]
    have hcs : ∀ k, coefSum (p :: P) k = (if p.2 = k then p.1 else 0) + coefSum P k := by
      intro k
      by_cases h : p.2 = k <;> simp [coefSum, h]
    simp only [hcs, Rat.cast_add, add_mul, Finset.sum_add_distrib]
    congr 1
    simp only [apply_ite (fun x : ℚ => (x : ℝ)), Rat.cast_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, hS p List.mem_cons_self, ite_true]

theorem evalPoly_eq_of_polyEqB {n : ℕ} (len : Finset (Fin n) → ℝ)
    {P Q : List (ℚ × List (ℕ × ℕ))} (h : polyEqB P Q = true) :
    evalPoly len P = evalPoly len Q := by
  simp only [polyEqB, List.all_eq_true, decide_eq_true_eq] at h
  let S := (P.map (·.2) ++ Q.map (·.2)).toFinset
  rw [evalPoly_eq_sum_coefSum len P S (fun p hp => by simp [S]; exact Or.inl ⟨p.1, hp⟩),
    evalPoly_eq_sum_coefSum len Q S (fun p hp => by simp [S]; exact Or.inr ⟨p.1, hp⟩)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [h k (List.mem_toFinset.1 hk)]

/-- The (coefficient, monomial) pairs of the terms whose family has the codes `u`. -/
def collect (M : List CTerm) (u : List ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  (M.filter fun τ => sameSet τ.forest u).map fun τ => (τ.coef, normKey τ.key)

theorem sum_eq_evalPoly_collect {m n : ℕ} (len : Finset (Fin n) → ℝ) (M : List CTerm)
    (u : List ℕ) (hM : ∀ τ ∈ M, Valid m τ.forest) (hu : Valid m u) :
    (M.map fun τ => if decF m τ.forest = decF m u then τ.val len else 0).sum =
      evalPoly len (collect M u) := by
  induction M with
  | nil => rfl
  | cons τ M ih =>
    have ih' := ih fun τ' h => hM τ' (List.mem_cons_of_mem _ h)
    have hiff := decF_eq_iff_sameSet (hM τ List.mem_cons_self) hu
    rw [List.map_cons, List.sum_cons, ih']
    by_cases h : sameSet τ.forest u = true
    · rw [ite_eq_left (hiff.2 h)]
      simp [collect, h, CTerm.val, monoVal_normKey]
    · rw [ite_eq_right (fun h' => h (hiff.1 h'))]
      simp [collect, h]

/-- Checks that the computation `R` succeeded with valid codes, and that the probability of the
family with codes `u` is the polynomial `P`. -/
def certB (m : ℕ) (R : Option (List CTerm)) (u : List ℕ) (P : List (ℚ × List (ℕ × ℕ))) : Bool :=
  match R with
  | some M => decide (Valid m u) && M.all (fun τ => decide (Valid m τ.forest)) &&
      polyEqB (collect M u) P
  | none => false

theorem eq_evalPoly_of_certB {m n : ℕ} (len : Finset (Fin n) → ℝ) {R : Option (List CTerm)}
    {u : List ℕ} {P : List (ℚ × List (ℕ × ℕ))} (h : certB m R u P = true) :
    ∃ M, R = some M ∧
      (M.map fun τ => if decF m τ.forest = decF m u then τ.val len else 0).sum =
        evalPoly len P := by
  unfold certB at h
  split at h
  · rename_i M
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨hu, hM⟩, hP⟩ := h
    exact ⟨M, rfl, by rw [sum_eq_evalPoly_collect len M u hM hu, evalPoly_eq_of_polyEqB len hP]⟩
  · simp at h

/-- Checks that the computation `R` succeeded with valid codes, that every family produced is one
of the targets (exactly one), and that the probability of each target is the given polynomial. -/
def certAllB (m : ℕ) (R : Option (List CTerm))
    (targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))) : Bool :=
  match R with
  | some M => M.all (fun τ => decide (Valid m τ.forest) &&
        (targets.filter fun t => sameSet τ.forest t.1).length == 1) &&
      targets.all (fun t => decide (Valid m t.1) && polyEqB (collect M t.1) t.2)
  | none => false

theorem eq_sum_targets_of_certAllB {m n : ℕ} (len : Finset (Fin n) → ℝ) {R : Option (List CTerm)}
    {targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))} (h : certAllB m R targets = true) :
    ∃ M, R = some M ∧ ∀ U : Finset (Finset (Fin m)),
      (M.map fun τ => if decF m τ.forest = U then τ.val len else 0).sum =
        (targets.map fun t => if decF m t.1 = U then evalPoly len t.2 else 0).sum := by
  unfold certAllB at h
  split at h
  · rename_i M
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨hM, ht⟩ := h
    refine ⟨M, rfl, fun U => ?_⟩
    -- each term is counted at its unique target
    have key : ∀ τ ∈ M, (if decF m τ.forest = U then τ.val len else 0) =
        (targets.map fun t => if decF m t.1 = U then
          (if sameSet τ.forest t.1 = true then τ.val len else 0) else 0).sum := by
      intro τ hτ
      obtain ⟨hv, h1⟩ := hM τ hτ
      obtain ⟨t₀, ht₀⟩ := List.length_eq_one_iff.1 h1
      have hsplit : ∀ l : List (List ℕ × List (ℚ × List (ℕ × ℕ))),
          (l.filter fun t => sameSet τ.forest t.1) = [t₀] →
          (∀ t ∈ l, Valid m t.1) →
          (l.map fun t => if decF m t.1 = U then
            (if sameSet τ.forest t.1 = true then τ.val len else 0) else 0).sum =
          if decF m τ.forest = U then τ.val len else 0 := by
        intro l
        induction l with
        | nil => intro h; simp at h
        | cons t l ih =>
          intro hl hvl
          by_cases hs : sameSet τ.forest t.1 = true
          · simp only [List.filter_cons, hs, ite_true, List.cons.injEq] at hl
            obtain ⟨rfl, hl⟩ := hl
            have hrest : (l.map fun t => if decF m t.1 = U then
                (if sameSet τ.forest t.1 = true then τ.val len else 0) else 0).sum = 0 := by
              apply List.sum_eq_zero
              intro x hx
              obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hx
              have : sameSet τ.forest t'.1 = false := by
                by_contra hc
                have : t' ∈ l.filter fun t => sameSet τ.forest t.1 :=
                  List.mem_filter.2 ⟨ht', by simpa using hc⟩
                rw [hl] at this
                simp at this
              simp [this]
            rw [List.map_cons, List.sum_cons, hrest, add_zero, ite_eq_left hs,
              (decF_eq_iff_sameSet hv (hvl t List.mem_cons_self)).2 hs]
          · simp only [List.filter_cons, hs, Bool.false_eq_true, ite_false] at hl
            rw [List.map_cons, List.sum_cons, ih hl (fun t' h => hvl t' (List.mem_cons_of_mem _ h))]
            simp [hs]
      exact (hsplit targets ht₀ (fun t h => (ht t h).1)).symm
    rw [List.map_congr_left key]
    -- swap the two sums
    have hswap : ∀ (A : List CTerm) (B : List (List ℕ × List (ℚ × List (ℕ × ℕ))))
        (f : CTerm → (List ℕ × List (ℚ × List (ℕ × ℕ))) → ℝ),
        (A.map fun a => (B.map fun b => f a b).sum).sum =
          (B.map fun b => (A.map fun a => f a b).sum).sum := by
      intro A B f
      induction A with
      | nil => simp
      | cons a A ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        rw [← List.sum_map_add]
    rw [hswap]
    congr 1
    apply List.map_congr_left
    intro t htm
    obtain ⟨hvt, hP⟩ := ht t htm
    by_cases hU : decF m t.1 = U
    · simp only [hU, ite_true]
      rw [← evalPoly_eq_of_polyEqB len hP, ← sum_eq_evalPoly_collect len M t.1
        (fun τ h => (hM τ h).1) hvt]
      congr 1
      apply List.map_congr_left
      intro τ hτ
      have hiff := decF_eq_iff_sameSet (hM τ hτ).1 hvt
      by_cases hs : sameSet τ.forest t.1 = true
      · rw [ite_eq_left hs, ite_eq_left (hiff.2 hs)]
      · rw [ite_eq_right hs, ite_eq_right (fun h => hs (hiff.1 h))]
    · simp [hU]
  · simp at h

/-! ### Gene tree distributions of species trees -/

theorem rootedDist_eq_evalPoly {n : ℕ} (σ : SpeciesTree (Fin n)) {H : Finset (Finset (Fin n))}
    (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB n H = true) (htop : T.code = 2 ^ n - 1)
    {g : List ℕ} {G : Finset (Finset (Fin n))} (hg : decF n g = G)
    {P : List (ℚ × List (ℕ × ℕ))} (hc : certB n (T.rootedL n n id) g P = true) :
    σ.rootedDist id G = evalPoly σ.length P := by
  obtain ⟨M, hM, hval⟩ := eq_evalPoly_of_certB σ.length hc
  rw [SpeciesTree.rootedDist, hσ, T.rootedL_spec H σ.length hwf htop M hM G, ← hg, hval]

theorem unrootedDist_eq_evalPoly {n : ℕ} (σ : SpeciesTree (Fin n)) {H : Finset (Finset (Fin n))}
    (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB n H = true) (htop : T.code = 2 ^ n - 1)
    {u : List ℕ} {U : Finset (Finset (Fin n))} (hu : decF n u = U)
    {P : List (ℚ × List (ℕ × ℕ))} (hc : certB n (T.unrootedL n n id) u P = true) :
    σ.unrootedDist id U = evalPoly σ.length P := by
  obtain ⟨M, hM, hval⟩ := eq_evalPoly_of_certB σ.length hc
  rw [SpeciesTree.unrootedDist_eq_unrootedDistOf, hσ,
    T.unrootedL_spec H σ.length hwf htop M hM U, ← hu, hval]

theorem unrootedDist_eq_sum_targets {n : ℕ} (σ : SpeciesTree (Fin n))
    {H : Finset (Finset (Fin n))} (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB n H = true)
    (htop : T.code = 2 ^ n - 1) {targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))}
    (hc : certAllB n (T.unrootedL n n id) targets = true) (U : Finset (Finset (Fin n))) :
    σ.unrootedDist id U =
      (targets.map fun t => if decF n t.1 = U then evalPoly σ.length t.2 else 0).sum := by
  obtain ⟨M, hM, hval⟩ := eq_sum_targets_of_certAllB σ.length hc
  rw [SpeciesTree.unrootedDist_eq_unrootedDistOf, hσ,
    T.unrootedL_spec H σ.length hwf htop M hM U, hval]

theorem rootedDist_eq_sum_targets {n : ℕ} (σ : SpeciesTree (Fin n))
    {H : Finset (Finset (Fin n))} (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB n H = true)
    (htop : T.code = 2 ^ n - 1) {targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))}
    (hc : certAllB n (T.rootedL n n id) targets = true) (G : Finset (Finset (Fin n))) :
    σ.rootedDist id G =
      (targets.map fun t => if decF n t.1 = G then evalPoly σ.length t.2 else 0).sum := by
  obtain ⟨M, hM, hval⟩ := eq_sum_targets_of_certAllB σ.length hc
  rw [SpeciesTree.rootedDist, hσ, T.rootedL_spec H σ.length hwf htop M hM G, hval]

/-- The rooted gene tree distribution for raw data `H`, `len` and any sampling map
`s : Fin m → Fin n` (several lineages per taxon are allowed; each population above a non-root
cluster must receive at most four lineages, otherwise the computation fails). -/
theorem forestDist_univ_eq_sum_targets {m n : ℕ} (H : Finset (Finset (Fin n)))
    (len : Finset (Fin n) → ℝ) (s : Fin m → Fin n) (T : PTree) (hwf : T.wfB n H = true)
    (htop : T.code = 2 ^ n - 1) {targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))}
    (hc : certAllB m (T.rootedL m n s) targets = true) (G : Finset (Finset (Fin m))) :
    forestDist H len s univ G =
      (targets.map fun t => if decF m t.1 = G then evalPoly len t.2 else 0).sum := by
  obtain ⟨M, hM, hval⟩ := eq_sum_targets_of_certAllB len hc
  rw [T.rootedL_spec H len hwf htop M hM G, hval]

/-- The unrooted gene tree distribution for raw data `H`, `len` and any sampling map
`s : Fin m → Fin n` (with the same restriction as `forestDist_univ_eq_sum_targets`). -/
theorem unrootedDistOf_eq_sum_targets {m n : ℕ} (H : Finset (Finset (Fin n)))
    (len : Finset (Fin n) → ℝ) (s : Fin m → Fin n) (T : PTree) (hwf : T.wfB n H = true)
    (htop : T.code = 2 ^ n - 1) {targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))}
    (hc : certAllB m (T.unrootedL m n s) targets = true) (U : Finset (Finset (Fin m))) :
    unrootedDistOf H len s U =
      (targets.map fun t => if decF m t.1 = U then evalPoly len t.2 else 0).sum := by
  obtain ⟨M, hM, hval⟩ := eq_sum_targets_of_certAllB len hc
  rw [T.unrootedL_spec H len hwf htop M hM U, hval]

/-- A sum over three distinct targets, as nested `if`s. -/
theorem eq_ite_of_sum_targets₃ {α : Type*} {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x y z : ℝ) (U : α) [DecidableEq α] :
    ((if a = U then x else 0) + ((if b = U then y else 0) + ((if c = U then z else 0) + 0))) =
      if U = a then x else if U = b then y else if U = c then z else 0 := by
  rcases eq_or_ne U a with rfl | ha
  · simp [hab.symm, hac.symm]
  · rcases eq_or_ne U b with rfl | hb
    · simp [ha, ha.symm, hbc.symm]
    · rcases eq_or_ne U c with rfl | hc
      · simp [ha, ha.symm, hb, hb.symm]
      · simp [ha, hb, hc, ha.symm, hb.symm, hc.symm]

/-- The whole rooted gene tree distribution, when only three gene trees have positive
probability. -/
theorem rootedDist_eq_ite₃ {n : ℕ} (σ : SpeciesTree (Fin n)) {H : Finset (Finset (Fin n))}
    (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB n H = true) (htop : T.code = 2 ^ n - 1)
    {t₁ t₂ t₃ : List ℕ} {P₁ P₂ P₃ : List (ℚ × List (ℕ × ℕ))}
    (hc : certAllB n (T.rootedL n n id) [(t₁, P₁), (t₂, P₂), (t₃, P₃)] = true)
    {G₁ G₂ G₃ : Finset (Finset (Fin n))} (h₁ : decF n t₁ = G₁) (h₂ : decF n t₂ = G₂)
    (h₃ : decF n t₃ = G₃) (h₁₂ : G₁ ≠ G₂) (h₁₃ : G₁ ≠ G₃) (h₂₃ : G₂ ≠ G₃)
    (G : Finset (Finset (Fin n))) :
    σ.rootedDist id G =
      if G = G₁ then evalPoly σ.length P₁ else if G = G₂ then evalPoly σ.length P₂
      else if G = G₃ then evalPoly σ.length P₃ else 0 := by
  rw [rootedDist_eq_sum_targets σ hσ T hwf htop hc G]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h₁, h₂, h₃]
  exact eq_ite_of_sum_targets₃ h₁₂ h₁₃ h₂₃ _ _ _ G

/-- The whole unrooted gene tree distribution, when only three gene trees have positive
probability. -/
theorem unrootedDist_eq_ite₃ {n : ℕ} (σ : SpeciesTree (Fin n)) {H : Finset (Finset (Fin n))}
    (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB n H = true) (htop : T.code = 2 ^ n - 1)
    {t₁ t₂ t₃ : List ℕ} {P₁ P₂ P₃ : List (ℚ × List (ℕ × ℕ))}
    (hc : certAllB n (T.unrootedL n n id) [(t₁, P₁), (t₂, P₂), (t₃, P₃)] = true)
    {U₁ U₂ U₃ : Finset (Finset (Fin n))} (h₁ : decF n t₁ = U₁) (h₂ : decF n t₂ = U₂)
    (h₃ : decF n t₃ = U₃) (h₁₂ : U₁ ≠ U₂) (h₁₃ : U₁ ≠ U₃) (h₂₃ : U₂ ≠ U₃)
    (U : Finset (Finset (Fin n))) :
    σ.unrootedDist id U =
      if U = U₁ then evalPoly σ.length P₁ else if U = U₂ then evalPoly σ.length P₂
      else if U = U₃ then evalPoly σ.length P₃ else 0 := by
  rw [unrootedDist_eq_sum_targets σ hσ T hwf htop hc U]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h₁, h₂, h₃]
  exact eq_ite_of_sum_targets₃ h₁₂ h₁₃ h₂₃ _ _ _ U

/-- Evaluating a distribution given by three nested `if`s at its first target. -/
theorem ite₃_eq_first {α : Type*} [DecidableEq α] (a b c : α) (x y z : ℝ) :
    (if a = a then x else if a = b then y else if a = c then z else 0) = x := by
  simp

/-- Evaluating a distribution given by three nested `if`s at its second target. -/
theorem ite₃_eq_second {α : Type*} [DecidableEq α] {a b : α} (c : α) (x y z : ℝ) (hab : a ≠ b) :
    (if b = a then x else if b = b then y else if b = c then z else 0) = y := by
  simp [Ne.symm hab]

/-- Evaluating a distribution given by three nested `if`s at its third target. -/
theorem ite₃_eq_third {α : Type*} [DecidableEq α] {a b c : α} (x y z : ℝ) (hac : a ≠ c)
    (hbc : b ≠ c) : (if c = a then x else if c = b then y else if c = c then z else 0) = z := by
  simp [Ne.symm hac, Ne.symm hbc]

end ADR11.Computation
