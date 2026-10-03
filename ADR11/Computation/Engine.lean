module

public import ADR11.Computation.Codes
public import ADR11.MSC.Basic

/-!
# A verified computation of gene tree distributions

For a species tree whose shape is given by a `PTree` (a cluster code and the list of its
children), `PTree.rootedL` and `PTree.unrootedL` compute, by a program that the kernel can run,
the rooted and the unrooted gene tree distributions as lists of terms `CTerm`: a rational
coefficient, a monomial in the `e^{-len A}` (one factor per non-root cluster `A`, as a pair
(code of `A`, exponent)), and a family of clusters (a rooted gene tree, or the sides of the
splits of an unrooted one). `PTree.rootedL_spec` and `PTree.unrootedL_spec` prove that the
computation is the multispecies coalescent model, whenever the tree shape is well formed for
the clusters of the species tree (`PTree.wfB`, decidable) and the computation succeeds.

## Main steps

* `kingmanTransition_eq_sum_range`: over a time `t`, Kingman's coalescent from a forest with
  `k ≥ 1` roots is `∑_{j < k} g_{k,k-j}(t) J^j`; `deathProb_eq_gPoly`: the `g_kj` for
  `2 ≤ k ≤ 4` as polynomials in `e^{-t}`.
* `kernelL_spec`, `absorbL_spec`, `outcomeL_spec`: one population above a non-root cluster, above
  the root (rooted gene trees), above the root (unrooted gene trees, by first-step analysis until
  at most three roots cover all lineages).
* `forestDist_eq_iterSum`: unfolding `forestDist` at a cluster with any list of children.
* `PTree.out_spec`, `PTree.prodL_spec`: the recursion over the species tree.
-/

@[expose] public section

namespace ADR11.Computation

open Finset

/-! ### Kingman's coalescent over a finite time, along the jump chain -/

theorem kingmanTransition_eq_sum_range {L : Type*} [Fintype L] [DecidableEq L]
    {F : Finset (Finset L)} (hF : IsForest F) (hk : 1 ≤ #(roots F)) (t : ℝ)
    (G : Finset (Finset L)) :
    kingmanTransition t F G =
      ∑ j ∈ range #(roots F), deathProb #(roots F) (#(roots F) - j) t * (jumpMatrix ^ j) F G := by
  rw [kingmanTransition_apply hF]
  have hsupp : ∀ j, (jumpMatrix ^ j) F G ≠ 0 →
      #(roots G) = if j < #(roots F) then #(roots F) - j else min (#(roots F)) 1 :=
    fun j h => (jumpMatrix_pow_support hF h).2.2.2
  have hzero : ∀ j ∈ range #(roots F), #(roots F) - j ≠ #(roots G) →
      (jumpMatrix ^ j) F G = 0 := by
    intro j hj hne
    by_contra h
    have := hsupp j h
    rw [mem_range] at hj
    rw [ite_eq_left hj] at this
    exact hne this.symm
  by_cases hr : 1 ≤ #(roots G) ∧ #(roots G) ≤ #(roots F)
  · rw [Finset.sum_eq_single (#(roots F) - #(roots G))]
    · congr 2; omega
    · intro j hj hne
      rw [hzero j hj (by omega), mul_zero]
    · intro h; exfalso; rw [mem_range] at h; omega
  · have hL : deathProb (#(roots F)) (#(roots G)) t *
        (jumpMatrix ^ (#(roots F) - #(roots G))) F G = 0 := by
      by_cases hgt : #(roots F) < #(roots G)
      · rw [deathProb_eq_zero_of_lt hgt, zero_mul]
      · have h0 : #(roots G) = 0 := by omega
        have : (jumpMatrix ^ (#(roots F) - #(roots G))) F G = 0 := by
          by_contra h
          have := hsupp _ h
          split_ifs at this <;> omega
        rw [this, mul_zero]
    rw [hL]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [hzero j hj (by rw [mem_range] at hj; omega), mul_zero]

/-- The closed forms of `g_kj(t)` (`2 ≤ k ≤ 4`) as lists of (coefficient, exponent of
`e^{-t}`). -/
def gPoly : ℕ → ℕ → List (ℚ × ℕ)
  | 2, 1 => [(1, 0), (-1, 1)]
  | 2, 2 => [(1, 1)]
  | 3, 1 => [(1, 0), (-3/2, 1), (1/2, 3)]
  | 3, 2 => [(3/2, 1), (-3/2, 3)]
  | 3, 3 => [(1, 3)]
  | 4, 1 => [(1, 0), (-9/5, 1), (1, 3), (-1/5, 6)]
  | 4, 2 => [(9/5, 1), (-3, 3), (6/5, 6)]
  | 4, 3 => [(2, 3), (-2, 6)]
  | 4, 4 => [(1, 6)]
  | _, _ => []

theorem deathProb_eq_gPoly {k j : ℕ} (hk2 : 2 ≤ k) (hk4 : k ≤ 4) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (t : ℝ) :
    deathProb k j t = ((gPoly k j).map fun ce => (ce.1 : ℝ) * Real.exp (-t) ^ ce.2).sum := by
  have h := deathProb_small t
  dsimp only at h
  obtain ⟨-, -, h21, h22, h31, h32, h33, h41, h42, h43, h44⟩ := h
  interval_cases k <;> interval_cases j <;>
    simp only [gPoly, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h21, h22, h31,
      h32, h33, h41, h42, h43, h44] <;> push_cast <;> ring

/-! ### Weighted terms -/

/-- A term of a distribution: a rational coefficient, a monomial `∏ (e^{-len A})^e` given by the
list of pairs (code of `A`, `e`), and a family of clusters given by codes. -/
structure CTerm where
  coef : ℚ
  key : List (ℕ × ℕ)
  forest : List ℕ

/-- The value of a monomial: `∏ (e^{-len A})^e` over the pairs (code of `A`, `e`). -/
noncomputable def monoVal {n : ℕ} (len : Finset (Fin n) → ℝ) (k : List (ℕ × ℕ)) : ℝ :=
  (k.map fun ae => Real.exp (-len (decC n ae.1)) ^ ae.2).prod

/-- The weight of a term. -/
noncomputable def CTerm.val {n : ℕ} (len : Finset (Fin n) → ℝ) (τ : CTerm) : ℝ :=
  τ.coef * monoVal len τ.key

@[simp] theorem monoVal_nil {n : ℕ} (len : Finset (Fin n) → ℝ) : monoVal len [] = 1 := rfl

@[simp] theorem monoVal_cons {n : ℕ} (len : Finset (Fin n) → ℝ) (ae : ℕ × ℕ)
    (k : List (ℕ × ℕ)) :
    monoVal len (ae :: k) = Real.exp (-len (decC n ae.1)) ^ ae.2 * monoVal len k := by
  simp [monoVal]

theorem monoVal_append {n : ℕ} (len : Finset (Fin n) → ℝ) (k₁ k₂ : List (ℕ × ℕ)) :
    monoVal len (k₁ ++ k₂) = monoVal len k₁ * monoVal len k₂ := by
  simp [monoVal, List.prod_append]

/-! ### The population above a non-root cluster -/

/-- The terms produced from `τ` by a population of code `a`, when `τ.forest` has `k ≥ 2` roots. -/
def kernelAux (a k : ℕ) (τ : CTerm) : List CTerm :=
  (List.range k).flatMap fun j => (gPoly k (k - j)).flatMap fun ce =>
    (jumpL j τ.forest).map fun q => ⟨τ.coef * ce.1 * q.1, τ.key ++ [(a, ce.2)], q.2⟩

/-- The terms produced from `τ` by a population of code `a`, when `τ.forest` has `k` roots;
`none` when `k > 4` (closed forms of `g_kj` are only provided for `k ≤ 4`). -/
def kernelK (a k : ℕ) (τ : CTerm) : Option (List CTerm) :=
  if k ≤ 1 then some [⟨τ.coef, τ.key ++ [(a, 0)], τ.forest⟩]
  else if k ≤ 4 then some (kernelAux a k τ) else none

/-- The terms produced from `τ` by the population above the cluster of code `a` (lineages coded
on `m` bits). -/
def kernelL (m a : ℕ) (τ : CTerm) : Option (List CTerm) :=
  if checkF m τ.forest then kernelK a (rootsL τ.forest).length τ else none

theorem kernelL_spec {m n a : ℕ} (len : Finset (Fin n) → ℝ) {τ : CTerm} {K : List CTerm}
    (h : kernelL m a τ = some K) (G : Finset (Finset (Fin m))) :
    τ.val len * kingmanTransition (len (decC n a)) (decF m τ.forest) G =
      (K.map fun τ' => if decF m τ'.forest = G then τ'.val len else 0).sum := by
  unfold kernelL at h
  split_ifs at h with hc
  obtain ⟨hv, hnd, hF⟩ := of_checkF hc
  have hk := card_roots_decF hv hnd
  unfold kernelK at h
  split_ifs at h with h1 h4
  · cases h
    rw [kingmanTransition_of_card_roots_le_one hF (by omega)]
    rcases eq_or_ne (decF m τ.forest) G with hG | hG
    · subst hG; simp [CTerm.val, monoVal_append]
    · simp [hG, Ne.symm hG]
  · cases h
    rw [kingmanTransition_eq_sum_range hF (by omega), hk, sum_range_eq_list,
      ← List.sum_map_mul_left, kernelAux, sum_map_flatMap]
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    rw [sum_map_flatMap, deathProb_eq_gPoly (by omega) h4 (by omega) (by omega),
      jumpMatrix_pow_decF j _ hv hnd hF G, sum_mul_sum_list, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro ce _
    rw [← List.sum_map_mul_left, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply, CTerm.val, monoVal_append, monoVal_cons, monoVal_nil]
    split_ifs <;> push_cast <;> ring

/-! ### The population above the root -/

theorem kingmanAbsorption_of_card_roots_le_one {L : Type*} [Fintype L] [DecidableEq L]
    {F : Finset (Finset L)} (hF : IsForest F) (hk : #(roots F) ≤ 1) (G : Finset (Finset L)) :
    kingmanAbsorption F G = if G = F then 1 else 0 := by
  rw [kingmanAbsorption_apply hF]
  by_cases h0 : #(roots F) = 0
  · rw [ite_eq_left h0]
  · rw [ite_eq_right h0]
    have h1 : #(roots F) = 1 := by omega
    rw [h1, Nat.sub_self, pow_zero, Matrix.one_apply]
    by_cases hG : G = F
    · subst hG; simp [h1]
    · simp [hG, Ne.symm hG]

/-- The rooted gene trees produced by the population above the root from the forest with codes
`F`, with their probabilities. -/
def absorbL (m : ℕ) (F : List ℕ) : Option (List (ℚ × List ℕ)) :=
  if checkF m F then
    (if (rootsL F).length = 0 then some [(1, F)] else some (jumpL ((rootsL F).length - 1) F))
  else none

theorem absorbL_spec {m : ℕ} {F : List ℕ} {P : List (ℚ × List ℕ)} (h : absorbL m F = some P)
    (G : Finset (Finset (Fin m))) :
    kingmanAbsorption (decF m F) G =
      (P.map fun q => if decF m q.2 = G then (q.1 : ℝ) else 0).sum := by
  unfold absorbL at h
  split_ifs at h with hc h0
  · obtain ⟨hv, hnd, hF⟩ := of_checkF hc
    cases h
    rw [kingmanAbsorption_of_card_roots_le_one hF (by rw [card_roots_decF hv hnd]; omega)]
    rcases eq_or_ne (decF m F) G with hG | hG
    · subst hG; simp
    · simp [hG, Ne.symm hG]
  · obtain ⟨hv, hnd, hF⟩ := of_checkF hc
    cases h
    have hk := card_roots_decF hv hnd
    rw [kingmanAbsorption_apply hF, ite_eq_right (by omega), hk,
      ← jumpMatrix_pow_decF _ _ hv hnd hF G]
    split_ifs with hG
    · rfl
    · by_contra hne
      have := (jumpMatrix_pow_support hF (Ne.symm hne)).2.2.2
      rw [hk] at this
      split_ifs at this with hlt <;> omega

/-- Whether the unrooted topology of the forest with codes `F` is decided (at most one root, or at
most three roots covering all lineages). -/
def stopB (m : ℕ) (F : List ℕ) : Bool :=
  decide ((rootsL F).length ≤ 1) || (decide ((rootsL F).length ≤ 3) && coversB m F)

/-- The unrooted gene trees produced by the population above the root from the forest with codes
`F`, with their probabilities (first-step analysis until the topology is decided; `fuel` bounds
the number of steps). -/
def outcomeL (m : ℕ) : ℕ → List ℕ → Option (List (ℚ × List ℕ))
  | 0, F => if stopB m F then some [(1, unrootL m F)] else none
  | fuel + 1, F => if stopB m F then some [(1, unrootL m F)] else
      flatMapO (fun p => (outcomeL m fuel ((p.1 ||| p.2) :: F)).map
        (List.map fun q => ((((rootsL F).length.choose 2 : ℕ) : ℚ)⁻¹ * q.1, q.2)))
        (pairsL (rootsL F))

theorem unrootedOutcome_of_stopB {m : ℕ} {F : List ℕ} (hv : Valid m F) (hnd : F.Nodup)
    (hF : IsForest (decF m F)) (h : stopB m F = true) (U : Finset (Finset (Fin m))) :
    unrootedOutcome (decF m F) U = if decF m (unrootL m F) = U then 1 else 0 := by
  have hk := card_roots_decF hv hnd
  rw [decF_unrootL hv]
  simp only [stopB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have hle : (rootsL F).length ≤ 1 → unrootedOutcome (decF m F) U =
      if unroot (decF m F) = U then 1 else 0 := by
    intro h1
    have hle : #(roots (decF m F)) ≤ 1 := by omega
    rw [unrootedOutcome, Finset.sum_eq_single (decF m F)]
    · rw [kingmanAbsorption_of_card_roots_le_one hF hle, ite_eq_left rfl]
    · intro G _ hG
      rw [kingmanAbsorption_of_card_roots_le_one hF hle, ite_eq_right hG]
      simp
    · simp
  rcases h with h | ⟨h3, hcov⟩
  · exact hle h
  · by_cases h1 : (rootsL F).length ≤ 1
    · exact hle h1
    · exact unrootedOutcome_of_card_roots_le_three hF (lineages_eq_univ_of_coversB hcov)
        (by omega) (by omega) U

theorem outcomeL_spec {m : ℕ} : ∀ (fuel : ℕ) (F : List ℕ), Valid m F → F.Nodup →
    IsForest (decF m F) → ∀ P, outcomeL m fuel F = some P → ∀ U : Finset (Finset (Fin m)),
    unrootedOutcome (decF m F) U = (P.map fun q => if decF m q.2 = U then (q.1 : ℝ) else 0).sum
  | 0, F, hv, hnd, hF, P, h, U => by
    unfold outcomeL at h
    split_ifs at h with hs
    cases h
    rw [unrootedOutcome_of_stopB hv hnd hF hs]
    simp
  | fuel + 1, F, hv, hnd, hF, P, h, U => by
    unfold outcomeL at h
    split_ifs at h with hs
    · cases h
      rw [unrootedOutcome_of_stopB hv hnd hF hs]
      simp
    · have hk := card_roots_decF hv hnd
      have h2 : 2 ≤ (rootsL F).length := by
        by_contra h2
        apply hs
        simp only [stopB, Bool.or_eq_true, decide_eq_true_eq]
        left; omega
      rw [unrootedOutcome_first_step hF (by omega), sum_merges_decF hv hnd hF, hk,
        ← List.sum_map_mul_left]
      symm
      apply sum_flatMapO h
      intro p hp x hx
      obtain ⟨P', hP', rfl⟩ := Option.map_eq_some_iff.1 hx
      rw [outcomeL_spec fuel _ (valid_merge hv hp) (nodup_merge hv hnd hF hp)
        (isForest_merge hv hnd hF hp) P' hP' U, ← List.sum_map_mul_left, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q _
      simp only [Function.comp_apply]
      split_ifs <;> push_cast <;> ring

/-! ### Unfolding the multispecies coalescent at a cluster with a list of children -/

/-- The iterated sum over the forests leaving the populations of a list of child clusters: the
forests are joined to `S` one at a time, and `φ` is applied to the union. -/
noncomputable def iterSum {ι β : Type*} [Fintype β] [DecidableEq β] (μ : ι → Finset β → ℝ) :
    List ι → Finset β → (Finset β → ℝ) → ℝ
  | [], S, φ => φ S
  | B :: l, S, φ => ∑ F, μ B F * iterSum μ l (F ∪ S) φ

/-- Functions on `insert B C` (for `B ∉ C`) are pairs: a value at `B` and a function on `C`. -/
def piInsertEquiv {ι γ : Type*} [DecidableEq ι] {B : ι} {C : Finset ι} (hB : B ∉ C) :
    (↥(insert B C) → γ) ≃ γ × (↥C → γ) where
  toFun f := (f ⟨B, mem_insert_self B C⟩, fun i => f ⟨i.1, mem_insert_of_mem i.2⟩)
  invFun p i := if h : i.1 = B then p.1 else p.2 ⟨i.1, (mem_insert.1 i.2).resolve_left h⟩
  left_inv f := by
    funext i
    by_cases h : i.1 = B
    · simp only [h, dite_true]
      congr 1
      exact Subtype.ext h.symm
    · simp [h]
  right_inv p := by
    rcases p with ⟨x, f⟩
    simp only [Prod.mk.injEq]
    refine ⟨by simp, ?_⟩
    funext i
    have : i.1 ≠ B := fun h => hB (h ▸ i.2)
    simp [this]

theorem prod_coe_insert {ι M : Type*} [DecidableEq ι] [CommMonoid M] {B : ι} {C : Finset ι}
    (hB : B ∉ C) (h : ↥(insert B C) → M) :
    ∏ i : ↥(insert B C), h i =
      h ⟨B, mem_insert_self B C⟩ * ∏ i : ↥C, h ⟨i.1, mem_insert_of_mem i.2⟩ := by
  rw [Finset.univ_eq_attach, Finset.attach_insert, Finset.prod_insert, Finset.prod_image,
    ← Finset.univ_eq_attach]
  · intro x _ y _ hxy
    exact Subtype.ext (congrArg Subtype.val hxy :)
  · simp only [mem_image, mem_attach, true_and, not_exists]
    intro x hx
    have hxB : (x : ι) = B := congrArg Subtype.val hx
    exact hB (hxB ▸ x.2)

theorem sup_coe_insert {ι β : Type*} [DecidableEq ι] [DecidableEq β] {B : ι} {C : Finset ι}
    (h : ↥(insert B C) → Finset β) :
    univ.sup h = h ⟨B, mem_insert_self B C⟩ ∪ univ.sup fun i : ↥C => h ⟨i.1, mem_insert_of_mem i.2⟩ := by
  rw [Finset.univ_eq_attach, Finset.attach_insert, Finset.sup_insert, Finset.sup_image,
    ← Finset.univ_eq_attach]
  rfl

theorem sum_pi_eq_iterSum {ι β : Type*} [DecidableEq ι] [Fintype β] [DecidableEq β]
    (μ : ι → Finset β → ℝ) (φ : Finset β → ℝ) : ∀ (l : List ι), l.Nodup →
    ∀ (C : Finset ι), C = l.toFinset → ∀ S : Finset β,
    ∑ f : ↥C → Finset β, (∏ B : ↥C, μ B (f B)) * φ (univ.sup f ∪ S) = iterSum μ l S φ
  | [], _, C, hC, S => by
    rw [List.toFinset_nil] at hC
    subst hC
    rw [iterSum, Fintype.sum_unique]
    simp
  | B :: l, hnd, C, hC, S => by
    rw [List.toFinset_cons] at hC
    subst hC
    rw [List.nodup_cons] at hnd
    have hB : B ∉ l.toFinset := by simpa using hnd.1
    rw [iterSum, Fintype.sum_equiv (piInsertEquiv hB) _
      (fun p => μ B p.1 * ((∏ i : ↥l.toFinset, μ i (p.2 i)) * φ (univ.sup p.2 ∪ (p.1 ∪ S))))]
    · rw [Fintype.sum_prod_type]
      congr 1
      ext x
      dsimp only
      rw [← Finset.mul_sum, sum_pi_eq_iterSum μ φ l hnd.2 _ rfl (x ∪ S)]
    · intro f
      rw [prod_coe_insert hB, sup_coe_insert]
      simp only [piInsertEquiv, Equiv.coe_fn_mk]
      rw [mul_assoc, union_assoc, union_left_comm]

theorem forestDist_eq_iterSum {X L : Type*} [Fintype X] [DecidableEq X] [Fintype L]
    [DecidableEq L] {H : Finset (Finset X)} {len : Finset X → ℝ} {s : L → X} {A : Finset X}
    {l : List (Finset X)} (hC : childClusters H A = l.toFinset) (hl : l.Nodup)
    (G : Finset (Finset L)) :
    forestDist H len s A G =
      iterSum (forestDist H len s) l (sampledForest s A) (fun F => populationKernel len A F G) := by
  rw [forestDist]
  exact sum_pi_eq_iterSum (forestDist H len s) (fun F => populationKernel len A F G) l hl _ hC _

theorem sum_collapse {β γ : Type*} [Fintype γ] [DecidableEq γ] (M : List β) (key : β → γ)
    (v : β → ℝ) (ψ : γ → ℝ) :
    ∑ x, (M.map fun b => if key b = x then v b else 0).sum * ψ x =
      (M.map fun b => v b * ψ (key b)).sum := by
  induction M with
  | nil => simp
  | cons b M ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih, ite_mul,
      zero_mul, Finset.sum_ite_eq, mem_univ, ite_true]

theorem sum_ite_list_sum {β γ : Type*} [Fintype γ] (E : List β) (p : γ → Prop) [DecidablePred p]
    (f : β → γ → ℝ) :
    ∑ x, (if p x then (E.map fun b => f b x).sum else 0) =
      (E.map fun b => ∑ x, if p x then f b x else 0).sum := by
  induction E with
  | nil => simp
  | cons b E ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih, ← Finset.sum_add_distrib]
    congr 1
    ext x
    split_ifs <;> simp

/-! ### The species tree recursion -/

/-- A rooted tree shape driving the recursion: the code of a cluster and the list of its
children. -/
inductive PTree where
  | node (a : ℕ) (cs : List PTree)

namespace PTree

/-- The code of the top cluster. -/
def code : PTree → ℕ
  | node a _ => a

/-- The children of the top cluster. -/
def children : PTree → List PTree
  | node _ cs => cs

end PTree

/-- The product of two terms: coefficients and monomials multiply, the family of the second term
is kept. -/
def CTerm.mul (τ τ' : CTerm) : CTerm := ⟨τ.coef * τ'.coef, τ.key ++ τ'.key, τ'.forest⟩

theorem CTerm.val_mul {n : ℕ} (len : Finset (Fin n) → ℝ) (τ τ' : CTerm) :
    (τ.mul τ').val len = τ.val len * τ'.val len := by
  simp only [CTerm.val, CTerm.mul, monoVal_append]; push_cast; ring

section Engine

variable (m n : ℕ) (s : Fin m → Fin n)

mutual
/-- The terms of the distribution of the forest leaving the population above the top cluster of a
tree shape (lineages coded on `m` bits, taxa on `n` bits, sampling map `s`). -/
def PTree.out : PTree → Option (List CTerm)
  | .node a cs => match PTree.prodL cs (sampledL m n s a) with
    | some E => flatMapO (kernelL m a) E
    | none => none
/-- The terms of the joint distribution of the forests leaving the populations of the trees `cs`,
joined to the family of codes `S`. -/
def PTree.prodL : List PTree → List ℕ → Option (List CTerm)
  | [], S => some [⟨1, [], S⟩]
  | c :: cs, S => match PTree.out c with
    | some M => flatMapO (fun τ => (PTree.prodL cs (τ.forest ∪ S)).map (List.map τ.mul)) M
    | none => none
end

mutual
/-- A tree shape is well formed for the clusters `H` (taxa coded on `n` bits) if at every node the
children in `H` of the cluster are exactly the clusters of the children, without repetition, and
the children are proper clusters. -/
def PTree.wfB (H : Finset (Finset (Fin n))) : PTree → Bool
  | .node a cs =>
    decide (childClusters H (decC n a) = (cs.map fun c => decC n c.code).toFinset) &&
      decide (cs.map fun c => decC n c.code).Nodup &&
      cs.all (fun c => decide (c.code < 2 ^ n) && c.code != 2 ^ n - 1) && PTree.wfListB H cs
/-- `PTree.wfB` for a list of trees. -/
def PTree.wfListB (H : Finset (Finset (Fin n))) : List PTree → Bool
  | [] => true
  | c :: cs => PTree.wfB H c && PTree.wfListB H cs
end

/-- The terms of the forest entering the population above the top cluster. -/
def PTree.enteringL (T : PTree) : Option (List CTerm) :=
  PTree.prodL m n s T.children (sampledL m n s T.code)

/-- The terms of the rooted gene tree distribution, for a tree shape whose top cluster is the root
of the species tree. -/
def PTree.rootedL (T : PTree) : Option (List CTerm) :=
  match T.enteringL m n s with
  | some E => flatMapO (fun τ => (absorbL m τ.forest).map
      (List.map fun q => ⟨τ.coef * q.1, τ.key, q.2⟩)) E
  | none => none

/-- `outcomeL` after checking the entering forest. -/
def outcomeRootL (F : List ℕ) : Option (List (ℚ × List ℕ)) :=
  if checkF m F then outcomeL m m F else none

/-- The terms of the unrooted gene tree distribution (the families are unrooted trees), for a tree
shape whose top cluster is the root of the species tree. -/
def PTree.unrootedL (T : PTree) : Option (List CTerm) :=
  match T.enteringL m n s with
  | some E => flatMapO (fun τ => (outcomeRootL m τ.forest).map
      (List.map fun q => ⟨τ.coef * q.1, τ.key, q.2⟩)) E
  | none => none

variable {m n s} (H : Finset (Finset (Fin n))) (len : Finset (Fin n) → ℝ)

theorem wfB_node {a : ℕ} {cs : List PTree} (h : (PTree.node a cs).wfB n H = true) :
    childClusters H (decC n a) = (cs.map fun c => decC n c.code).toFinset ∧
      (cs.map fun c => decC n c.code).Nodup ∧
      (∀ c ∈ cs, c.code < 2 ^ n ∧ c.code ≠ 2 ^ n - 1) ∧ PTree.wfListB n H cs = true := by
  simp only [PTree.wfB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne,
    ne_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

mutual
theorem PTree.out_spec : ∀ (T : PTree), T.wfB n H = true → T.code < 2 ^ n →
    T.code ≠ 2 ^ n - 1 → ∀ M, T.out m n s = some M → ∀ G,
    forestDist H len s (decC n T.code) G =
      (M.map fun τ => if decF m τ.forest = G then τ.val len else 0).sum
  | .node a cs, hwf, hlt, hne, M, hM, G => by
    obtain ⟨hC, hnd, hcodes, hwfl⟩ := wfB_node H hwf
    simp only [PTree.code] at hlt hne ⊢
    simp only [PTree.out] at hM
    split at hM
    · rename_i E hE
      rw [forestDist_eq_iterSum hC hnd G, populationKernel,
        ite_eq_right (fun h => hne ((decC_eq_univ_iff hlt).1 h)), ← decF_sampledL,
        PTree.prodL_spec cs hwfl hcodes _ E hE]
      exact (sum_flatMapO hM _ _ fun τ _ K hK => (kernelL_spec len hK G).symm).symm
    · simp at hM
theorem PTree.prodL_spec : ∀ (cs : List PTree), PTree.wfListB n H cs = true →
    (∀ c ∈ cs, c.code < 2 ^ n ∧ c.code ≠ 2 ^ n - 1) → ∀ S M, PTree.prodL m n s cs S = some M →
    ∀ φ, iterSum (forestDist H len s) (cs.map fun c => decC n c.code) (decF m S) φ =
      (M.map fun τ => τ.val len * φ (decF m τ.forest)).sum
  | [], _, _, S, M, hM, φ => by
    simp only [PTree.prodL, Option.some.injEq] at hM
    subst hM
    simp [iterSum, CTerm.val]
  | c :: cs, hwf, hcodes, S, M, hM, φ => by
    simp only [PTree.wfListB, Bool.and_eq_true] at hwf
    simp only [PTree.prodL] at hM
    split at hM
    · rename_i Mc hMc
      have hc := hcodes c List.mem_cons_self
      simp only [List.map_cons, iterSum]
      simp_rw [PTree.out_spec c hwf.1 hc.1 hc.2 Mc hMc]
      rw [sum_collapse]
      symm
      apply sum_flatMapO hM
      intro τ _ x hx
      obtain ⟨Mτ, hMτ, rfl⟩ := Option.map_eq_some_iff.1 hx
      rw [← decF_union, PTree.prodL_spec cs hwf.2
        (fun c' hc' => hcodes c' (List.mem_cons_of_mem _ hc')) _ Mτ hMτ φ, List.map_map,
        ← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro τ' _
      simp only [Function.comp_apply]
      rw [CTerm.val_mul]
      simp only [CTerm.mul]
      ring
    · simp at hM
end

theorem PTree.forestDist_univ_spec (T : PTree) (hwf : T.wfB n H = true)
    (htop : T.code = 2 ^ n - 1) (E : List CTerm) (hE : T.enteringL m n s = some E)
    (G : Finset (Finset (Fin m))) :
    forestDist H len s univ G =
      (E.map fun τ => τ.val len * kingmanAbsorption (decF m τ.forest) G).sum := by
  obtain ⟨a, cs⟩ := T
  simp only [PTree.code] at htop
  subst htop
  obtain ⟨hC, hnd, hcodes, hwfl⟩ := wfB_node H hwf
  rw [decC_full] at hC
  rw [forestDist_eq_iterSum hC hnd G, populationKernel, ite_eq_left rfl, ← decC_full n,
    ← decF_sampledL]
  exact PTree.prodL_spec H len cs hwfl hcodes _ E hE _

theorem PTree.rootedL_spec (T : PTree) (hwf : T.wfB n H = true) (htop : T.code = 2 ^ n - 1)
    (M : List CTerm) (hM : T.rootedL m n s = some M) (G : Finset (Finset (Fin m))) :
    forestDist H len s univ G =
      (M.map fun τ => if decF m τ.forest = G then τ.val len else 0).sum := by
  unfold PTree.rootedL at hM
  split at hM
  · rename_i E hE
    rw [T.forestDist_univ_spec H len hwf htop E hE G]
    symm
    apply sum_flatMapO hM
    intro τ _ x hx
    obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.1 hx
    rw [absorbL_spec hP G, List.map_map, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply, CTerm.val]
    split_ifs <;> push_cast <;> ring
  · simp at hM

theorem PTree.unrootedL_spec (T : PTree) (hwf : T.wfB n H = true) (htop : T.code = 2 ^ n - 1)
    (M : List CTerm) (hM : T.unrootedL m n s = some M) (U : Finset (Finset (Fin m))) :
    unrootedDistOf H len s U =
      (M.map fun τ => if decF m τ.forest = U then τ.val len else 0).sum := by
  unfold PTree.unrootedL at hM
  split at hM
  · rename_i E hE
    rw [unrootedDistOf]
    simp_rw [T.forestDist_univ_spec H len hwf htop E hE]
    rw [sum_ite_list_sum]
    symm
    apply sum_flatMapO hM
    intro τ _ x hx
    obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.1 hx
    unfold outcomeRootL at hP
    split_ifs at hP with hc
    obtain ⟨hv, hnd, hF⟩ := of_checkF hc
    have hout := outcomeL_spec m _ hv hnd hF P hP U
    have h1 : (∑ x, if unroot x = U then τ.val len * kingmanAbsorption (decF m τ.forest) x
        else 0) = τ.val len * unrootedOutcome (decF m τ.forest) U := by
      rw [unrootedOutcome, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    show _ = ∑ x, if unroot x = U then τ.val len * kingmanAbsorption (decF m τ.forest) x else 0
    rw [h1, hout, List.map_map, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply, CTerm.val]
    split_ifs <;> push_cast <;> ring
  · simp at hM

end Engine

end ADR11.Computation
