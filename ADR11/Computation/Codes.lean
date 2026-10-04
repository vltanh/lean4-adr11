module

public import ADR11.Coalescent.Factorization

/-!
# Bitmask codes for forests of gene lineages

The computations of explicit gene tree distributions (`ADR11.Computation.Engine`) run in the
kernel on lists of natural numbers: a cluster on `Fin n` is coded by the bitmask of its elements,
and a family of clusters by a list of codes. This file relates these codes to the objects of the
model.

* `decC n c`: the cluster with bitmask `c`; `decF n l`: the family of clusters with codes `l`;
  `Valid n l`: all codes are bitmasks of subsets of `Fin n`.
* `rootsL`, `pairsL`: the roots of a family and the unordered pairs of roots, so that the merges
  of `decF n F` are the families `decF n ((a ||| b) :: F)` for `(a, b) ∈ pairsL (rootsL F)`
  (`sum_merges_decF`).
* `jumpL j F`: the paths of length `j` of the jump chain, with their probabilities;
  `jumpMatrix_pow_decF` computes `(jumpMatrix ^ j) (decF n F)` from it.
* `isForestB`, `checkF`: Boolean tests that a family of codes is a forest; `unrootL`: the code
  list of `unroot`; `coversB`: covering all lineages; `sampledL`: the codes of the sampled
  singletons.
* `flatMapO`: `flatMap` for computations that may fail, with `sum_flatMapO`.
-/

@[expose] public section

namespace ADR11.Computation

open Finset

/-! ### Bitmask codes of clusters -/

/-- The cluster on `Fin n` with bitmask `c`: the `i < n` such that bit `i` of `c` is set. -/
def decC (n c : ℕ) : Finset (Fin n) := univ.filter fun i => c.testBit i

/-- The family of clusters with the bitmasks in the list `l`. -/
def decF (n : ℕ) (l : List ℕ) : Finset (Finset (Fin n)) := (l.map (decC n)).toFinset

/-- All codes in `l` are bitmasks of subsets of `Fin n`. -/
def Valid (n : ℕ) (l : List ℕ) : Prop := ∀ c ∈ l, c < 2 ^ n

instance (n : ℕ) (l : List ℕ) : Decidable (Valid n l) :=
  inferInstanceAs (Decidable (∀ c ∈ l, c < 2 ^ n))

theorem mem_decC {n c : ℕ} {i : Fin n} : i ∈ decC n c ↔ c.testBit i = true := by
  simp [decC]

theorem testBit_eq_false_of_lt {n c : ℕ} (hc : c < 2 ^ n) {i : ℕ} (hi : n ≤ i) :
    c.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hi))

theorem decC_inj {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    decC n a = decC n b ↔ a = b := by
  refine ⟨fun h => Nat.eq_of_testBit_eq fun i => ?_, fun h => h ▸ rfl⟩
  by_cases hi : i < n
  · have h' := congrArg (fun A => (⟨i, hi⟩ : Fin n) ∈ A) h
    simp only [mem_decC, eq_iff_iff] at h'
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rw [testBit_eq_false_of_lt ha (not_lt.1 hi), testBit_eq_false_of_lt hb (not_lt.1 hi)]

theorem decC_or (n a b : ℕ) : decC n (a ||| b) = decC n a ∪ decC n b := by
  ext i; simp [mem_decC]

theorem decC_subset_iff {n a b : ℕ} (ha : a < 2 ^ n) :
    decC n a ⊆ decC n b ↔ a &&& b = a := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < n
    · cases ha' : a.testBit i
      · simp
      · have : (⟨i, hi⟩ : Fin n) ∈ decC n b := h (mem_decC.2 ha')
        rw [mem_decC] at this
        simp [this]
    · simp [testBit_eq_false_of_lt ha (not_lt.1 hi)]
  · intro h i hi
    rw [mem_decC] at hi ⊢
    have := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.true_and] at this
    exact this

theorem decC_nonempty_iff {n a : ℕ} (ha : a < 2 ^ n) : (decC n a).Nonempty ↔ a ≠ 0 := by
  constructor
  · rintro ⟨i, hi⟩ rfl
    simp [mem_decC] at hi
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    have hin : i < n := by
      by_contra hn
      rw [testBit_eq_false_of_lt ha (not_lt.1 hn)] at hi
      exact absurd hi (by simp)
    exact ⟨⟨i, hin⟩, mem_decC.2 hi⟩

theorem decC_disjoint_iff {n a b : ℕ} (ha : a < 2 ^ n) :
    Disjoint (decC n a) (decC n b) ↔ a &&& b = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < n
    · cases ha' : a.testBit i
      · simp
      · cases hb' : b.testBit i
        · simp
        · exact absurd (mem_decC.2 hb' : (⟨i, hi⟩ : Fin n) ∈ decC n b)
            (Finset.disjoint_left.1 h (mem_decC.2 ha' : (⟨i, hi⟩ : Fin n) ∈ decC n a))
    · simp [testBit_eq_false_of_lt ha (not_lt.1 hi)]
  · intro h
    rw [Finset.disjoint_left]
    intro i hia hib
    rw [mem_decC] at hia hib
    have := congrArg (fun x => x.testBit i) h
    simp [Nat.testBit_and, hia, hib] at this

/-- The code of the complement. -/
theorem decC_compl {n a : ℕ} : (decC n a)ᶜ = decC n ((2 ^ n - 1) ^^^ a) := by
  ext i; simp [mem_decC, Nat.testBit_xor, i.2]

theorem decC_full (n : ℕ) : decC n (2 ^ n - 1) = univ := by
  ext i; simp [mem_decC, i.2]

theorem decC_eq_univ_iff {n a : ℕ} (ha : a < 2 ^ n) : decC n a = univ ↔ a = 2 ^ n - 1 := by
  rw [← decC_full n, decC_inj ha (by have := Nat.one_le_two_pow (n := n); omega)]

theorem decC_two_pow {n i : ℕ} (hi : i < n) : decC n (2 ^ i) = {⟨i, hi⟩} := by
  ext j
  simp only [mem_decC, Nat.testBit_two_pow, decide_eq_true_eq, mem_singleton, Fin.ext_iff]
  exact eq_comm

theorem full_lt (n : ℕ) : 2 ^ n - 1 < 2 ^ n := by
  have := Nat.one_le_two_pow (n := n); omega

theorem xor_full_lt {n a : ℕ} (ha : a < 2 ^ n) : (2 ^ n - 1) ^^^ a < 2 ^ n :=
  Nat.xor_lt_two_pow (full_lt n) ha

/-! ### Families of codes -/

theorem mem_decF {n : ℕ} {l : List ℕ} {A : Finset (Fin n)} :
    A ∈ decF n l ↔ ∃ c ∈ l, decC n c = A := by
  simp [decF]

theorem decC_mem_decF {n : ℕ} {l : List ℕ} {c : ℕ} (h : c ∈ l) : decC n c ∈ decF n l :=
  mem_decF.2 ⟨c, h, rfl⟩

@[simp] theorem decF_nil (n : ℕ) : decF n [] = ∅ := rfl

theorem decF_cons (n c : ℕ) (l : List ℕ) : decF n (c :: l) = insert (decC n c) (decF n l) := by
  simp [decF]

theorem decF_append (n : ℕ) (l₁ l₂ : List ℕ) : decF n (l₁ ++ l₂) = decF n l₁ ∪ decF n l₂ := by
  simp [decF]

theorem decF_union (n : ℕ) (l₁ l₂ : List ℕ) : decF n (l₁ ∪ l₂) = decF n l₁ ∪ decF n l₂ := by
  ext A; simp [mem_decF, List.mem_union_iff, or_and_right, exists_or]

theorem decC_mem_decF_iff {n : ℕ} {l : List ℕ} (hl : Valid n l) {c : ℕ} (hc : c < 2 ^ n) :
    decC n c ∈ decF n l ↔ c ∈ l := by
  refine ⟨fun h => ?_, decC_mem_decF⟩
  obtain ⟨d, hd, hdc⟩ := mem_decF.1 h
  rw [decC_inj (hl d hd) hc] at hdc
  exact hdc ▸ hd

theorem decF_eq_iff {n : ℕ} {l₁ l₂ : List ℕ} (h₁ : Valid n l₁) (h₂ : Valid n l₂) :
    decF n l₁ = decF n l₂ ↔ (∀ c ∈ l₁, c ∈ l₂) ∧ ∀ c ∈ l₂, c ∈ l₁ := by
  constructor
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · rw [← decC_mem_decF_iff h₂ (h₁ c hc), ← h]; exact decC_mem_decF hc
    · rw [← decC_mem_decF_iff h₁ (h₂ c hc), h]; exact decC_mem_decF hc
  · rintro ⟨h, h'⟩
    ext A
    simp only [mem_decF]
    exact ⟨fun ⟨c, hc, e⟩ => ⟨c, h c hc, e⟩, fun ⟨c, hc, e⟩ => ⟨c, h' c hc, e⟩⟩

theorem card_decF {n : ℕ} {l : List ℕ} (hl : Valid n l) (hnd : l.Nodup) : #(decF n l) = l.length := by
  rw [decF, List.toFinset_card_of_nodup, List.length_map]
  exact hnd.map_on fun a ha b hb e => (decC_inj (hl a ha) (hl b hb)).1 e

/-! ### Roots and merges on codes -/

/-- The roots of a family of codes: the codes not strictly contained in another one. -/
def rootsL (F : List ℕ) : List ℕ := F.filter fun c => F.all fun d => !(c &&& d == c) || d == c

theorem mem_rootsL {F : List ℕ} {c : ℕ} :
    c ∈ rootsL F ↔ c ∈ F ∧ ∀ d ∈ F, c &&& d = c → d = c := by
  simp only [rootsL, List.mem_filter, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, beq_iff_eq]
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, fun d hd hcd => (h d hd).resolve_left (not_not.2 hcd)⟩
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun d hd => ?_⟩
    by_cases hcd : c &&& d = c
    · exact Or.inr (h d hd hcd)
    · exact Or.inl hcd

theorem valid_rootsL {n : ℕ} {F : List ℕ} (hv : Valid n F) : Valid n (rootsL F) :=
  fun c hc => hv c (mem_rootsL.1 hc).1

theorem nodup_rootsL {F : List ℕ} (hnd : F.Nodup) : (rootsL F).Nodup := hnd.filter _

theorem decF_rootsL {n : ℕ} {F : List ℕ} (hv : Valid n F) :
    decF n (rootsL F) = roots (decF n F) := by
  ext A
  simp only [roots, mem_filter]
  constructor
  · intro hA
    obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
    rw [mem_rootsL] at hc
    refine ⟨decC_mem_decF hc.1, fun B hB hsub => ?_⟩
    obtain ⟨d, hd, rfl⟩ := mem_decF.1 hB
    rw [decC_subset_iff (hv c hc.1)] at hsub
    rw [hc.2 d hd hsub]
  · rintro ⟨hA, h⟩
    obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
    refine decC_mem_decF (mem_rootsL.2 ⟨hc, fun d hd hcd => ?_⟩)
    have := h (decC n d) (decC_mem_decF hd) ((decC_subset_iff (hv c hc)).2 hcd)
    exact (decC_inj (hv d hd) (hv c hc)).1 this

theorem card_roots_decF {n : ℕ} {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup) :
    #(roots (decF n F)) = (rootsL F).length := by
  rw [← decF_rootsL hv, card_decF (valid_rootsL hv) (nodup_rootsL hnd)]

/-- The unordered pairs of distinct entries of a list. -/
def pairsL : List ℕ → List (ℕ × ℕ)
  | [] => []
  | a :: l => l.map (fun b => (a, b)) ++ pairsL l

theorem length_pairsL : ∀ l : List ℕ, (pairsL l).length = l.length.choose 2
  | [] => rfl
  | a :: l => by
    simp only [pairsL, List.length_append, List.length_map, length_pairsL l, List.length_cons,
      Nat.choose_succ_succ, Nat.choose_one_right]

theorem mem_pairsL {l : List ℕ} {p : ℕ × ℕ} (h : p ∈ pairsL l) : p.1 ∈ l ∧ p.2 ∈ l := by
  induction l with
  | nil => simp [pairsL] at h
  | cons a l ih =>
    simp only [pairsL, List.mem_append, List.mem_map] at h
    rcases h with ⟨b, hb, rfl⟩ | h
    · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ hb⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, List.mem_cons_of_mem _ (ih h).2⟩

theorem ne_of_mem_pairsL {l : List ℕ} (hnd : l.Nodup) {p : ℕ × ℕ} (h : p ∈ pairsL l) :
    p.1 ≠ p.2 := by
  induction l with
  | nil => simp [pairsL] at h
  | cons a l ih =>
    simp only [pairsL, List.mem_append, List.mem_map] at h
    rw [List.nodup_cons] at hnd
    rcases h with ⟨b, hb, rfl⟩ | h
    · show a ≠ b
      rintro rfl; exact hnd.1 hb
    · exact ih hnd.2 h

theorem mem_pairsL_of_ne {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    (a, b) ∈ pairsL l ∨ (b, a) ∈ pairsL l := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    simp only [pairsL, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.1 ha with h1 | ha'
    · subst h1
      rcases List.mem_cons.1 hb with h2 | hb'
      · exact absurd h2.symm hab
      · exact Or.inl (Or.inl ⟨b, hb', rfl, rfl⟩)
    · rcases List.mem_cons.1 hb with h2 | hb'
      · subst h2
        exact Or.inr (Or.inl ⟨a, ha', rfl, rfl⟩)
      · rcases ih ha' hb' with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

theorem decF_merge (n : ℕ) (F : List ℕ) (a b : ℕ) :
    decF n ((a ||| b) :: F) = insert (decC n a ∪ decC n b) (decF n F) := by
  rw [decF_cons, decC_or]

theorem nodup_of_card_toFinset {α : Type*} [DecidableEq α] {l : List α}
    (h : #l.toFinset = l.length) : l.Nodup := by
  rw [List.card_toFinset] at h
  exact List.dedup_eq_self.1 ((List.dedup_sublist l).eq_of_length h)

theorem roots_pair_of_mem_pairsL {n : ℕ} {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup)
    {p : ℕ × ℕ} (hp : p ∈ pairsL (rootsL F)) :
    decC n p.1 ∈ roots (decF n F) ∧ decC n p.2 ∈ roots (decF n F) ∧ decC n p.1 ≠ decC n p.2 := by
  have h12 := mem_pairsL hp
  have hne := ne_of_mem_pairsL (nodup_rootsL hnd) hp
  rw [← decF_rootsL hv]
  refine ⟨decC_mem_decF h12.1, decC_mem_decF h12.2, fun h => hne ?_⟩
  exact (decC_inj (valid_rootsL hv _ h12.1) (valid_rootsL hv _ h12.2)).1 h

theorem merges_decF {n : ℕ} {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup) :
    merges (decF n F) = ((pairsL (rootsL F)).map fun p => decF n ((p.1 ||| p.2) :: F)).toFinset := by
  ext F'
  simp only [merges, mem_image, mem_filter, mem_product, List.mem_toFinset, List.mem_map,
    Prod.exists]
  constructor
  · rintro ⟨A, B, ⟨⟨hA, hB⟩, hAB⟩, rfl⟩
    rw [← decF_rootsL hv] at hA hB
    obtain ⟨a, ha, rfl⟩ := mem_decF.1 hA
    obtain ⟨b, hb, rfl⟩ := mem_decF.1 hB
    have hab : a ≠ b := fun h => hAB (h ▸ rfl)
    rcases mem_pairsL_of_ne ha hb hab with h | h
    · exact ⟨a, b, h, decF_merge n F a b⟩
    · exact ⟨b, a, h, by rw [decF_merge, union_comm]⟩
  · rintro ⟨a, b, hp, rfl⟩
    obtain ⟨ha, hb, hne⟩ := roots_pair_of_mem_pairsL hv hnd hp
    exact ⟨decC n a, decC n b, ⟨⟨ha, hb⟩, hne⟩, (decF_merge n F a b).symm⟩

theorem sum_merges_decF {n : ℕ} {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup)
    (hF : IsForest (decF n F)) {M : Type*} [AddCommMonoid M] (g : Finset (Finset (Fin n)) → M) :
    ∑ F' ∈ merges (decF n F), g F' =
      ((pairsL (rootsL F)).map fun p => g (decF n ((p.1 ||| p.2) :: F))).sum := by
  have hcard := hF.card_merges
  rw [merges_decF hv hnd] at hcard ⊢
  have hnd' : ((pairsL (rootsL F)).map fun p => decF n ((p.1 ||| p.2) :: F)).Nodup := by
    apply nodup_of_card_toFinset
    rw [List.length_map, length_pairsL, ← card_roots_decF hv hnd, ← hcard]
  rw [List.sum_toFinset _ hnd', List.map_map]
  rfl

theorem valid_merge {n : ℕ} {F : List ℕ} (hv : Valid n F) {p : ℕ × ℕ}
    (hp : p ∈ pairsL (rootsL F)) : Valid n ((p.1 ||| p.2) :: F) := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · have h12 := mem_pairsL hp
    exact Nat.or_lt_two_pow (valid_rootsL hv _ h12.1) (valid_rootsL hv _ h12.2)
  · exact hv c hc

theorem nodup_merge {n : ℕ} {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup)
    (hF : IsForest (decF n F)) {p : ℕ × ℕ} (hp : p ∈ pairsL (rootsL F)) :
    ((p.1 ||| p.2) :: F).Nodup := by
  refine List.nodup_cons.2 ⟨fun h => ?_, hnd⟩
  obtain ⟨ha, hb, hne⟩ := roots_pair_of_mem_pairsL hv hnd hp
  exact union_not_mem_of_mem_roots ha hb hne (decC_or n p.1 p.2 ▸ decC_mem_decF h)

theorem isForest_merge {n : ℕ} {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup)
    (hF : IsForest (decF n F)) {p : ℕ × ℕ} (hp : p ∈ pairsL (rootsL F)) :
    IsForest (decF n ((p.1 ||| p.2) :: F)) := by
  obtain ⟨ha, hb, hne⟩ := roots_pair_of_mem_pairsL hv hnd hp
  rw [decF_merge]
  exact hF.isForest_merge ha hb

/-! ### List sums -/

theorem sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (l : List α) (f : α → List β)
    (g : β → M) : ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-! ### The jump chain on codes -/

/-- The paths of length `j` of the jump chain from the forest with codes `F`, with their
probabilities. -/
def jumpL : ℕ → List ℕ → List (ℚ × List ℕ)
  | 0, F => [(1, F)]
  | j + 1, F => if (rootsL F).length ≤ 1 then [(1, F)] else
      (pairsL (rootsL F)).flatMap fun p => (jumpL j ((p.1 ||| p.2) :: F)).map fun q =>
        ((((rootsL F).length.choose 2 : ℕ) : ℚ)⁻¹ * q.1, q.2)

theorem jumpMatrix_pow_decF {n : ℕ} : ∀ (j : ℕ) (F : List ℕ), Valid n F → F.Nodup →
    IsForest (decF n F) → ∀ G : Finset (Finset (Fin n)),
    (jumpMatrix ^ j) (decF n F) G = ((jumpL j F).map fun q => if decF n q.2 = G then (q.1 : ℝ) else 0).sum
  | 0, F, _, _, _, G => by
    rcases eq_or_ne (decF n F) G with h | h
    · subst h; simp [jumpL]
    · simp [jumpL, h]
  | j + 1, F, hv, hnd, hF, G => by
    by_cases hk : (rootsL F).length ≤ 1
    · rw [jumpMatrix_pow_of_card_roots_le_one (by rw [card_roots_decF hv hnd]; exact hk)]
      rcases eq_or_ne (decF n F) G with h | h
      · subst h; simp [jumpL, hk]
      · simp [jumpL, hk, h, Ne.symm h]
    · rw [jumpMatrix_pow_succ_apply hF (by rw [card_roots_decF hv hnd]; omega),
        sum_merges_decF hv hnd hF, card_roots_decF hv hnd]
      rw [jumpL, ite_eq_right hk, sum_map_flatMap, ← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro p hp
      rw [jumpMatrix_pow_decF j _ (valid_merge hv hp) (nodup_merge hv hnd hF hp)
        (isForest_merge hv hnd hF hp) G, ← List.sum_map_mul_left, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q _
      simp only [Function.comp_apply]
      split_ifs <;> push_cast <;> ring

theorem sum_range_eq_list {M : Type*} [AddCommMonoid M] (k : ℕ) (f : ℕ → M) :
    ∑ j ∈ range k, f j = ((List.range k).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

theorem sum_mul_sum_list {α β : Type*} (A : List α) (B : List β) (f : α → ℝ) (g : β → ℝ) :
    (A.map f).sum * (B.map g).sum = (A.map fun a => (B.map fun b => f a * g b).sum).sum := by
  rw [← List.sum_map_mul_right]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [← List.sum_map_mul_left]

/-! ### Forest checks -/

/-- A Boolean test that a family of codes is a forest. -/
def isForestB (F : List ℕ) : Bool :=
  F.all (· != 0) && F.all fun c => F.all fun d => (c &&& d == c) || (c &&& d == d) || (c &&& d == 0)

theorem isForest_of_isForestB {n : ℕ} {F : List ℕ} (hv : Valid n F) (h : isForestB F = true) :
    IsForest (decF n F) := by
  simp only [isForestB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨fun A hA => ?_, fun A hA B hB => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
    exact (decC_nonempty_iff (hv c hc)).2 (h.1 c hc)
  · obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
    obtain ⟨d, hd, rfl⟩ := mem_decF.1 hB
    rcases h.2 c hc d hd with (h1 | h2) | h3
    · exact Or.inl ((decC_subset_iff (hv c hc)).2 h1)
    · exact Or.inr (Or.inl ((decC_subset_iff (hv d hd)).2 (by rw [Nat.and_comm]; exact h2)))
    · exact Or.inr (Or.inr ((decC_disjoint_iff (hv c hc)).2 h3))

/-- The checks made on a family of codes entering a population: valid codes, no repetition, and a
forest. -/
def checkF (n : ℕ) (F : List ℕ) : Bool := decide (Valid n F) && decide F.Nodup && isForestB F

theorem of_checkF {n : ℕ} {F : List ℕ} (h : checkF n F = true) :
    Valid n F ∧ F.Nodup ∧ IsForest (decF n F) := by
  simp only [checkF, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, isForest_of_isForestB h.1.1 h.2⟩

/-- The code list of `unroot`. -/
def unrootL (m : ℕ) (F : List ℕ) : List ℕ :=
  (F.filter (· != 2 ^ m - 1)) ++ (F.filter (· != 2 ^ m - 1)).map ((2 ^ m - 1) ^^^ ·)

theorem decF_unrootL {m : ℕ} {F : List ℕ} (hv : Valid m F) :
    decF m (unrootL m F) = unroot (decF m F) := by
  have h1 : decF m (F.filter (· != 2 ^ m - 1)) = (decF m F).erase univ := by
    ext A
    simp only [mem_decF, List.mem_filter, bne_iff_ne, ne_eq, mem_erase]
    constructor
    · rintro ⟨c, ⟨hc, hne⟩, rfl⟩
      exact ⟨fun h => hne ((decC_eq_univ_iff (hv c hc)).1 h), c, hc, rfl⟩
    · rintro ⟨hne, c, hc, rfl⟩
      exact ⟨c, ⟨hc, fun h => hne ((decC_eq_univ_iff (hv c hc)).2 h)⟩, rfl⟩
  have h2 : ∀ l : List ℕ, decF m (l.map ((2 ^ m - 1) ^^^ ·)) = (decF m l).image compl := by
    intro l
    ext A
    simp only [mem_decF, List.mem_map, mem_image]
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨decC m c, ⟨c, hc, rfl⟩, decC_compl⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨_, ⟨c, hc, rfl⟩, decC_compl.symm⟩
  rw [unrootL, decF_append, h1, h2, h1, unroot]

theorem valid_unrootL {m : ℕ} {F : List ℕ} (hv : Valid m F) : Valid m (unrootL m F) := by
  intro c hc
  simp only [unrootL, List.mem_append, List.mem_filter, List.mem_map] at hc
  rcases hc with ⟨hc, -⟩ | ⟨d, ⟨hd, -⟩, rfl⟩
  · exact hv c hc
  · exact xor_full_lt (hv d hd)

/-- Whether the codes in `F` cover all `m` lineages. -/
def coversB (m : ℕ) (F : List ℕ) : Bool := F.foldr (· ||| ·) 0 == 2 ^ m - 1

theorem lineages_decF (m : ℕ) (F : List ℕ) :
    lineages (decF m F) = decC m (F.foldr (· ||| ·) 0) := by
  induction F with
  | nil => ext i; simp [lineages, mem_decC]
  | cons c F ih =>
    rw [decF_cons, lineages, sup_insert, ← lineages, ih, List.foldr_cons, decC_or]
    rfl

theorem lineages_eq_univ_of_coversB {m : ℕ} {F : List ℕ} (h : coversB m F = true) :
    lineages (decF m F) = univ := by
  rw [lineages_decF]
  simp only [coversB, beq_iff_eq] at h
  rw [h, decC_full]

/-! ### The forest sampled at a cluster -/

/-- The codes of the singletons of the lineages (coded on `m` bits) sampled from the taxa in the
cluster with code `a`. -/
def sampledL (m n : ℕ) (s : Fin m → Fin n) (a : ℕ) : List ℕ :=
  ((List.finRange m).filter fun l => a.testBit (s l)).map fun l : Fin m => 2 ^ l.val

theorem mem_sampledL {m n : ℕ} {s : Fin m → Fin n} {a c : ℕ} :
    c ∈ sampledL m n s a ↔ ∃ l : Fin m, a.testBit (s l) = true ∧ 2 ^ (l : ℕ) = c := by
  unfold sampledL
  rw [List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, (List.mem_filter.1 hl).2, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, List.mem_filter.2 ⟨List.mem_finRange l, hl⟩, rfl⟩

theorem decF_sampledL {m n : ℕ} (s : Fin m → Fin n) (a : ℕ) :
    decF m (sampledL m n s a) = sampledForest s (decC n a) := by
  ext A
  rw [mem_decF, sampledForest, mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨l, hl, rfl⟩ := mem_sampledL.1 hc
    exact ⟨l, mem_filter.2 ⟨mem_univ _, mem_decC.2 hl⟩, (decC_two_pow l.2).symm⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨_, mem_sampledL.2 ⟨l, mem_decC.1 (mem_filter.1 hl).2, rfl⟩, decC_two_pow l.2⟩

/-! ### Lists of results that may fail -/

/-- `flatMap` for a function that may fail. -/
def flatMapO {α β : Type*} (f : α → Option (List β)) : List α → Option (List β)
  | [] => some []
  | a :: l => match f a, flatMapO f l with
    | some x, some y => some (x ++ y)
    | _, _ => none

theorem sum_flatMapO {α β : Type*} {f : α → Option (List β)} {l : List α} {M : List β}
    (h : flatMapO f l = some M) (w : β → ℝ) (v : α → ℝ)
    (hv : ∀ a ∈ l, ∀ x, f a = some x → (x.map w).sum = v a) :
    (M.map w).sum = (l.map v).sum := by
  induction l generalizing M with
  | nil => simp only [flatMapO, Option.some.injEq] at h; subst h; simp
  | cons a l ih =>
    simp only [flatMapO] at h
    split at h
    · rename_i x y hx hy
      simp only [Option.some.injEq] at h
      subst h
      rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        hv a (List.mem_cons_self ..) x hx,
        ih hy fun b hb => hv b (List.mem_cons_of_mem _ hb)]
    · simp at h

theorem forall_mem_flatMapO {α β : Type*} {f : α → Option (List β)} {l : List α} {M : List β}
    (h : flatMapO f l = some M) (p : β → Prop)
    (hp : ∀ a ∈ l, ∀ x, f a = some x → ∀ b ∈ x, p b) : ∀ b ∈ M, p b := by
  induction l generalizing M with
  | nil => simp only [flatMapO, Option.some.injEq] at h; subst h; simp
  | cons a l ih =>
    simp only [flatMapO] at h
    split at h
    · rename_i x y hx hy
      simp only [Option.some.injEq] at h
      subst h
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact hp a (List.mem_cons_self ..) x hx b hb
      · exact ih hy (fun a ha => hp a (List.mem_cons_of_mem _ ha)) b hb
    · simp at h

end ADR11.Computation
