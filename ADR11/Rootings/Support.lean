module

public import ADR11.Computation.Codes
public import ADR11.Model.History
public import ADR11.SmallTrees

/-!
# Binary hierarchies on few taxa, and the support of the gene tree distributions

With one lineage per taxon, a rooted gene tree with positive probability is a binary hierarchy on
the taxa (`model_rootedDist_support`). This file enumerates the binary hierarchies on `Fin n` by a
program that the kernel can run, and proves the enumeration complete; this gives the support of
the rooted and unrooted gene tree distributions on four and five taxa, for every species tree.

* `root_binEnum k b`: code lists (see `ADR11.Computation.decC`) of the binary hierarchies on the
  cluster with code `b`: the root `b`, then a binary hierarchy on each side of a split of `b`.
* `root_binEnum_complete`: every binary hierarchy on the cluster with code `b` is (the family of
  clusters with the codes of) one of them.
* `root_rootedDist_support`: a rooted gene tree with positive probability is one of them.
* `root_unrootedDist_eq_sum`: the unrooted gene tree distribution as a finite sum over a list of
  code lists containing all binary hierarchies, each counted once.
* `root_unrootedDist_eq_zero_four`, `root_unrootedDist_eq_zero_five`: on four (five) taxa, only
  the three quartet trees (the fifteen trees `T5 i`) have positive probability.
* `root_table`, `root_u_eq_sum`: Tables 4 and 5 of the paper (`ADR11.AppendixA`), for a table of
  rooted trees given by code lists and checked by the Boolean test `root_tableB`.
* `root_binHierB`, `root_isBinHier_of_binHierB`: a Boolean test that a code list is a binary
  hierarchy; `root_famMask`: the bitmask of a family of codes, to compare families quickly.
-/
@[expose] public section

namespace ADR11

open Finset _root_.ADR11.Computation

/-! ### Codes -/

/-- Every cluster on `Fin n` has a code. -/
theorem root_exists_code {n : ℕ} (A : Finset (Fin n)) : ∃ c, c < 2 ^ n ∧ decC n c = A := by
  induction A using Finset.induction_on with
  | empty => exact ⟨0, Nat.two_pow_pos n, by ext i; simp [mem_decC]⟩
  | insert a A _ ih =>
    obtain ⟨c, hc, rfl⟩ := ih
    refine ⟨2 ^ (a : ℕ) ||| c, Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) a.2) hc, ?_⟩
    rw [decC_or, decC_two_pow a.2, Finset.insert_eq]

theorem root_xor_eq {c d : ℕ} (h : c &&& d = 0) : (c ||| d) ^^^ c = d := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun x => x.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at hi
  simp only [Nat.testBit_xor, Nat.testBit_or]
  cases hc : c.testBit i <;> cases hd : d.testBit i <;> simp_all

/-- Whether two code lists have the same elements. -/
def root_sameSet (a b : List ℕ) : Bool := a.all (· ∈ b) && b.all (· ∈ a)

theorem root_decF_eq_iff_sameSet {n : ℕ} {a b : List ℕ} (ha : Valid n a) (hb : Valid n b) :
    decF n a = decF n b ↔ root_sameSet a b = true := by
  rw [decF_eq_iff ha hb]
  simp [root_sameSet, List.all_eq_true]

/-- The bitmask of a list of codes: bit `c` is set for each code `c` of the list. -/
def root_famMask (l : List ℕ) : ℕ := l.foldr (fun c acc => 2 ^ c ||| acc) 0

theorem root_testBit_famMask (l : List ℕ) (c : ℕ) :
    (root_famMask l).testBit c = decide (c ∈ l) := by
  induction l with
  | nil => simp [root_famMask]
  | cons a l ih =>
    simp only [root_famMask, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_or, ih, Nat.testBit_two_pow]
    by_cases h : a = c
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem root_famMask_eq_iff_sameSet (a b : List ℕ) :
    root_famMask a = root_famMask b ↔ root_sameSet a b = true := by
  simp only [root_sameSet, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    have hm : ∀ c, c ∈ a ↔ c ∈ b := fun c => by
      have := congrArg (fun x => x.testBit c) h
      simpa [root_testBit_famMask] using this
    exact ⟨fun c hc => (hm c).1 hc, fun c hc => (hm c).2 hc⟩
  · rintro ⟨hab, hba⟩
    apply Nat.eq_of_testBit_eq
    intro c
    rw [root_testBit_famMask, root_testBit_famMask]
    exact decide_eq_decide.2 ⟨hab c, hba c⟩

theorem root_decF_eq_iff_famMask {n : ℕ} {a b : List ℕ} (ha : Valid n a) (hb : Valid n b) :
    decF n a = decF n b ↔ root_famMask a = root_famMask b := by
  rw [root_decF_eq_iff_sameSet ha hb, root_famMask_eq_iff_sameSet]

/-! ### The enumeration -/

/-- The codes `c` of the nonempty proper subsets of the cluster with code `b` with
`c < b ^^^ c`: one side of each split of `b` into two nonempty parts. -/
def root_splits (b : ℕ) : List ℕ :=
  (List.range b).filter fun c => c &&& b == c && c != 0 && decide (c < b ^^^ c)

/-- The code lists of the binary hierarchies on the cluster with code `b` (with fuel `k`): the
root `b`, followed by binary hierarchies on both sides of a split of `b`. -/
def root_binEnum : ℕ → ℕ → List (List ℕ)
  | 0, b => [[b]]
  | k + 1, b => if root_splits b = [] then [[b]] else
      (root_splits b).flatMap fun c => (root_binEnum k c).flatMap fun h₁ =>
        (root_binEnum k (b ^^^ c)).map fun h₂ => b :: (h₁ ++ h₂)

/-- `F` is a binary hierarchy on the cluster `B`. -/
def root_BinOn {n : ℕ} (F : Finset (Finset (Fin n))) (B : Finset (Fin n)) : Prop :=
  B ∈ F ∧ (∀ A ∈ F, A ⊆ B) ∧ (∀ A ∈ F, A.Nonempty) ∧
    (∀ A ∈ F, ∀ A' ∈ F, A ⊆ A' ∨ A' ⊆ A ∨ Disjoint A A') ∧
    ∀ A ∈ F, 2 ≤ #A → ∃ C ∈ F, ∃ D ∈ F, Disjoint C D ∧ C ∪ D = A

theorem root_BinOn.eq_singleton {n : ℕ} {F : Finset (Finset (Fin n))} {B : Finset (Fin n)}
    (hF : root_BinOn F B) (hB : #B ≤ 1) : F = {B} := by
  obtain ⟨hBF, hsub, hne, -, -⟩ := hF
  ext A
  rw [mem_singleton]
  constructor
  · intro hA
    have := (hne A hA).card_pos
    exact eq_of_subset_of_card_le (hsub A hA) (by omega)
  · rintro rfl
    exact hBF

theorem root_BinOn.restrict {n : ℕ} {F : Finset (Finset (Fin n))} {B C : Finset (Fin n)}
    (hF : root_BinOn F B) (hC : C ∈ F) : root_BinOn (F.filter (· ⊆ C)) C := by
  obtain ⟨-, -, hne, hlam, hbin⟩ := hF
  refine ⟨mem_filter.2 ⟨hC, subset_rfl⟩, fun A hA => (mem_filter.1 hA).2,
    fun A hA => hne A (mem_filter.1 hA).1,
    fun A hA A' hA' => hlam A (mem_filter.1 hA).1 A' (mem_filter.1 hA').1, ?_⟩
  intro A hA h2
  obtain ⟨hA, hAC⟩ := mem_filter.1 hA
  obtain ⟨D, hD, E, hE, hDE, rfl⟩ := hbin A hA h2
  exact ⟨D, mem_filter.2 ⟨hD, subset_union_left.trans hAC⟩, E,
    mem_filter.2 ⟨hE, subset_union_right.trans hAC⟩, hDE, rfl⟩

/-- A binary hierarchy on `B = C ∪ D` (a split of `B` into clusters) consists of `B` and the
clusters below `C` and below `D`. -/
theorem root_BinOn.decomp {n : ℕ} {F : Finset (Finset (Fin n))} {B C D : Finset (Fin n)}
    (hF : root_BinOn F B) (hC : C ∈ F) (hD : D ∈ F) (hCD : Disjoint C D) (hB : C ∪ D = B) :
    F = insert B (F.filter (· ⊆ C) ∪ F.filter (· ⊆ D)) := by
  obtain ⟨hBF, hsub, hne, hlam, -⟩ := hF
  have hside : ∀ A ∈ F, ∀ {E E' : Finset (Fin n)}, E ∪ E' = B → Disjoint A E → A ⊆ E' := by
    intro A hA E E' hEE' hAE x hx
    have hxB := hsub A hA hx
    rw [← hEE'] at hxB
    rcases mem_union.1 hxB with hxE | hxE'
    · exact absurd hxE (disjoint_left.1 hAE hx)
    · exact hxE'
  ext A
  simp only [mem_insert, mem_union, mem_filter]
  constructor
  · intro hA
    by_cases hAB : A = B
    · exact Or.inl hAB
    right
    rcases hlam A hA C hC with h | h | h
    · exact Or.inl ⟨hA, h⟩
    · rcases hlam A hA D hD with h' | h' | h'
      · exfalso
        obtain ⟨x, hx⟩ := hne C hC
        exact disjoint_left.1 hCD hx (h' (h hx))
      · exact absurd (Subset.antisymm (hsub A hA) (hB ▸ union_subset h h')) hAB
      · exact Or.inl ⟨hA, hside A hA (by rw [union_comm, hB]) h'⟩
    · exact Or.inr ⟨hA, hside A hA hB h⟩
  · rintro (rfl | ⟨hA, -⟩ | ⟨hA, -⟩)
    · exact hBF
    · exact hA
    · exact hA

theorem root_splits_eq_nil {n b : ℕ} (hb : b < 2 ^ n) (h1 : #(decC n b) ≤ 1) :
    root_splits b = [] := by
  rw [root_splits, List.filter_eq_nil_iff]
  intro c hc
  rw [List.mem_range] at hc
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, not_and]
  rintro ⟨hcb, hc0⟩ -
  have hc' : c < 2 ^ n := hc.trans hb
  have hsub : decC n c ⊆ decC n b := (decC_subset_iff hc').2 hcb
  have hne := ((decC_nonempty_iff hc').2 hc0).card_pos
  have h := eq_of_subset_of_card_le hsub (by omega)
  rw [decC_inj hc' hb] at h
  omega

theorem root_mem_splits {b c : ℕ} (hcb : c < b) (hsub : c &&& b = c) (hc0 : c ≠ 0)
    (hlt : c < b ^^^ c) : c ∈ root_splits b := by
  simp [root_splits, hcb, hsub, hc0, hlt]

/-- **Completeness of the enumeration.** Every binary hierarchy on the cluster with code `b` is
the family of clusters of one of the code lists `root_binEnum k b`, when `k + 1` is at least the
number of elements of the cluster. -/
theorem root_binEnum_complete {n : ℕ} (k : ℕ) : ∀ b : ℕ, b < 2 ^ n → #(decC n b) ≤ k + 1 →
    ∀ F : Finset (Finset (Fin n)), root_BinOn F (decC n b) →
      ∃ l ∈ root_binEnum k b, decF n l = F := by
  induction k with
  | zero =>
    intro b hb hcard F hF
    refine ⟨[b], by simp [root_binEnum], ?_⟩
    rw [hF.eq_singleton hcard]
    simp [decF]
  | succ k ih =>
    intro b hb hcard F hF
    by_cases h1 : #(decC n b) ≤ 1
    · refine ⟨[b], ?_, ?_⟩
      · simp [root_binEnum, root_splits_eq_nil hb h1]
      · rw [hF.eq_singleton h1]
        simp [decF]
    have hF' := hF
    obtain ⟨hBF, hsub, hne, hlam, hbin⟩ := hF'
    obtain ⟨C, hC, D, hD, hCD, hCDB⟩ := hbin _ hBF (by omega)
    obtain ⟨c, hc, rfl⟩ := root_exists_code C
    obtain ⟨d, hd, rfl⟩ := root_exists_code D
    have hcard' := card_union_of_disjoint hCD
    rw [hCDB] at hcard'
    have hCne := hne _ hC
    have hDne := hne _ hD
    have hCc := hCne.card_pos
    have hDc := hDne.card_pos
    obtain ⟨l₁, hl₁, e₁⟩ := ih c hc (by omega) _ (hF.restrict hC)
    obtain ⟨l₂, hl₂, e₂⟩ := ih d hd (by omega) _ (hF.restrict hD)
    have hdec := hF.decomp hC hD hCD hCDB
    have hand : c &&& d = 0 := (decC_disjoint_iff hc).1 hCD
    have hor : c ||| d = b := (decC_inj (Nat.or_lt_two_pow hc hd) hb).1 (by rw [decC_or, hCDB])
    have hc0 : c ≠ 0 := (decC_nonempty_iff hc).1 hCne
    have hd0 : d ≠ 0 := (decC_nonempty_iff hd).1 hDne
    have hxc : b ^^^ c = d := hor ▸ root_xor_eq hand
    have hxd : b ^^^ d = c := by
      rw [← hor, Nat.lor_comm]
      exact root_xor_eq (by rw [Nat.land_comm]; exact hand)
    have hcb : c &&& b = c := (decC_subset_iff hc).1 (hCDB ▸ subset_union_left)
    have hdb : d &&& b = d := (decC_subset_iff hd).1 (hCDB ▸ subset_union_right)
    have hcltb : c < b := by
      refine lt_of_le_of_ne (hcb ▸ Nat.and_le_right) fun h => ?_
      subst h
      have : decC n d ⊆ decC n c := hCDB ▸ subset_union_right
      obtain ⟨x, hx⟩ := hDne
      exact disjoint_left.1 hCD (this hx) hx
    have hdltb : d < b := by
      refine lt_of_le_of_ne (hdb ▸ Nat.and_le_right) fun h => ?_
      subst h
      have : decC n c ⊆ decC n d := hCDB ▸ subset_union_left
      obtain ⟨x, hx⟩ := hCne
      exact disjoint_left.1 hCD hx (this hx)
    have hcd : c ≠ d := by
      rintro rfl
      rw [Nat.and_self] at hand
      exact hc0 hand
    rcases lt_or_gt_of_ne hcd with hlt | hlt
    · have hmem := root_mem_splits hcltb hcb hc0 (hxc ▸ hlt)
      refine ⟨b :: (l₁ ++ l₂), ?_, ?_⟩
      · rw [root_binEnum, ite_eq_right (List.ne_nil_of_mem hmem)]
        exact List.mem_flatMap.2 ⟨c, hmem, List.mem_flatMap.2 ⟨l₁, hl₁,
          List.mem_map.2 ⟨l₂, hxc ▸ hl₂, rfl⟩⟩⟩
      · rw [decF_cons, decF_append, e₁, e₂, ← hdec]
    · have hmem := root_mem_splits hdltb hdb hd0 (hxd ▸ hlt)
      refine ⟨b :: (l₂ ++ l₁), ?_, ?_⟩
      · rw [root_binEnum, ite_eq_right (List.ne_nil_of_mem hmem)]
        exact List.mem_flatMap.2 ⟨d, hmem, List.mem_flatMap.2 ⟨l₂, hl₂,
          List.mem_map.2 ⟨l₁, hxd ▸ hl₁, rfl⟩⟩⟩
      · rw [decF_cons, decF_append, e₁, e₂, union_comm, ← hdec]

/-! ### The support of the rooted gene tree distribution -/

theorem root_binOn_univ_of_rootedDist {n : ℕ} [Nonempty (Fin n)] (σ : SpeciesTree (Fin n))
    {G : Finset (Finset (Fin n))} (hG : σ.rootedDist id G ≠ 0) : root_BinOn G univ := by
  obtain ⟨⟨hu, -, hne, hlam⟩, hbin⟩ := model_rootedDist_support σ id hG
  exact ⟨hu, fun A _ => subset_univ A, hne, hlam, hbin⟩

theorem root_binOn_univ_of_isBinary {n : ℕ} (σ : SpeciesTree (Fin n)) (hσ : σ.IsBinary) :
    root_BinOn σ.clusters univ :=
  ⟨σ.univ_mem, fun A _ => subset_univ A, σ.nonempty_of_mem, σ.laminar, hσ⟩

theorem root_binEnum_complete_univ {n : ℕ} {G : Finset (Finset (Fin n))}
    (hG : root_BinOn G univ) : ∃ l ∈ root_binEnum (n - 1) (2 ^ n - 1), decF n l = G := by
  apply root_binEnum_complete (n - 1) (2 ^ n - 1) (full_lt n)
  · rw [decC_full, card_univ, Fintype.card_fin]
    omega
  · rw [decC_full]
    exact hG

/-- A rooted gene tree with positive probability (one lineage per taxon) is one of the trees
`root_binEnum (n - 1) (2 ^ n - 1)`. -/
theorem root_rootedDist_support {n : ℕ} [Nonempty (Fin n)] (σ : SpeciesTree (Fin n))
    {G : Finset (Finset (Fin n))} (hG : σ.rootedDist id G ≠ 0) :
    ∃ l ∈ root_binEnum (n - 1) (2 ^ n - 1), decF n l = G :=
  root_binEnum_complete_univ (root_binOn_univ_of_rootedDist σ hG)

/-- The unrooted gene tree distribution as a finite sum, over a list `Bs` of code lists that
contains every binary hierarchy exactly once. -/
theorem root_unrootedDist_eq_sum {n : ℕ} [Nonempty (Fin n)] (σ : SpeciesTree (Fin n))
    (Bs : List (List ℕ))
    (hcomp : ∀ l ∈ root_binEnum (n - 1) (2 ^ n - 1), ∃ l' ∈ Bs, decF n l' = decF n l)
    (hnd : (Bs.map (decF n)).Nodup) (T : Finset (Finset (Fin n))) :
    σ.unrootedDist id T =
      (Bs.map fun l => if unroot (decF n l) = T then σ.rootedDist id (decF n l) else 0).sum := by
  rw [SpeciesTree.unrootedDist]
  rw [← Finset.sum_subset (subset_univ (Bs.map (decF n)).toFinset)]
  · rw [List.sum_toFinset _ hnd, List.map_map]
    rfl
  · intro G _ hG
    by_contra hne
    have hr : σ.rootedDist id G ≠ 0 := by
      intro h
      apply hne
      simp [h]
    obtain ⟨l, hl, rfl⟩ := root_rootedDist_support σ hr
    obtain ⟨l', hl', e⟩ := hcomp l hl
    exact hG (List.mem_toFinset.2 (List.mem_map.2 ⟨l', hl', e⟩))

/-! ### A Boolean test for binary hierarchies -/

/-- A Boolean test that the code list `l` is a binary hierarchy on `Fin n`: valid codes, a forest,
containing the root and the singletons, and every cluster other than a singleton is the union of
two disjoint clusters. -/
def root_binHierB (n : ℕ) (l : List ℕ) : Bool :=
  decide (Valid n l) && isForestB l && l.contains (2 ^ n - 1) &&
    (List.range n).all (fun i => l.contains (2 ^ i)) &&
    l.all fun c => (List.range n).any (fun i => c == 2 ^ i) ||
      l.any fun a => l.any fun b => a &&& b == 0 && a ||| b == c

theorem root_isBinHier_of_binHierB {n : ℕ} {l : List ℕ} (h : root_binHierB n l = true) :
    IsHierarchy (decF n l) ∧ ∀ A ∈ decF n l, 2 ≤ #A →
      ∃ B ∈ decF n l, ∃ C ∈ decF n l, Disjoint B C ∧ B ∪ C = A := by
  simp only [root_binHierB, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hv, hF⟩, hu⟩, hs⟩, hb⟩ := h
  have hF' := isForest_of_isForestB hv hF
  refine ⟨⟨?_, fun x => ?_, hF'.1, hF'.2⟩, ?_⟩
  · rw [← decC_full n]
    exact decC_mem_decF hu
  · rw [← decC_two_pow x.2]
    exact decC_mem_decF (hs x x.2)
  · intro A hA h2
    obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
    rcases hb c hc with ⟨i, hi, rfl⟩ | ⟨a, ha, b, hb', hab, rfl⟩
    · rw [decC_two_pow hi, card_singleton] at h2
      omega
    · exact ⟨decC n a, decC_mem_decF ha, decC n b, decC_mem_decF hb',
        (decC_disjoint_iff (hv a ha)).2 hab, (decC_or n a b).symm⟩

/-! ### The gene trees on four and five taxa -/

/-- The codes of the rooted tree on `Fin 5` with the nontrivial clusters of codes `a` and `b`. -/
def root_hier5 (a b : ℕ) : List ℕ := [a, b, 1, 2, 4, 8, 16, 31]

/-- The codes of `T5 i`. -/
def root_T5code : ℕ → List ℕ
  | 1 => unrootL 5 (root_hier5 3 7)
  | 2 => unrootL 5 (root_hier5 3 11)
  | 3 => unrootL 5 (root_hier5 3 19)
  | 4 => unrootL 5 (root_hier5 5 7)
  | 5 => unrootL 5 (root_hier5 5 13)
  | 6 => unrootL 5 (root_hier5 5 21)
  | 7 => unrootL 5 (root_hier5 9 11)
  | 8 => unrootL 5 (root_hier5 9 13)
  | 9 => unrootL 5 (root_hier5 9 25)
  | 10 => unrootL 5 (root_hier5 17 19)
  | 11 => unrootL 5 (root_hier5 17 21)
  | 12 => unrootL 5 (root_hier5 17 25)
  | 13 => unrootL 5 (root_hier5 6 7)
  | 14 => unrootL 5 (root_hier5 10 11)
  | 15 => unrootL 5 (root_hier5 18 19)
  | _ => []

theorem root_decF_T5code_1 : decF 5 (root_T5code 1) = T5 1 := by decide +kernel
theorem root_decF_T5code_2 : decF 5 (root_T5code 2) = T5 2 := by decide +kernel
theorem root_decF_T5code_3 : decF 5 (root_T5code 3) = T5 3 := by decide +kernel
theorem root_decF_T5code_4 : decF 5 (root_T5code 4) = T5 4 := by decide +kernel
theorem root_decF_T5code_5 : decF 5 (root_T5code 5) = T5 5 := by decide +kernel
theorem root_decF_T5code_6 : decF 5 (root_T5code 6) = T5 6 := by decide +kernel
theorem root_decF_T5code_7 : decF 5 (root_T5code 7) = T5 7 := by decide +kernel
theorem root_decF_T5code_8 : decF 5 (root_T5code 8) = T5 8 := by decide +kernel
theorem root_decF_T5code_9 : decF 5 (root_T5code 9) = T5 9 := by decide +kernel
theorem root_decF_T5code_10 : decF 5 (root_T5code 10) = T5 10 := by decide +kernel
theorem root_decF_T5code_11 : decF 5 (root_T5code 11) = T5 11 := by decide +kernel
theorem root_decF_T5code_12 : decF 5 (root_T5code 12) = T5 12 := by decide +kernel
theorem root_decF_T5code_13 : decF 5 (root_T5code 13) = T5 13 := by decide +kernel
theorem root_decF_T5code_14 : decF 5 (root_T5code 14) = T5 14 := by decide +kernel
theorem root_decF_T5code_15 : decF 5 (root_T5code 15) = T5 15 := by decide +kernel

theorem root_decF_T5code {i : ℕ} (hi : i ∈ Icc 1 15) : decF 5 (root_T5code i) = T5 i := by
  rw [mem_Icc] at hi
  obtain ⟨h1, h15⟩ := hi
  interval_cases i
  exacts [root_decF_T5code_1, root_decF_T5code_2, root_decF_T5code_3, root_decF_T5code_4,
    root_decF_T5code_5, root_decF_T5code_6, root_decF_T5code_7, root_decF_T5code_8,
    root_decF_T5code_9, root_decF_T5code_10, root_decF_T5code_11, root_decF_T5code_12,
    root_decF_T5code_13, root_decF_T5code_14, root_decF_T5code_15]

theorem root_valid_T5code {i : ℕ} (hi : i ∈ Icc 1 15) : Valid 5 (root_T5code i) := by
  rw [mem_Icc] at hi
  obtain ⟨h1, h15⟩ := hi
  interval_cases i <;> decide +kernel

/-- The codes of the quartet tree `treeOfClusters {A}` on `Fin 4`, `a` being the code of `A`. -/
def root_Q4code (a : ℕ) : List ℕ := unrootL 4 [a, 1, 2, 4, 8, 15]

theorem root_decF_Q4code_3 : decF 4 (root_Q4code 3) = treeOfClusters {{0, 1}} := by
  decide +kernel
theorem root_decF_Q4code_5 : decF 4 (root_Q4code 5) = treeOfClusters {{0, 2}} := by
  decide +kernel
theorem root_decF_Q4code_9 : decF 4 (root_Q4code 9) = treeOfClusters {{0, 3}} := by
  decide +kernel

/-! ### The support of the unrooted gene tree distributions on four and five taxa -/

/-- The unrooted versions of the binary hierarchies on `Fin 5` are the trees `T5 i`. -/
def root_checkT5 : Bool :=
  (root_binEnum 4 31).all fun l => decide (Valid 5 l) &&
    (List.range' 1 15).any fun i => decide (Valid 5 (root_T5code i)) &&
      root_famMask (unrootL 5 l) == root_famMask (root_T5code i)

theorem root_checkT5_eq : root_checkT5 = true := by decide +kernel

theorem root_unrootedDist_eq_zero_five (τ : SpeciesTree (Fin 5)) (T : Finset (Finset (Fin 5)))
    (hT : ∀ i ∈ Icc 1 15, T ≠ T5 i) : τ.unrootedDist id T = 0 := by
  rw [SpeciesTree.unrootedDist]
  refine Finset.sum_eq_zero fun G _ => ?_
  split_ifs with hG
  · by_contra hne
    obtain ⟨l, hl, rfl⟩ := root_rootedDist_support τ hne
    have h := root_checkT5_eq
    simp only [root_checkT5, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true, List.mem_range'_1, beq_iff_eq] at h
    obtain ⟨hv, i, hi, hvi, hs⟩ := h l hl
    have hi' : i ∈ Icc 1 15 := mem_Icc.2 ⟨hi.1, by omega⟩
    apply hT i hi'
    rw [← hG, ← decF_unrootL hv, (root_decF_eq_iff_famMask (valid_unrootL hv) hvi).2 hs,
      root_decF_T5code hi']
  · rfl

/-- The unrooted versions of the binary hierarchies on `Fin 4` are the three quartet trees. -/
def root_checkQ4 : Bool :=
  (root_binEnum 3 15).all fun l => decide (Valid 4 l) &&
    [3, 5, 9].any fun a => decide (Valid 4 (root_Q4code a)) &&
      root_famMask (unrootL 4 l) == root_famMask (root_Q4code a)

theorem root_checkQ4_eq : root_checkQ4 = true := by decide +kernel

theorem root_unrootedDist_eq_zero_four (τ : SpeciesTree (Fin 4)) (T : Finset (Finset (Fin 4)))
    (hT : T ≠ treeOfClusters {{0, 1}} ∧ T ≠ treeOfClusters {{0, 2}} ∧
      T ≠ treeOfClusters {{0, 3}}) :
    τ.unrootedDist id T = 0 := by
  rw [SpeciesTree.unrootedDist]
  refine Finset.sum_eq_zero fun G _ => ?_
  split_ifs with hG
  · by_contra hne
    obtain ⟨l, hl, rfl⟩ := root_rootedDist_support τ hne
    have h := root_checkQ4_eq
    simp only [root_checkQ4, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true, beq_iff_eq] at h
    obtain ⟨hv, a, ha, hva, hs⟩ := h l hl
    have e : T = decF 4 (root_Q4code a) := by
      rw [← hG, ← decF_unrootL hv, (root_decF_eq_iff_famMask (valid_unrootL hv) hva).2 hs]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact hT.1 (e.trans root_decF_Q4code_3)
    · exact hT.2.1 (e.trans root_decF_Q4code_5)
    · exact hT.2.2 (e.trans root_decF_Q4code_9)
  · rfl

/-! ### Tables of all binary hierarchies -/

theorem root_valid_of_binHierB {n : ℕ} {l : List ℕ} (h : root_binHierB n l = true) :
    Valid n l := by
  simp only [root_binHierB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

/-- A Boolean check on a list `Bs` of code lists: each is a binary hierarchy on `Fin n`, no two
of them define the same family of clusters, and every code list of
`root_binEnum (n - 1) (2 ^ n - 1)` defines the same family as one of them. Families are compared
through the bitmasks `root_famMask`. -/
def root_tableB (n : ℕ) (Bs : List (List ℕ)) : Bool :=
  Bs.all (root_binHierB n) && decide (Bs.map root_famMask).Nodup &&
    (root_binEnum (n - 1) (2 ^ n - 1)).all fun l =>
      decide (Valid n l) && (Bs.map root_famMask).contains (root_famMask l)

theorem root_tableB_spec {n : ℕ} {Bs : List (List ℕ)} (h : root_tableB n Bs = true) :
    (∀ l ∈ Bs, IsHierarchy (decF n l) ∧ ∀ A ∈ decF n l, 2 ≤ #A →
      ∃ B ∈ decF n l, ∃ C ∈ decF n l, Disjoint B C ∧ B ∪ C = A) ∧
    (Bs.map (decF n)).Nodup ∧
    ∀ l ∈ root_binEnum (n - 1) (2 ^ n - 1), ∃ l' ∈ Bs, decF n l' = decF n l := by
  simp only [root_tableB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.contains_iff_mem, List.mem_map] at h
  obtain ⟨⟨hb, hp⟩, hc⟩ := h
  have hv : ∀ l ∈ Bs, Valid n l := fun l hl => root_valid_of_binHierB (hb l hl)
  refine ⟨fun l hl => root_isBinHier_of_binHierB (hb l hl), ?_, fun l hl => ?_⟩
  · rw [List.Nodup, List.pairwise_map] at hp ⊢
    refine hp.imp_of_mem fun ha hb' hab e => hab ?_
    exact (root_decF_eq_iff_famMask (hv _ ha) (hv _ hb')).1 e
  · obtain ⟨hvl, l', hl', hs⟩ := hc l hl
    exact ⟨l', hl', (root_decF_eq_iff_famMask (hv l' hl') hvl).2 hs⟩

theorem root_mem_Icc_iff_mem_range' {j N : ℕ} : j ∈ Icc 1 N ↔ j ∈ List.range' 1 N := by
  rw [mem_Icc, List.mem_range'_1]
  omega

/-- **Table 4** for a list of trees `R j` (`1 ≤ j ≤ N`) given by code lists. -/
theorem root_table {n : ℕ} (R : ℕ → Finset (Finset (Fin n))) (code : ℕ → List ℕ) (N : ℕ)
    (hR : ∀ j ∈ Icc 1 N, R j = decF n (code j))
    (hc : root_tableB n ((List.range' 1 N).map code) = true) :
    Set.InjOn R (Icc 1 N : Finset ℕ) ∧
      ∀ G : Finset (Finset (Fin n)),
        (∃ τ : SpeciesTree (Fin n), τ.clusters = G ∧ τ.IsBinary) ↔ ∃ j ∈ Icc 1 N, R j = G := by
  obtain ⟨hbin, hnd, hcomp⟩ := root_tableB_spec hc
  refine ⟨fun a ha b hb hab => ?_, fun G => ⟨?_, ?_⟩⟩
  · rw [Finset.mem_coe] at ha hb
    rw [hR a ha, hR b hb] at hab
    rw [List.map_map] at hnd
    exact List.inj_on_of_nodup_map hnd (root_mem_Icc_iff_mem_range'.1 ha)
      (root_mem_Icc_iff_mem_range'.1 hb) hab
  · rintro ⟨τ, rfl, hτ⟩
    obtain ⟨l, hl, e⟩ := root_binEnum_complete_univ (root_binOn_univ_of_isBinary τ hτ)
    obtain ⟨l', hl', e'⟩ := hcomp l hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl'
    have hj' := root_mem_Icc_iff_mem_range'.2 hj
    exact ⟨j, hj', by rw [hR j hj', e', e]⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨hH, hb⟩ :=
      hbin (code j) (List.mem_map.2 ⟨j, root_mem_Icc_iff_mem_range'.1 hj, rfl⟩)
    rw [hR j hj]
    exact ⟨⟨decF n (code j), hH.1, hH.2.1, hH.2.2.1, hH.2.2.2, fun _ => 1, fun _ _ _ => one_pos⟩,
      rfl, hb⟩

theorem root_sum_filter {α : Type*} (L : List α) (p : α → Bool) (g : α → ℝ) :
    ((L.filter p).map g).sum = (L.map fun j => if p j = true then g j else 0).sum := by
  induction L with
  | nil => simp
  | cons a L ih => by_cases h : p a = true <;> simp [h, ih]

/-- **Table 5** for a list of trees `R j` (`1 ≤ j ≤ N`) given by code lists: `u σ i` is the sum of
the probabilities of the trees `R j` whose unrooted version is `T5 i`. -/
theorem root_u_eq_sum (σ : SpeciesTree (Fin 5)) (R : ℕ → Finset (Finset (Fin 5)))
    (code : ℕ → List ℕ) (N : ℕ) (hR : ∀ j ∈ Icc 1 N, R j = decF 5 (code j))
    (hc : root_tableB 5 ((List.range' 1 N).map code) = true) {i : ℕ} (hi : i ∈ Icc 1 15)
    {js : List ℕ}
    (hjs : (List.range' 1 N).filter
      (fun j => root_famMask (unrootL 5 (code j)) == root_famMask (root_T5code i)) = js) :
    u σ i = (js.map fun j => σ.rootedDist id (R j)).sum := by
  obtain ⟨hbin, hnd, hcomp⟩ := root_tableB_spec hc
  rw [u, root_unrootedDist_eq_sum σ _ hcomp hnd, List.map_map, ← hjs, root_sum_filter]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have hj' := root_mem_Icc_iff_mem_range'.2 hj
  have hv : Valid 5 (code j) :=
    root_valid_of_binHierB (List.all_eq_true.1 (by
      simp only [root_tableB, Bool.and_eq_true] at hc; exact hc.1.1) _
        (List.mem_map.2 ⟨j, hj, rfl⟩))
  have e : unroot (decF 5 (code j)) = T5 i ↔
      (root_famMask (unrootL 5 (code j)) == root_famMask (root_T5code i)) = true := by
    rw [← decF_unrootL hv, ← root_decF_T5code hi, beq_iff_eq]
    exact root_decF_eq_iff_famMask (valid_unrootL hv) (root_valid_T5code hi)
  exact if_congr e (by rw [hR j hj']) rfl

end ADR11
