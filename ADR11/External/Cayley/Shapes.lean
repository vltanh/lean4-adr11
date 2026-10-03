module

public import ADR11.MSC.Relabel
public import ADR11.SmallTrees
public import ADR11.Trees.Classify

/-!
# Rooted tree shapes on three, four and five taxa

[A. Cayley, *On the theory of the analytical forms called trees*, Philos. Mag. 13 (1857)
172–176], cited in Section 5 of the paper: there are two unlabelled rooted shapes on three taxa,
five on four taxa and twelve on five taxa, binary or not. In the representation by hierarchies,
every hierarchy on `Fin n` is a relabelling of exactly one of the listed representatives.

* `shapes3`: `(a,b,c)` and `((a,b),c)`.
* `shapes4`: `(a,b,c,d)`, `((a,b),c,d)`, `((a,b,c),d)`, `((a,b),(c,d))`, `(((a,b),c),d)`.
* `shapes5`: the balanced tree, the caterpillar, the pseudocaterpillar and `P₁, …, P₉` of Table 6.
-/

@[expose] public section

namespace ADR11

open Finset

/-- The two rooted shapes on three taxa. -/
def shapes3 : ℕ → Finset (Finset (Fin 3))
  | 1 => hierarchyOf ∅
  | _ => hierarchyOf {{0, 1}}

/-- The five rooted shapes on four taxa. -/
def shapes4 : ℕ → Finset (Finset (Fin 4))
  | 1 => hierarchyOf ∅
  | 2 => hierarchyOf {{0, 1}}
  | 3 => hierarchyOf {{0, 1, 2}}
  | 4 => balanced4
  | _ => caterpillar4

/-- The twelve rooted shapes on five taxa: the three binary shapes of Fig. 2 and the nine
nonbinary representatives of Table 6. -/
def shapes5 : ℕ → Finset (Finset (Fin 5))
  | 1 => balanced5
  | 2 => caterpillar5
  | 3 => pseudocaterpillar5
  | k => polytomy5 (k - 3)

/-! ### Proof

Shapes are distinguished by the number of pairs of nested clusters, which is invariant under
relabelling. A hierarchy on four or five taxa is transported to a rooting of a standard unrooted
tree (`ADR11.exists_equiv_unroot_eq_U4`, `ADR11.exists_equiv_unroot_eq_U5`), and each of these
rootings is a relabelling of a listed shape. -/

/-- The number of pairs `A ⊆ B` of clusters of `H`: an invariant of relabelling. -/
def classify_nestCount {X : Type*} [DecidableEq X] (H : Finset (Finset X)) : ℕ :=
  ∑ A ∈ H, #(H.filter fun B => A ⊆ B)

theorem classify_nestCount_relabel {X Y : Type*} [DecidableEq X] [DecidableEq Y] (π : X ≃ Y)
    (H : Finset (Finset X)) : classify_nestCount (relabelFamily π H) = classify_nestCount H := by
  unfold classify_nestCount relabelFamily
  have hinj : Function.Injective fun A : Finset X => A.map π.toEmbedding := map_injective _
  rw [sum_image hinj.injOn]
  refine sum_congr rfl fun A _ => ?_
  rw [filter_image, card_image_of_injective _ hinj]
  congr 1
  exact filter_congr fun B _ => map_subset_map

theorem classify_eq_of_relabel {n m : ℕ} {S : ℕ → Finset (Finset (Fin n))}
    (hinj : ∀ a ∈ Icc 1 m, ∀ b ∈ Icc 1 m,
      classify_nestCount (S a) = classify_nestCount (S b) → a = b)
    {H : Finset (Finset (Fin n))} {k k' : ℕ} (hk : k ∈ Icc 1 m) (hk' : k' ∈ Icc 1 m)
    {π π' : Fin n ≃ Fin n} (h : H = relabelFamily π (S k)) (h' : H = relabelFamily π' (S k')) :
    k' = k := by
  apply hinj k' hk' k hk
  rw [← classify_nestCount_relabel π' (S k'), ← h', h, classify_nestCount_relabel]

/-- A permutation of `Fin n` given by its values and those of its inverse. -/
def classify_perm {n : ℕ} (f g : Fin n → Fin n) (h₁ : ∀ i, g (f i) = i := by decide)
    (h₂ : ∀ i, f (g i) = i := by decide) : Fin n ≃ Fin n :=
  ⟨f, g, h₁, h₂⟩

section Decide

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

theorem classify_nestCount_shapes3 : ∀ a ∈ Icc 1 2, ∀ b ∈ Icc 1 2,
    classify_nestCount (shapes3 a) = classify_nestCount (shapes3 b) → a = b := by
  decide +kernel

theorem classify_nestCount_shapes4 : ∀ a ∈ Icc 1 5, ∀ b ∈ Icc 1 5,
    classify_nestCount (shapes4 a) = classify_nestCount (shapes4 b) → a = b := by
  decide +kernel

theorem classify_nestCount_shapes5 : ∀ a ∈ Icc 1 12, ∀ b ∈ Icc 1 12,
    classify_nestCount (shapes5 a) = classify_nestCount (shapes5 b) → a = b := by
  decide +kernel

theorem classify_cands3 : ∀ A ∈ (univ : Finset (Finset (Fin 3))), 2 ≤ #A → A ≠ univ →
    A ∈ ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 3))) := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem classify_laminar3 : ∀ N ∈ ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 3))).powerset,
    (∀ A ∈ N, ∀ B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
      N = ∅ ∨ N = {{0, 1}} ∨ N = {{0, 2}} ∨ N = {{1, 2}} := by
  decide +kernel

end Decide

theorem classify_exists_shape3 (H : Finset (Finset (Fin 3))) (hH : IsHierarchy H) :
    ∃ k ∈ Icc 1 2, ∃ π : Fin 3 ≃ Fin 3, H = relabelFamily π (shapes3 k) := by
  have hN := classify_eq_hierarchyOf hH
  have hC : (H.filter fun A => 2 ≤ #A ∧ A ≠ univ) ∈
      ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 3))).powerset := by
    rw [mem_powerset]
    intro A hA
    rw [mem_filter] at hA
    exact classify_cands3 A (mem_univ A) hA.2.1 hA.2.2
  have hlam : ∀ A ∈ H.filter (fun A => 2 ≤ #A ∧ A ≠ univ),
      ∀ B ∈ H.filter (fun A => 2 ≤ #A ∧ A ≠ univ), A ⊆ B ∨ B ⊆ A ∨ Disjoint A B :=
    fun A hA B hB => hH.2.2.2 A (mem_filter.1 hA).1 B (mem_filter.1 hB).1
  rw [hN]
  rcases classify_laminar3 _ hC hlam with h | h | h | h <;> rw [h]
  · exact ⟨1, by simp, Equiv.refl _, by decide +kernel⟩
  · exact ⟨2, by simp, Equiv.refl _, by decide +kernel⟩
  · exact ⟨2, by simp, classify_perm ![0, 2, 1] ![0, 2, 1], by decide +kernel⟩
  · exact ⟨2, by simp, classify_perm ![1, 2, 0] ![2, 0, 1], by decide +kernel⟩

theorem classify_rootings4_shape : ∀ k₀ ∈ ({0, 1} : Finset ℕ), ∀ R ∈ rootings4 k₀,
    ∃ k ∈ Icc 1 5, ∃ π : Fin 4 ≃ Fin 4, R = relabelFamily π (shapes4 k) := by
  intro k₀ hk₀ R hR
  simp only [mem_insert, mem_singleton] at hk₀
  rcases hk₀ with rfl | rfl
  · simp only [rootings4, mem_insert, mem_singleton] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, by simp, Equiv.refl _, by decide +kernel⟩
    · exact ⟨3, by simp, Equiv.refl _, by decide +kernel⟩
    · exact ⟨3, by simp, classify_perm ![0, 1, 3, 2] ![0, 1, 3, 2], by decide +kernel⟩
    · exact ⟨3, by simp, classify_perm ![0, 2, 3, 1] ![0, 3, 1, 2], by decide +kernel⟩
    · exact ⟨3, by simp, classify_perm ![1, 2, 3, 0] ![3, 0, 1, 2], by decide +kernel⟩
  · simp only [rootings4, mem_insert, mem_singleton] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨5, by simp, Equiv.refl _, by decide +kernel⟩
    · exact ⟨5, by simp, classify_perm ![0, 1, 3, 2] ![0, 1, 3, 2], by decide +kernel⟩
    · exact ⟨5, by simp, classify_perm ![2, 3, 0, 1] ![2, 3, 0, 1], by decide +kernel⟩
    · exact ⟨5, by simp, classify_perm ![2, 3, 1, 0] ![3, 2, 0, 1], by decide +kernel⟩
    · exact ⟨4, by simp, Equiv.refl _, by decide +kernel⟩
    · exact ⟨2, by simp, Equiv.refl _, by decide +kernel⟩
    · exact ⟨2, by simp, classify_perm ![2, 3, 0, 1] ![2, 3, 0, 1], by decide +kernel⟩

theorem classify_rootings5_shape : ∀ k₀ ∈ ({0, 1, 2} : Finset ℕ), ∀ R ∈ rootings5 k₀,
    ∃ k ∈ Icc 1 12, ∃ π : Fin 5 ≃ Fin 5, R = relabelFamily π (shapes5 k) := by
  intro k₀ hk₀ R hR
  simp only [mem_insert, mem_singleton] at hk₀
  rcases hk₀ with rfl | rfl | rfl
  · simp only [rootings5, mem_insert, mem_singleton] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨4, by simp, Equiv.refl _, by decide +kernel⟩
    · exact ⟨6, by simp, classify_perm ![1, 2, 3, 4, 0] ![4, 0, 1, 2, 3], by decide +kernel⟩
    · exact ⟨6, by simp, classify_perm ![0, 2, 3, 4, 1] ![0, 4, 1, 2, 3], by decide +kernel⟩
    · exact ⟨6, by simp, classify_perm ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3], by decide +kernel⟩
    · exact ⟨6, by simp, classify_perm ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3], by decide +kernel⟩
    · exact ⟨6, by simp, Equiv.refl _, by decide +kernel⟩
  · simp only [rootings5, mem_insert, mem_singleton] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨5, by simp, classify_perm ![2, 3, 4, 0, 1] ![3, 4, 0, 1, 2], by decide +kernel⟩
    · exact ⟨7, by simp, classify_perm ![2, 3, 4, 0, 1] ![3, 4, 0, 1, 2], by decide +kernel⟩
    · exact ⟨11, by simp, classify_perm ![2, 3, 4, 0, 1] ![3, 4, 0, 1, 2], by decide +kernel⟩
    · exact ⟨12, by simp, classify_perm ![2, 3, 4, 1, 0] ![4, 3, 0, 1, 2], by decide +kernel⟩
    · exact ⟨12, by simp, classify_perm ![2, 3, 4, 0, 1] ![3, 4, 0, 1, 2], by decide +kernel⟩
    · exact ⟨10, by simp, Equiv.refl _, by decide +kernel⟩
    · exact ⟨10, by simp, classify_perm ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4], by decide +kernel⟩
    · exact ⟨10, by simp, classify_perm ![0, 1, 4, 2, 3] ![0, 1, 3, 4, 2], by decide +kernel⟩
  · simp only [rootings5, mem_insert, mem_singleton] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, by simp, Equiv.refl _, by decide +kernel⟩
    · exact ⟨2, by simp, classify_perm ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3], by decide +kernel⟩
    · exact ⟨2, by simp, classify_perm ![3, 4, 2, 1, 0] ![4, 3, 2, 0, 1], by decide +kernel⟩
    · exact ⟨2, by simp, classify_perm ![3, 4, 2, 0, 1] ![3, 4, 2, 0, 1], by decide +kernel⟩
    · exact ⟨3, by simp, Equiv.refl _, by decide +kernel⟩
    · exact ⟨1, by simp, Equiv.refl _, by decide +kernel⟩
    · exact ⟨1, by simp, classify_perm ![3, 4, 2, 0, 1] ![3, 4, 2, 0, 1], by decide +kernel⟩
    · exact ⟨8, by simp, Equiv.refl _, by decide +kernel⟩
    · exact ⟨9, by simp, Equiv.refl _, by decide +kernel⟩
    · exact ⟨9, by simp, classify_perm ![3, 4, 2, 0, 1] ![3, 4, 2, 0, 1], by decide +kernel⟩

theorem classify_exists_shape4 (H : Finset (Finset (Fin 4))) (hH : IsHierarchy H) :
    ∃ k ∈ Icc 1 5, ∃ π : Fin 4 ≃ Fin 4, H = relabelFamily π (shapes4 k) := by
  let τ : SpeciesTree (Fin 4) :=
    ⟨H, hH.1, hH.2.1, hH.2.2.1, hH.2.2.2, fun _ => 1, fun _ _ _ => one_pos⟩
  obtain ⟨e, k₀, hk₀, he⟩ := exists_equiv_unroot_eq_U4 (by simp) τ
  obtain ⟨k, hk, π, hπ⟩ := classify_rootings4_shape k₀ hk₀ _ (mem_rootings4 _ k₀ hk₀ he)
  refine ⟨k, hk, π.trans e, ?_⟩
  rw [← classify_relabelFamily_trans, ← hπ]
  show H = relabelFamily e (relabelFamily e.symm H)
  have := relabelFamily_symm e.symm H
  rw [Equiv.symm_symm] at this
  exact this.symm

theorem classify_exists_shape5 (H : Finset (Finset (Fin 5))) (hH : IsHierarchy H) :
    ∃ k ∈ Icc 1 12, ∃ π : Fin 5 ≃ Fin 5, H = relabelFamily π (shapes5 k) := by
  let τ : SpeciesTree (Fin 5) :=
    ⟨H, hH.1, hH.2.1, hH.2.2.1, hH.2.2.2, fun _ => 1, fun _ _ _ => one_pos⟩
  obtain ⟨e, k₀, hk₀, he⟩ := exists_equiv_unroot_eq_U5 (by simp) τ
  obtain ⟨k, hk, π, hπ⟩ := classify_rootings5_shape k₀ hk₀ _ (mem_rootings5 _ k₀ hk₀ he)
  refine ⟨k, hk, π.trans e, ?_⟩
  rw [← classify_relabelFamily_trans, ← hπ]
  show H = relabelFamily e (relabelFamily e.symm H)
  have := relabelFamily_symm e.symm H
  rw [Equiv.symm_symm] at this
  exact this.symm

/-- Every hierarchy on `Fin n` (`n = 3, 4, 5`) is a relabelling of exactly one of the listed
shapes: two on three taxa, five on four taxa, twelve on five taxa. -/
theorem cayley_shapes :
    (∀ H : Finset (Finset (Fin 3)), IsHierarchy H →
      ∃! k, k ∈ Icc 1 2 ∧ ∃ π : Fin 3 ≃ Fin 3, H = relabelFamily π (shapes3 k)) ∧
    (∀ H : Finset (Finset (Fin 4)), IsHierarchy H →
      ∃! k, k ∈ Icc 1 5 ∧ ∃ π : Fin 4 ≃ Fin 4, H = relabelFamily π (shapes4 k)) ∧
    (∀ H : Finset (Finset (Fin 5)), IsHierarchy H →
      ∃! k, k ∈ Icc 1 12 ∧ ∃ π : Fin 5 ≃ Fin 5, H = relabelFamily π (shapes5 k)) := by
  refine ⟨fun H hH => ?_, fun H hH => ?_, fun H hH => ?_⟩
  · obtain ⟨k, hk, π, hπ⟩ := classify_exists_shape3 H hH
    exact ⟨k, ⟨hk, π, hπ⟩, fun k' ⟨hk', _, hπ'⟩ =>
      classify_eq_of_relabel classify_nestCount_shapes3 hk hk' hπ hπ'⟩
  · obtain ⟨k, hk, π, hπ⟩ := classify_exists_shape4 H hH
    exact ⟨k, ⟨hk, π, hπ⟩, fun k' ⟨hk', _, hπ'⟩ =>
      classify_eq_of_relabel classify_nestCount_shapes4 hk hk' hπ hπ'⟩
  · obtain ⟨k, hk, π, hπ⟩ := classify_exists_shape5 H hH
    exact ⟨k, ⟨hk, π, hπ⟩, fun k' ⟨hk', _, hπ'⟩ =>
      classify_eq_of_relabel classify_nestCount_shapes5 hk hk' hπ hπ'⟩

end ADR11
