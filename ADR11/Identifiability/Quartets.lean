module

public import ADR11.External.Quartets.Steel

/-!
# Corollary 6's argument: quartet trees and their internal lengths determine `σ⁻`

The proof of Corollary 6 (l.574): "That all induced quartet topologies determine the topology
`ψ⁻` is well known [Steel 1992]. Because each internal edge of `ψ⁻` is the internal edge for some
induced quartet tree, `λ⁻` is determined as well."

* `SpeciesTree.sameUnrootedMetricTree_of_restrict`: two species trees whose induced unrooted
  metric trees agree on every set of four taxa have the same unrooted metric tree. The splits of
  `σ⁻` are compared through their quartets by Steel's reconstruction (`mem_unroot_iff_quartets`,
  with `SpeciesTree.restrict_unroot`), and the length of a split through a quartet that
  distinguishes it (`exists_distinguishing_quartet`, Steel's Proposition 6), whose induced split
  is induced by no other split (`SpeciesTree.restrict_unrootedLength`).

The same argument serves for nonbinary trees in Proposition 11, where the reconstruction is that of
Bandelt–Dress and Semple–Steel (Theorem 6.3.5), which `mem_unroot_iff_quartets` also covers.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Membership in `unroot`: a non-root cluster or the complement of one. -/
private theorem quart_mem_unroot {G : Finset (Finset X)} {A : Finset X} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := by
  unfold unroot
  rw [mem_union, mem_erase, mem_image]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨B, hB, rfl⟩)
    · exact Or.inl ⟨h2, h1⟩
    · rw [mem_erase] at hB
      right
      rw [compl_compl]
      exact ⟨hB.2, hB.1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨Aᶜ, mem_erase.2 ⟨h2, h1⟩, compl_compl A⟩

/-- `unroot` is closed under complements. -/
private theorem quart_compl_mem_unroot {G : Finset (Finset X)} {A : Finset X}
    (h : A ∈ unroot G) : Aᶜ ∈ unroot G := by
  rw [quart_mem_unroot] at h ⊢
  rw [compl_compl]
  exact h.symm

/-- The sides of the splits of `σ⁻` are nonempty. -/
private theorem quart_nonempty_of_mem_unroot (σ : SpeciesTree X) {A : Finset X}
    (h : A ∈ unroot σ.clusters) : A.Nonempty := by
  rcases quart_mem_unroot.1 h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact σ.nonempty_of_mem A h1
  · rw [nonempty_iff_ne_empty]
    rintro rfl
    exact h2 compl_empty


omit [Fintype X] in
/-- Two sets with the same trace on `S` contain the same taxa of `S`. -/
private theorem quart_mem_iff_of_subtype_eq {S A C : Finset X}
    (h : C.subtype (· ∈ S) = A.subtype (· ∈ S)) {x : X} (hx : x ∈ S) : x ∈ C ↔ x ∈ A := by
  have h1 : (⟨x, hx⟩ : S) ∈ C.subtype (· ∈ S) ↔ (⟨x, hx⟩ : S) ∈ A.subtype (· ∈ S) := by
    rw [h]
  simpa only [mem_subtype] using h1

/-- The trace of a complement is the complement of the trace. -/
private theorem quart_subtype_compl (S A : Finset X) :
    Aᶜ.subtype (· ∈ S) = (A.subtype (· ∈ S))ᶜ := by
  ext ⟨x, hx⟩
  simp

/-- The two sides of a split have the same unrooted length. -/
private theorem quart_unrootedLength_compl (τ : SpeciesTree X) (A : Finset X) :
    τ.unrootedLength Aᶜ = τ.unrootedLength A := by
  unfold SpeciesTree.unrootedLength
  rw [compl_compl]
  refine sum_congr ?_ fun _ _ => rfl
  ext C
  simp only [mem_filter]
  tauto

omit [Fintype X] in
/-- Four distinct taxa form a set of four taxa. -/
private theorem quart_card_quartet {a a' b b' : X} (haa : a ≠ a') (hab : a ≠ b) (hab' : a ≠ b')
    (ha'b : a' ≠ b) (ha'b' : a' ≠ b') (hbb : b ≠ b') : #({a, a', b, b'} : Finset X) = 4 := by
  rw [card_insert_of_notMem, card_insert_of_notMem, card_pair hbb]
  · simp [ha'b, ha'b']
  · simp [haa, hab, hab']

/-- If a split `A` of `σ⁻` separates `aa'|bb'`, and `σ` and `σ'` induce the same unrooted tree on
a set `Q` containing `a, a', b, b'`, then some split of `σ'⁻` separates `aa'|bb'`. -/
private theorem quart_separating_of_restrict (σ σ' : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) {a a' b b' : X} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∉ A)
    (hb' : b' ∉ A) {Q : Finset X} (hQ : Q.Nonempty) (haQ : a ∈ Q) (ha'Q : a' ∈ Q)
    (hbQ : b ∈ Q) (hb'Q : b' ∈ Q)
    (hU : unroot (σ.restrict Q hQ).clusters = unroot (σ'.restrict Q hQ).clusters) :
    ∃ C ∈ unroot σ'.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C ∧ b' ∉ C := by
  have h1 : A.subtype (· ∈ Q) ∈ restrictSplits Q (unroot σ'.clusters) := by
    rw [← SpeciesTree.restrict_unroot σ' Q hQ, ← hU, SpeciesTree.restrict_unroot]
    exact mem_image.2 ⟨A, mem_filter.2 ⟨hA, ⟨a, mem_inter.2 ⟨ha, haQ⟩⟩,
      ⟨b, mem_inter.2 ⟨mem_compl.2 hb, hbQ⟩⟩⟩, rfl⟩
  unfold restrictSplits at h1
  obtain ⟨C, hC, hCA⟩ := mem_image.1 h1
  have key : ∀ x ∈ Q, x ∈ C ↔ x ∈ A := fun x hx => quart_mem_iff_of_subtype_eq hCA hx
  exact ⟨C, (mem_filter.1 hC).1, (key a haQ).2 ha, (key a' ha'Q).2 ha',
    fun h => hb ((key b hbQ).1 h), fun h => hb' ((key b' hb'Q).1 h)⟩

/-- If `σ` and `σ'` induce the same unrooted trees on all sets of four taxa, every split of `σ⁻`
is a split of `σ'⁻`. -/
private theorem quart_unroot_subset (σ σ' : SpeciesTree X)
    (h : ∀ Q : Finset X, ∀ hQ : Q.Nonempty, #Q = 4 →
      unroot (σ.restrict Q hQ).clusters = unroot (σ'.restrict Q hQ).clusters) :
    unroot σ.clusters ⊆ unroot σ'.clusters := by
  intro A hA
  have hAne := quart_nonempty_of_mem_unroot σ hA
  have hAcne := quart_nonempty_of_mem_unroot σ (quart_compl_mem_unroot hA)
  by_cases h1 : #A ≤ 1
  · obtain ⟨x, rfl⟩ := card_eq_one.1 (le_antisymm h1 (card_pos.2 hAne))
    refine quart_mem_unroot.2 (Or.inl ⟨σ'.singleton_mem x, ?_⟩)
    intro hu
    rw [hu, compl_univ] at hAcne
    exact not_nonempty_empty hAcne
  by_cases h2 : #Aᶜ ≤ 1
  · obtain ⟨x, hx⟩ := card_eq_one.1 (le_antisymm h2 (card_pos.2 hAcne))
    refine quart_mem_unroot.2 (Or.inr ⟨hx ▸ σ'.singleton_mem x, ?_⟩)
    intro hu
    have : A = ∅ := by rw [← compl_compl A, hu, compl_univ]
    exact hAne.ne_empty this
  rw [mem_unroot_iff_quartets σ' (by omega) (by omega)]
  intro a ha a' ha' b hb b' hb' haa hbb
  rw [mem_compl] at hb hb'
  have hQ : ({a, a', b, b'} : Finset X).Nonempty := insert_nonempty _ _
  have hab : a ≠ b := by rintro rfl; exact hb ha
  have hab' : a ≠ b' := by rintro rfl; exact hb' ha
  have ha'b : a' ≠ b := by rintro rfl; exact hb ha'
  have ha'b' : a' ≠ b' := by rintro rfl; exact hb' ha'
  exact quart_separating_of_restrict σ σ' hA ha ha' hb hb' hQ (by simp) (by simp) (by simp)
    (by simp) (h _ hQ (quart_card_quartet haa hab hab' ha'b ha'b' hbb))

/-- Unrooted metric trees are determined by their quartets. -/
theorem SpeciesTree.sameUnrootedMetricTree_of_restrict (σ σ' : SpeciesTree X)
    (h : ∀ Q : Finset X, ∀ hQ : Q.Nonempty, #Q = 4 →
      (σ.restrict Q hQ).SameUnrootedMetricTree (σ'.restrict Q hQ)) :
    σ.SameUnrootedMetricTree σ' := by
  have hU : unroot σ.clusters = unroot σ'.clusters :=
    Subset.antisymm (quart_unroot_subset σ σ' fun Q hQ hQ4 => (h Q hQ hQ4).1)
      (quart_unroot_subset σ' σ fun Q hQ hQ4 => (h Q hQ hQ4).1.symm)
  refine ⟨hU, ?_⟩
  intro A hA hA₁ hA₂
  have hAne := quart_nonempty_of_mem_unroot σ hA
  obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, huniq⟩ :=
    exists_distinguishing_quartet σ hA hA₁ hA₂
  rw [mem_compl] at hb hb'
  have hab : a ≠ b := by rintro rfl; exact hb ha
  have hab' : a ≠ b' := by rintro rfl; exact hb' ha
  have ha'b : a' ≠ b := by rintro rfl; exact hb ha'
  have ha'b' : a' ≠ b' := by rintro rfl; exact hb' ha'
  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset X, Q = {a, a', b, b'} := ⟨_, rfl⟩
  have hQ : Q.Nonempty := hQdef ▸ insert_nonempty _ _
  have haQ : a ∈ Q := by simp [hQdef]
  have ha'Q : a' ∈ Q := by simp [hQdef]
  have hbQ : b ∈ Q := by simp [hQdef]
  have hb'Q : b' ∈ Q := by simp [hQdef]
  obtain ⟨hUQ, hLQ⟩ := h Q hQ (hQdef ▸ quart_card_quartet haa hab hab' ha'b ha'b' hbb)
  -- the split of the induced quartet tree induced by `A`
  have hC₀ : A.subtype (· ∈ Q) ∈ unroot (σ.restrict Q hQ).clusters := by
    rw [SpeciesTree.restrict_unroot]
    exact mem_image.2 ⟨A, mem_filter.2 ⟨hA, ⟨a, mem_inter.2 ⟨ha, haQ⟩⟩,
      ⟨b, mem_inter.2 ⟨mem_compl.2 hb, hbQ⟩⟩⟩, rfl⟩
  have hC₀₁ : 2 ≤ #(A.subtype (· ∈ Q)) :=
    one_lt_card.2 ⟨⟨a, haQ⟩, mem_subtype.2 ha, ⟨a', ha'Q⟩, mem_subtype.2 ha',
      fun h => haa (congrArg Subtype.val h)⟩
  have hC₀₂ : 2 ≤ #(A.subtype (· ∈ Q))ᶜ :=
    one_lt_card.2 ⟨⟨b, hbQ⟩, by simp [hb], ⟨b', hb'Q⟩, by simp [hb'],
      fun h => hbb (congrArg Subtype.val h)⟩
  have hAA : A ≠ Aᶜ := by
    intro h
    obtain ⟨x, hx⟩ := hAne
    have hx' := hx
    rw [h] at hx'
    exact mem_compl.1 hx' hx
  -- the length of the split induced by `A` in an induced quartet tree is the length of `A`
  have hlen : ∀ τ : SpeciesTree X, A ∈ unroot τ.clusters →
      (∀ C ∈ unroot τ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A) →
      A.subtype (· ∈ Q) ∈ unroot (τ.restrict Q hQ).clusters →
      (τ.restrict Q hQ).unrootedLength (A.subtype (· ∈ Q)) = τ.unrootedLength A := by
    intro τ hAτ huniqτ hCτ
    rw [τ.restrict_unrootedLength Q hQ _ hCτ hC₀₁ hC₀₂]
    have hfilter : (unroot τ.clusters).filter (fun B => B.subtype (· ∈ Q) = A.subtype (· ∈ Q) ∨
        B.subtype (· ∈ Q) = (A.subtype (· ∈ Q))ᶜ) = {A, Aᶜ} := by
      ext B
      rw [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hB, hB1 | hB1⟩
        · left
          have key : ∀ x ∈ Q, x ∈ B ↔ x ∈ A := fun x hx => quart_mem_iff_of_subtype_eq hB1 hx
          exact huniqτ B hB ((key a haQ).2 ha) ((key a' ha'Q).2 ha')
            (fun h => hb ((key b hbQ).1 h)) (fun h => hb' ((key b' hb'Q).1 h))
        · right
          have hB2 : Bᶜ.subtype (· ∈ Q) = A.subtype (· ∈ Q) := by
            rw [quart_subtype_compl, hB1, compl_compl]
          have key : ∀ x ∈ Q, x ∈ Bᶜ ↔ x ∈ A := fun x hx => quart_mem_iff_of_subtype_eq hB2 hx
          have := huniqτ Bᶜ (quart_compl_mem_unroot hB) ((key a haQ).2 ha) ((key a' ha'Q).2 ha')
            (fun h => hb ((key b hbQ).1 h)) (fun h => hb' ((key b' hb'Q).1 h))
          rw [← this, compl_compl]
      · rintro (rfl | rfl)
        · exact ⟨hAτ, Or.inl rfl⟩
        · exact ⟨quart_compl_mem_unroot hAτ, Or.inr (quart_subtype_compl _ _)⟩
    rw [hfilter, sum_pair hAA, quart_unrootedLength_compl]
    ring
  have hA' : A ∈ unroot σ'.clusters := hU ▸ hA
  have huniq' : ∀ C ∈ unroot σ'.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A := by
    rw [← hU]
    exact huniq
  rw [← hlen σ hA huniq hC₀, ← hlen σ' hA' huniq' (hUQ ▸ hC₀)]
  exact hLQ _ hC₀ hC₀₁ hC₀₂

end ADR11
