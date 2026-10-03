module

public import ADR11.MSC.Basic

/-!
# Marginalization

The paper's Lemma 5 is "clear from the structure of the coalescent model". It combines two facts:

* *Dropping lineages* (`forestDist_comp_embedding`): the forest formed by a subset of the lineages
  is distributed as the multispecies coalescent of that subset. Kingman's coalescent is
  consistent: restricting a forest to a subset of the lineages lumps the chain into Kingman's
  coalescent on the subset (`kingmanTransition_lump`, `kingmanAbsorption_lump`).
* *Pruning the species tree* (`rootedDist_restrict`): when only taxa in `S` are sampled, the
  populations without lineages do nothing, populations in a chain with the same lineages merge
  into one population whose length is the sum (`kingmanTransition_add`), and the populations above
  the most recent common ancestor of `S` merge into the population above the root.

* `restrictForest e F`: the restriction of a forest on `L` to the lineages `L'`, along an
  embedding `e : L' ↪ L`.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {L : Type*} [Fintype L] [DecidableEq L] {L' : Type*} [Fintype L'] [DecidableEq L']

/-- The restriction of a forest on `L` to the lineages `L'`, along an embedding `e : L' ↪ L`: the
nonempty traces of its clusters. -/
def restrictForest (e : L' ↪ L) (F : Finset (Finset L)) : Finset (Finset L') :=
  (F.filter fun A => ∃ l, e l ∈ A).image fun A => univ.filter fun l => e l ∈ A

theorem IsForest.restrictForest {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) :
    IsForest (restrictForest e F) := by
  sorry

/-- Consistency of Kingman's coalescent (lumpability). -/
theorem kingmanTransition_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) (t : ℝ)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then kingmanTransition t F G else 0) =
      kingmanTransition t (restrictForest e F) G' := by
  sorry

theorem kingmanAbsorption_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then kingmanAbsorption F G else 0) =
      kingmanAbsorption (restrictForest e F) G' := by
  sorry

/-- Dropping lineages: the multispecies coalescent of the lineages `L'` (sampled through
`s ∘ e`) is the restriction of the multispecies coalescent of the lineages `L`. -/
theorem forestDist_comp_embedding {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (s : L → X) (e : L' ↪ L) {A : Finset X} (hA : A ∈ H)
    (G' : Finset (Finset L')) :
    forestDist H len (s ∘ e) A G' =
      ∑ G, if restrictForest e G = G' then forestDist H len s A G else 0 := by
  sorry

theorem SpeciesTree.rootedDist_comp_embedding (σ : SpeciesTree X) (s : L → X) (e : L' ↪ L)
    (G' : Finset (Finset L')) :
    σ.rootedDist (s ∘ e) G' = ∑ G, if restrictForest e G = G' then σ.rootedDist s G else 0 := by
  sorry

/-- Pruning the species tree: if all lineages are sampled from taxa in `S`, the multispecies
coalescent on `σ` is the multispecies coalescent on the induced species tree `σ(S)`. -/
theorem SpeciesTree.rootedDist_restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty)
    (s : L → S) (G : Finset (Finset L)) :
    (σ.restrict S hS).rootedDist s G = σ.rootedDist (fun l => (s l : X)) G := by
  sorry

/-- Unrooting commutes with restricting a complete gene tree to a subset of the lineages. -/
theorem unroot_restrictForest {G : Finset (Finset L)} (hG : IsForest G) (hroot : univ ∈ G)
    (e : L' ↪ L) [Nonempty L'] :
    unroot (restrictForest e G) =
      ((unroot G).filter fun A => (∃ l, e l ∈ A) ∧ ∃ l, e l ∉ A).image
        fun A => univ.filter fun l => e l ∈ A := by
  sorry

end ADR11
