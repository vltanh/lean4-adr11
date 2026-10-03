module

public import ADR11.MSC.Basic

/-!
# Section 1: counting rooted and unrooted gene trees

"For `n` species, there are `(2n-5)!!` unrooted gene trees, and each unrooted gene tree can be
realized by `2n-3` rooted gene trees, corresponding to choices of an edge on which to place the
root" (Section 1, with the count `(2n-3)!!` of rooted binary topologies cited from
[Felsenstein 2004]).

* `IsBinaryHierarchy G`: `G` is a rooted binary tree on the leaves `L`, given by its clusters.
* `section1_card_rooted`: there are `(2n-3)!!` rooted binary trees on `n ≥ 1` labelled leaves.
* `section1_card_rootings`: each unrooted binary tree on `n ≥ 2` leaves has `2n-3` rooted versions.
* `section1_card_unrooted`: there are `(2n-5)!!` unrooted binary trees on `n ≥ 3` leaves.
-/

@[expose] public section

namespace ADR11

open Finset

/-- A rooted binary tree on the leaves `L`, given by its clusters: a hierarchy in which every
cluster with at least two leaves is the union of two disjoint clusters. -/
def IsBinaryHierarchy {L : Type*} [Fintype L] [DecidableEq L] (G : Finset (Finset L)) : Prop :=
  IsHierarchy G ∧ ∀ A ∈ G, 2 ≤ #A → ∃ B ∈ G, ∃ C ∈ G, Disjoint B C ∧ B ∪ C = A

open scoped Classical in
/-- Section 1 [Felsenstein 2004]: there are `(2n-3)!!` rooted binary trees on `n` labelled
leaves. -/
theorem section1_card_rooted (n : ℕ) (hn : 1 ≤ n) :
    #{G : Finset (Finset (Fin n)) | IsBinaryHierarchy G} = (2 * n - 3).doubleFactorial := by
  sorry

open scoped Classical in
/-- Section 1: each unrooted binary tree on `n ≥ 2` leaves is the unrooted version of exactly
`2n-3` rooted binary trees. -/
theorem section1_card_rootings (n : ℕ) (hn : 2 ≤ n) (G₀ : Finset (Finset (Fin n)))
    (hG₀ : IsBinaryHierarchy G₀) :
    #{G : Finset (Finset (Fin n)) | IsBinaryHierarchy G ∧ unroot G = unroot G₀} = 2 * n - 3 := by
  sorry

open scoped Classical in
/-- Section 1: there are `(2n-5)!!` unrooted binary trees on `n ≥ 3` labelled leaves. -/
theorem section1_card_unrooted (n : ℕ) (hn : 3 ≤ n) :
    #(({G : Finset (Finset (Fin n)) | IsBinaryHierarchy G} : Finset _).image unroot) =
      (2 * n - 5).doubleFactorial := by
  sorry

end ADR11
