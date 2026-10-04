module

public import ADR11.Nonbinary.FiveTaxa.Ac1Classes

/-!
# Appendix C: the rooted shape read off the classes of gene trees

The proof of Proposition 11 (Appendix C, l. 943–971) first reads the unlabelled rooted shape of a
five-taxon species tree off its classes of equiprobable gene trees, before the unrooted species
tree is used: the least probable class `𝒞` has `15` gene trees for `P₁`, `12` for `P₂` and `P₃`,
`10` for `P₅` and `P₇`, `8` for the resolved pseudocaterpillar and `6` for the other shapes. `P₂`
and `P₃` are told apart by the taxa in no cherry of the gene trees of their 3-element class; `P₅`
and `P₇` by the cherries that the gene trees of their two 2-element classes have in common, also
when these classes merge into one 4-element class; when `|𝒞| = 6` the class with the second
smallest probability has two gene trees for the caterpillar, three for `P₉`, six for `P₄` and `P₈`,
and four for the balanced tree and `P₆`. The pairs `P₄`, `P₈` and balanced, `P₆` are told apart
only later, with the branch lengths (l. 988–993).

## Main results

* `sh_shape`, `sh_groupOf`: the unlabelled rooted shape of a hierarchy on five taxa, and its group
  (`sh_Group`: the twelve shapes, with `P₄`, `P₈` and balanced, `P₆` taken together); both are
  invariant under relabelling (`sh_groupOf_relabel`).
* `sh_read`: the group read off the classes of gene trees by the rules of Appendix C
  (`sh_rules`). It depends only on the distribution (`sh_read_congr`), and it is invariant under
  relabelling the taxa (`sh_read_relabel`: a relabelling permutes the gene trees, hence their
  classes, and maps cherries to cherries).
* `sh_P2_P3_rule`, `sh_P5_P7_rule`: the rules for `|𝒞| = 12` and `|𝒞| = 10`, on the
  representatives `P₂`, `P₃`, `P₅`, `P₇` of Table 6.
* `sh_read_rep`: on the twelve representatives of the shapes (Table 6 and Section 4.2) the rules
  give the group of the shape; `sh_read_eq_groupOf`: hence on every species tree on five taxa,
  which is a relabelling of a representative ("permuting labels", l. 319).
* `sh_group_eq`: two species trees on five taxa with the same unrooted gene tree distribution
  have the same shape group (without Corollary 6).
-/

@[expose] public section

namespace ADR11

open Finset

/-! ### The shapes and their groups -/

/-- The groups of rooted shapes on five taxa that Appendix C tells apart by the classes of gene
trees: `P₁`, `P₂`, `P₃`, `P₅`, `P₇`, `P₉`, the caterpillar and the pseudocaterpillar, and the
two groups `{P₄, P₈}` and `{balanced, P₆}`, whose members are told apart only with the branch
lengths. -/
inductive sh_Group
  | p1 | p2 | p3 | p48 | p5 | balP6 | p7 | p9 | cat | pseudo
  deriving DecidableEq

/-- The shape with `n₂`, `n₃`, `n₄` nontrivial clusters of two, three and four taxa: `k` for `P_k`
(Table 6), `10` for the balanced tree, `11` for the caterpillar and `12` for the
pseudocaterpillar; with one cluster of two taxa and one of three, `nested` tells whether the first
lies in the second (`P₆`) or not (`P₈`). -/
def sh_shapeOf (n₂ n₃ n₄ : ℕ) (nested : Bool) : ℕ :=
  if n₂ = 0 ∧ n₃ = 0 ∧ n₄ = 0 then 1
  else if n₂ = 1 ∧ n₃ = 0 ∧ n₄ = 0 then 2
  else if n₂ = 0 ∧ n₃ = 0 ∧ n₄ = 1 then 3
  else if n₂ = 0 ∧ n₃ = 1 ∧ n₄ = 0 then 4
  else if n₂ = 2 ∧ n₃ = 0 ∧ n₄ = 0 then 5
  else if n₂ = 1 ∧ n₃ = 1 ∧ n₄ = 0 then (if nested then 6 else 8)
  else if n₂ = 1 ∧ n₃ = 0 ∧ n₄ = 1 then 7
  else if n₂ = 0 ∧ n₃ = 1 ∧ n₄ = 1 then 9
  else if n₂ = 2 ∧ n₃ = 1 ∧ n₄ = 0 then 10
  else if n₂ = 1 ∧ n₃ = 1 ∧ n₄ = 1 then 11
  else if n₂ = 2 ∧ n₃ = 0 ∧ n₄ = 1 then 12
  else 0

/-- The group of a shape. -/
def sh_groupOfShape : ℕ → sh_Group
  | 1 => .p1 | 2 => .p2 | 3 => .p3 | 4 => .p48 | 5 => .p5 | 6 => .balP6 | 7 => .p7 | 8 => .p48
  | 9 => .p9 | 10 => .balP6 | 11 => .cat | 12 => .pseudo | _ => .p1

section Shape

variable {X : Type*} [DecidableEq X] {Y : Type*} [DecidableEq Y]

/-- The unlabelled rooted shape of a hierarchy `H` on five taxa (`sh_shapeOf`), read off its
numbers of clusters with two, three and four taxa, and whether a cluster with two taxa lies in one
with three. -/
def sh_shape (H : Finset (Finset X)) : ℕ :=
  sh_shapeOf #(H.filter fun A => #A = 2) #(H.filter fun A => #A = 3) #(H.filter fun A => #A = 4)
    (decide (∃ A ∈ H, ∃ B ∈ H, #A = 2 ∧ #B = 3 ∧ A ⊆ B))

/-- The shape group of a hierarchy on five taxa. -/
def sh_groupOf (H : Finset (Finset X)) : sh_Group :=
  sh_groupOfShape (sh_shape H)

omit [DecidableEq X] in
theorem sh_card_filter_relabel (e : X ≃ Y) (H : Finset (Finset X)) (k : ℕ) :
    #((relabelFamily e H).filter fun A => #A = k) = #(H.filter fun A => #A = k) := by
  unfold relabelFamily
  rw [filter_image, card_image_of_injective _ (map_injective e.toEmbedding)]
  congr 1
  exact filter_congr fun A _ => by rw [card_map]

omit [DecidableEq X] in
theorem sh_nested_relabel (e : X ≃ Y) (H : Finset (Finset X)) :
    (∃ A ∈ relabelFamily e H, ∃ B ∈ relabelFamily e H, #A = 2 ∧ #B = 3 ∧ A ⊆ B) ↔
      ∃ A ∈ H, ∃ B ∈ H, #A = 2 ∧ #B = 3 ∧ A ⊆ B := by
  simp only [relabelFamily, mem_image, exists_exists_and_eq_and, card_map, map_subset_map]

/-- The shape is invariant under relabelling the taxa. -/
theorem sh_shape_relabel (e : X ≃ Y) (H : Finset (Finset X)) :
    sh_shape (relabelFamily e H) = sh_shape H := by
  unfold sh_shape
  rw [sh_card_filter_relabel, sh_card_filter_relabel, sh_card_filter_relabel,
    decide_eq_decide.2 (sh_nested_relabel e H)]

/-- The shape group is invariant under relabelling the taxa. -/
theorem sh_groupOf_relabel (e : X ≃ Y) (H : Finset (Finset X)) :
    sh_groupOf (relabelFamily e H) = sh_groupOf H := by
  rw [sh_groupOf, sh_groupOf, sh_shape_relabel]

end Shape

/-- The representatives of the twelve rooted shapes on five taxa: `P₁, …, P₉` (Table 6), and the
balanced tree, the caterpillar and the pseudocaterpillar (Section 4.2). -/
def sh_reps : Finset (Finset (Finset (Fin 5))) :=
  {polytomy5 1, polytomy5 2, polytomy5 3, polytomy5 4, polytomy5 5, polytomy5 6, polytomy5 7,
    polytomy5 8, polytomy5 9, balanced5, caterpillar5, pseudocaterpillar5}

/-- The shapes of the representatives: `P_k` has the shape `k`, the balanced tree `10`, the
caterpillar `11` and the pseudocaterpillar `12`. -/
theorem sh_shape_reps : sh_shape (polytomy5 1) = 1 ∧ sh_shape (polytomy5 2) = 2 ∧
    sh_shape (polytomy5 3) = 3 ∧ sh_shape (polytomy5 4) = 4 ∧ sh_shape (polytomy5 5) = 5 ∧
    sh_shape (polytomy5 6) = 6 ∧ sh_shape (polytomy5 7) = 7 ∧ sh_shape (polytomy5 8) = 8 ∧
    sh_shape (polytomy5 9) = 9 ∧ sh_shape balanced5 = 10 ∧ sh_shape caterpillar5 = 11 ∧
    sh_shape pseudocaterpillar5 = 12 := by
  decide +kernel

/-! ### The rules of Appendix C -/

/-- The taxa that appear in no cherry of the gene trees `T_i`, `i ∈ S`. For a single gene tree
`T_i` this is the one taxon of `T_i` in no cherry. -/
def sh_noCherry (S : Finset ℕ) : Finset (Fin 5) :=
  univ.filter fun x => ∀ i ∈ S, ∀ A ∈ cls_cherries (T5 i), x ∉ A

/-- The gene trees neither in the least probable class nor most probable. For `P₅` and `P₇` they
are the gene trees of the two 2-element classes, or of the 4-element class into which these can
merge. -/
noncomputable def sh_middle (τ : SpeciesTree (Fin 5)) : Finset ℕ :=
  (Icc 1 15).filter fun i => i ∉ cls_leastClass τ ∧ i ∉ cls_mostProbable τ

/-- The number of gene trees `T_i`, `i ∈ S`, that have a cherry in common with another gene tree
`T_j`, `j ∈ S`. -/
def sh_cherryTrees (S : Finset ℕ) : ℕ :=
  #(S.filter fun i => ∃ j ∈ S, j ≠ i ∧ (cls_cherries (T5 i) ∩ cls_cherries (T5 j)).Nonempty)

/-- The rules of Appendix C (l. 943–971), in terms of the size `nC` of the least probable class
`𝒞`, the size `nC₂` of the class with the second smallest probability, whether the gene trees of
that class all have the same taxon in no cherry (`sameNoCherry`), and the number `nShared` of the
gene trees outside `𝒞` and the most probable class that have a cherry in common with another such
gene tree. `|𝒞| = 15`: `P₁`. `|𝒞| = 12`: `P₃` if the gene trees of the 3-element class have the
same taxon in no cherry, `P₂` otherwise. `|𝒞| = 10`: `P₅` if the gene trees of both 2-element
classes have a cherry in common (four such gene trees, also when the classes merge), `P₇`
otherwise (two). `|𝒞| = 8`: the pseudocaterpillar. `|𝒞| = 6`: the caterpillar, `P₉`, `P₄`/`P₈`
or balanced/`P₆` as the second class has two, three, six or four gene trees. -/
def sh_rules (nC nC₂ : ℕ) (sameNoCherry : Bool) (nShared : ℕ) : sh_Group :=
  if nC = 15 then .p1
  else if nC = 12 then (if sameNoCherry then .p3 else .p2)
  else if nC = 10 then (if nShared = 4 then .p5 else .p7)
  else if nC = 8 then .pseudo
  else if nC₂ = 2 then .cat
  else if nC₂ = 3 then .p9
  else if nC₂ = 6 then .p48
  else .balP6

/-- The shape group read off the classes of gene trees of `τ` by the rules of Appendix C. -/
noncomputable def sh_read (τ : SpeciesTree (Fin 5)) : sh_Group :=
  sh_rules #(cls_leastClass τ) #(cls_secondClass τ)
    (decide (∃ x : Fin 5, ∀ i ∈ cls_secondClass τ, sh_noCherry {i} = {x}))
    (sh_cherryTrees (sh_middle τ))

/-- The shape group read off the classes depends only on the distribution. -/
theorem sh_read_congr {τ τ' : SpeciesTree (Fin 5)} (h : τ.unrootedDist id = τ'.unrootedDist id) :
    sh_read τ = sh_read τ' := by
  unfold sh_read sh_middle
  rw [cls_leastClass_congr h, cls_secondClass_congr h, cls_mostProbable_congr h]

/-! ### Permuting labels -/

/-- Relabelling an unrooted tree relabels its cherries. -/
theorem sh_cherries_relabel (π : Equiv.Perm (Fin 5)) (T : Finset (Finset (Fin 5))) :
    cls_cherries (relabelFamily π T) = relabelFamily π (cls_cherries T) := by
  unfold cls_cherries relabelFamily
  rw [filter_image]
  congr 1
  exact filter_congr fun A _ => by rw [card_map]

section Relabel

/-! In this section the relabelling `π` maps each gene tree `T_i` (`i ∈ [1, 15]`) to `T_{p i}`,
and every `T_j` is such an image. -/

variable {π : Equiv.Perm (Fin 5)} {p : ℕ → ℕ}
  (hp : ∀ i ∈ Icc 1 15, p i ∈ Icc 1 15 ∧ relabelFamily π (T5 i) = T5 (p i))
  (hs : ∀ j ∈ Icc 1 15, ∃ i ∈ Icc 1 15, p i = j)

include hp in
theorem sh_cherries_idx {i : ℕ} (hi : i ∈ Icc 1 15) :
    cls_cherries (T5 (p i)) = relabelFamily π (cls_cherries (T5 i)) := by
  rw [← (hp i hi).2, sh_cherries_relabel]

include hp in
/-- The taxon in no cherry of `T_{p i}` is the image of that of `T_i`. -/
theorem sh_noCherry_idx {i : ℕ} (hi : i ∈ Icc 1 15) :
    sh_noCherry {p i} = (sh_noCherry {i}).map π.toEmbedding := by
  ext x
  simp only [sh_noCherry, mem_filter, mem_univ, true_and, mem_singleton, forall_eq,
    mem_map_equiv, sh_cherries_idx hp hi, relabelFamily, mem_image]
  constructor
  · intro h B hB hx
    exact h (B.map π.toEmbedding) ⟨B, hB, rfl⟩ (by rw [mem_map_equiv]; exact hx)
  · rintro h A ⟨B, hB, rfl⟩ hx
    rw [mem_map_equiv] at hx
    exact h B hB hx

include hp in
/-- `T_{p i}` and `T_{p j}` have a cherry in common iff `T_i` and `T_j` do. -/
theorem sh_share_idx {i j : ℕ} (hi : i ∈ Icc 1 15) (hj : j ∈ Icc 1 15) :
    (cls_cherries (T5 (p i)) ∩ cls_cherries (T5 (p j))).Nonempty ↔
      (cls_cherries (T5 i) ∩ cls_cherries (T5 j)).Nonempty := by
  rw [sh_cherries_idx hp hi, sh_cherries_idx hp hj, relabelFamily, relabelFamily,
    ← image_inter _ _ (map_injective π.toEmbedding), image_nonempty]

include hp hs in
theorem sh_injOn_idx : Set.InjOn p (Icc 1 15 : Finset ℕ) := by
  have him : (Icc 1 15).image p = Icc 1 15 := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hj
      exact (hp i hi).1
    · intro hj
      obtain ⟨i, hi, rfl⟩ := hs j hj
      exact mem_image_of_mem p hi
  rw [← card_image_iff, him]

include hp hs in
/-- The number of gene trees with a cherry in common with another one is invariant. -/
theorem sh_cherryTrees_image {S : Finset ℕ} (hS : S ⊆ Icc 1 15) :
    sh_cherryTrees (S.image p) = sh_cherryTrees S := by
  have hinj : Set.InjOn p S := (sh_injOn_idx hp hs).mono (coe_subset.2 hS)
  unfold sh_cherryTrees
  rw [filter_image, card_image_of_injOn (hinj.mono (coe_subset.2 (filter_subset _ _)))]
  congr 1
  refine filter_congr fun i hi => ?_
  simp only [mem_image, exists_exists_and_eq_and]
  constructor
  · rintro ⟨j, hj, hne, hsh⟩
    exact ⟨j, hj, fun h => hne (by rw [h]), (sh_share_idx hp (hS hi) (hS hj)).1 hsh⟩
  · rintro ⟨j, hj, hne, hsh⟩
    exact ⟨j, hj, fun h => hne (hinj hj hi h), (sh_share_idx hp (hS hi) (hS hj)).2 hsh⟩

include hp hs in
/-- The classes of the relabelled tree are the images of those of `τ`. -/
theorem sh_classes_idx (τ : SpeciesTree (Fin 5)) :
    cls_leastClass (τ.relabel π) = (cls_leastClass τ).image p ∧
      cls_secondClass (τ.relabel π) = (cls_secondClass τ).image p ∧
      cls_mostProbable (τ.relabel π) = (cls_mostProbable τ).image p := by
  have e := τ.relabel_relabel_symm π
  refine ⟨?_, ?_, ?_⟩
  · rw [cls_leastClass_relabel (τ.relabel π) π hp hs, e]
  · rw [cls_secondClass_relabel (τ.relabel π) π hp hs, e]
  · rw [cls_mostProbable_relabel (τ.relabel π) π hp hs, e]

include hp hs in
/-- The rules of Appendix C give the same group for `τ` and for `τ` relabelled by `π`. -/
theorem sh_read_relabel_idx (τ : SpeciesTree (Fin 5)) : sh_read (τ.relabel π) = sh_read τ := by
  obtain ⟨hL, hC, hM⟩ := sh_classes_idx hp hs τ
  have hinj := sh_injOn_idx hp hs
  have sL : cls_leastClass τ ⊆ Icc 1 15 := fun i hi => (cls_mem_leastClass.1 hi).1
  have sC : cls_secondClass τ ⊆ Icc 1 15 := fun i hi => (cls_mem_secondClass.1 hi).1
  have sM : cls_mostProbable τ ⊆ Icc 1 15 := fun i hi => (cls_mem_mostProbable.1 hi).1
  -- the sizes of the classes
  have cL : #(cls_leastClass (τ.relabel π)) = #(cls_leastClass τ) := by
    rw [hL, card_image_of_injOn (hinj.mono (coe_subset.2 sL))]
  have cC : #(cls_secondClass (τ.relabel π)) = #(cls_secondClass τ) := by
    rw [hC, card_image_of_injOn (hinj.mono (coe_subset.2 sC))]
  -- the taxa in no cherry of the gene trees of the second class
  have cP : (∃ x : Fin 5, ∀ i ∈ cls_secondClass (τ.relabel π), sh_noCherry {i} = {x}) ↔
      ∃ x : Fin 5, ∀ i ∈ cls_secondClass τ, sh_noCherry {i} = {x} := by
    rw [hC]
    simp only [forall_mem_image]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨π.symm x, fun i hi => ?_⟩
      have h := hx hi
      rw [sh_noCherry_idx hp (sC hi)] at h
      apply map_injective π.toEmbedding
      rw [h, map_singleton]
      simp
    · rintro ⟨y, hy⟩
      refine ⟨π y, fun i hi => ?_⟩
      rw [sh_noCherry_idx hp (sC hi), hy i hi, map_singleton]
      rfl
  -- the gene trees neither least nor most probable, and their common cherries
  have hMid : sh_middle (τ.relabel π) = (sh_middle τ).image p := by
    ext j
    simp only [sh_middle, mem_filter, mem_image, hL, hM]
    constructor
    · rintro ⟨hj, hjL, hjM⟩
      obtain ⟨i, hi, rfl⟩ := hs j hj
      exact ⟨i, ⟨hi, fun h => hjL ⟨i, h, rfl⟩, fun h => hjM ⟨i, h, rfl⟩⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hiL, hiM⟩, rfl⟩
      refine ⟨(hp i hi).1, ?_, ?_⟩
      · rintro ⟨k, hk, hki⟩
        exact hiL (hinj (sL hk) hi hki ▸ hk)
      · rintro ⟨k, hk, hki⟩
        exact hiM (hinj (sM hk) hi hki ▸ hk)
  have cS : sh_cherryTrees (sh_middle (τ.relabel π)) = sh_cherryTrees (sh_middle τ) := by
    rw [hMid]
    exact sh_cherryTrees_image hp hs (filter_subset _ _)
  unfold sh_read
  rw [cL, cC, cS, decide_eq_decide.2 cP]

end Relabel

/-- A transposition maps each gene tree `T_j` to a gene tree `T_k`. -/
theorem sh_swap_T5 : ∀ x y : Fin 5, ∀ j ∈ Icc 1 15, ∃ k ∈ Icc 1 15,
    relabelFamily (Equiv.swap x y) (T5 j) = T5 k := by
  decide +kernel

/-- Every relabelling maps each gene tree `T_i` to a gene tree `T_j` (induction on the
transpositions). -/
theorem sh_relabel_T5 (π : Equiv.Perm (Fin 5)) :
    ∀ i ∈ Icc 1 15, ∃ j ∈ Icc 1 15, relabelFamily π (T5 i) = T5 j := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => exact fun i hi => ⟨i, hi, relabelFamily_refl _⟩
  | swap_mul f x y _ ih =>
    intro i hi
    obtain ⟨j, hj, e1⟩ := ih i hi
    obtain ⟨k, hk, e2⟩ := sh_swap_T5 x y j hj
    exact ⟨k, hk, by rw [Equiv.Perm.mul_def, ← classify_relabelFamily_trans, e1, e2]⟩

/-- The gene trees `T₁, …, T₁₅` are distinct. -/
theorem sh_T5_injOn : ∀ i ∈ Icc 1 15, ∀ j ∈ Icc 1 15, T5 i = T5 j → i = j := by
  decide +kernel

/-- Every relabelling permutes the gene trees `T₁, …, T₁₅`. -/
theorem sh_exists_idx (π : Equiv.Perm (Fin 5)) :
    ∃ p : ℕ → ℕ, (∀ i ∈ Icc 1 15, p i ∈ Icc 1 15 ∧ relabelFamily π (T5 i) = T5 (p i)) ∧
      ∀ j ∈ Icc 1 15, ∃ i ∈ Icc 1 15, p i = j := by
  choose! p hp hp' using sh_relabel_T5 π
  refine ⟨p, fun i hi => ⟨hp i hi, hp' i hi⟩, ?_⟩
  have hinj : Set.InjOn p (Icc 1 15 : Finset ℕ) := fun i hi j hj hij =>
    sh_T5_injOn i hi j hj (relabelFamily_injective π (by rw [hp' i hi, hp' j hj, hij]))
  have him : (Icc 1 15).image p = Icc 1 15 :=
    eq_of_subset_of_card_le (fun j hj => by
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hj
      exact hp i hi) (by rw [card_image_of_injOn hinj])
  intro j hj
  rw [← him] at hj
  exact mem_image.1 hj

/-- The shape group read off the classes is invariant under relabelling the taxa. -/
theorem sh_read_relabel (τ : SpeciesTree (Fin 5)) (π : Equiv.Perm (Fin 5)) :
    sh_read (τ.relabel π) = sh_read τ := by
  obtain ⟨p, hp, hs⟩ := sh_exists_idx π
  exact sh_read_relabel_idx hp hs τ

/-! ### The rules on the representatives -/

/-- A set `C ⊆ [1, 15]` of equiprobable gene trees, less probable than all the others, is the least
probable class. -/
theorem sh_leastClass_eq {τ : SpeciesTree (Fin 5)} {C : Finset ℕ} {m : ℕ} (hC : C ⊆ Icc 1 15)
    (hm : m ∈ C) (heq : ∀ i ∈ C, u τ i = u τ m) (hlt : ∀ i ∈ Icc 1 15, i ∉ C → u τ m < u τ i) :
    cls_leastClass τ = C := by
  ext i
  rw [cls_mem_leastClass]
  constructor
  · rintro ⟨hi, h⟩
    by_contra hiC
    exact absurd (h m (hC hm)) (not_le.2 (hlt i hi hiC))
  · intro hiC
    refine ⟨hC hiC, fun j hj => ?_⟩
    rw [heq i hiC]
    by_cases hjC : j ∈ C
    · rw [heq j hjC]
    · exact (hlt j hj hjC).le

/-- A set `C ⊆ [1, 15]` of equiprobable gene trees, more probable than all the others, is the set
of the most probable gene trees. -/
theorem sh_mostProbable_eq {τ : SpeciesTree (Fin 5)} {C : Finset ℕ} {m : ℕ} (hC : C ⊆ Icc 1 15)
    (hm : m ∈ C) (heq : ∀ i ∈ C, u τ i = u τ m) (hlt : ∀ i ∈ Icc 1 15, i ∉ C → u τ i < u τ m) :
    cls_mostProbable τ = C := by
  ext i
  rw [cls_mem_mostProbable]
  constructor
  · rintro ⟨hi, h⟩
    by_contra hiC
    exact absurd (h m (hC hm)) (not_le.2 (hlt i hi hiC))
  · intro hiC
    refine ⟨hC hiC, fun j hj => ?_⟩
    rw [heq i hiC]
    by_cases hjC : j ∈ C
    · rw [heq j hjC]
    · exact (hlt j hj hjC).le

/-- Appendix C, `|𝒞| = 12`: `P₂` and `P₃` are told apart since "all gene trees in the 3-element
class for `P₃` have the same taxon not occurring in a cherry, while for `P₂` the gene trees in the
3-element class have different taxa in this role". On the representatives `P₂ = (a,b,c,(d,e))` and
`P₃ = ((a,b,c,d),e)` of Table 6 (classes from Table 7, `ac1_classes_P2`, `ac1_classes_P3`): both
have `|𝒞| = 12`, and the class with the second smallest probability is the 3-element class. -/
theorem sh_P2_P3_rule :
    (∀ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 2 →
      #(cls_leastClass σ) = 12 ∧ #(cls_secondClass σ) = 3 ∧
        ∀ i ∈ cls_secondClass σ, ∀ j ∈ cls_secondClass σ, i ≠ j →
          sh_noCherry {i} ≠ sh_noCherry {j}) ∧
    (∀ σ : SpeciesTree (Fin 5), σ.clusters = polytomy5 3 →
      #(cls_leastClass σ) = 12 ∧ #(cls_secondClass σ) = 3 ∧
        ∃ x : Fin 5, ∀ i ∈ cls_secondClass σ, sh_noCherry {i} = {x}) := by
  refine ⟨fun σ h => ?_, fun σ h => ?_⟩
  · obtain ⟨e1, e2⟩ := ac1_classes_P2 σ h
    rw [e1, e2]
    decide
  · obtain ⟨e1, e2⟩ := ac1_classes_P3 σ h
    rw [e1, e2]
    exact ⟨by decide, by decide, 4, by decide⟩

/-- Appendix C, `|𝒞| = 10`: `P₅ = ((a,b),(d,e),c)` and `P₇ = (((a,b),d,e),c)` are told apart "by
considering the two 2-element classes for both". For `P₅`, the gene trees of each of the classes
`{T₂, T₃}` and `{T₄, T₁₃}` have a cherry in common; for `P₇`, those of `{T₂, T₃}` have a cherry in
common, those of `{T₈, T₁₁}` do not (Table 7, with the inequalities of Table 6). The two classes
can merge into one 4-element class (`appendixC_degenerate`); in all cases their union consists of
the gene trees neither least nor most probable (`sh_middle`), and "counting the number of trees
with a cherry in common in the larger degenerate class" gives four for `P₅` and two for `P₇`. -/
theorem sh_P5_P7_rule (σ : SpeciesTree (Fin 5)) :
    (σ.clusters = polytomy5 5 →
      sh_middle σ = {2, 3, 4, 13} ∧ u σ 2 = u σ 3 ∧ u σ 4 = u σ 13 ∧
        (cls_cherries (T5 2) ∩ cls_cherries (T5 3)).Nonempty ∧
        (cls_cherries (T5 4) ∩ cls_cherries (T5 13)).Nonempty ∧
        sh_cherryTrees (sh_middle σ) = 4) ∧
    (σ.clusters = polytomy5 7 →
      sh_middle σ = {2, 3, 8, 11} ∧ u σ 2 = u σ 3 ∧ u σ 8 = u σ 11 ∧
        (cls_cherries (T5 2) ∩ cls_cherries (T5 3)).Nonempty ∧
        cls_cherries (T5 8) ∩ cls_cherries (T5 11) = ∅ ∧
        sh_cherryTrees (sh_middle σ) = 2) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- `P₅`: Table 7 and the inequalities `u₁ > u₂, u₄ > u₅` of Table 6
    obtain ⟨h12, h14, h25, h45⟩ := (table6 σ).2.2.2.1 h
    obtain ⟨-, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ :=
      rootingDist5_2_7 σ h
    have q3 : u σ 3 = u σ 2 := by rw [e3, e2]
    have q13 : u σ 13 = u σ 4 := by rw [e13, e4]
    have hL : cls_leastClass σ = {5, 6, 7, 8, 9, 10, 11, 12, 14, 15} := by
      refine sh_leastClass_eq (m := 5) (by decide) (by decide) ?_ ?_
      · intro i hi
        simp only [mem_insert, mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [e5, e6, e7, e8, e9, e10, e11, e12, e14, e15]
      · intro i hi hiC
        obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
        interval_cases i <;> first | exact (hiC (by decide)).elim | linarith
    have hM : cls_mostProbable σ = {1} := by
      refine sh_mostProbable_eq (m := 1) (by decide) (by decide) ?_ ?_
      · intro i hi
        rw [mem_singleton.1 hi]
      · intro i hi hiC
        obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
        interval_cases i <;> first | exact (hiC (by decide)).elim | linarith
    have hmid : sh_middle σ = {2, 3, 4, 13} := by
      unfold sh_middle
      rw [hL, hM]
      decide
    refine ⟨hmid, q3.symm, q13.symm, by decide, by decide, ?_⟩
    rw [hmid]
    decide
  · -- `P₇`: Table 7 and the inequalities `u₁ > u₂, u₈ > u₄` of Table 6
    obtain ⟨h12, h18, h24, h84⟩ := (table6 σ).2.2.2.2.2.1 h
    obtain ⟨-, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ :=
      rootingDist5_1_5 σ h
    have q3 : u σ 3 = u σ 2 := by rw [e3, e2]
    have q11 : u σ 11 = u σ 8 := by rw [e11, e8]
    have hL : cls_leastClass σ = {4, 5, 6, 7, 9, 10, 12, 13, 14, 15} := by
      refine sh_leastClass_eq (m := 4) (by decide) (by decide) ?_ ?_
      · intro i hi
        simp only [mem_insert, mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [e4, e5, e6, e7, e9, e10, e12, e13, e14, e15]
      · intro i hi hiC
        obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
        interval_cases i <;> first | exact (hiC (by decide)).elim | linarith
    have hM : cls_mostProbable σ = {1} := by
      refine sh_mostProbable_eq (m := 1) (by decide) (by decide) ?_ ?_
      · intro i hi
        rw [mem_singleton.1 hi]
      · intro i hi hiC
        obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
        interval_cases i <;> first | exact (hiC (by decide)).elim | linarith
    have hmid : sh_middle σ = {2, 3, 8, 11} := by
      unfold sh_middle
      rw [hL, hM]
      decide
    refine ⟨hmid, q3.symm, q11.symm, by decide, by decide, ?_⟩
    rw [hmid]
    decide

/-- The shape groups of the representatives. -/
theorem sh_groupOf_reps : sh_groupOf (polytomy5 1) = .p1 ∧ sh_groupOf (polytomy5 2) = .p2 ∧
    sh_groupOf (polytomy5 3) = .p3 ∧ sh_groupOf (polytomy5 4) = .p48 ∧
    sh_groupOf (polytomy5 5) = .p5 ∧ sh_groupOf (polytomy5 6) = .balP6 ∧
    sh_groupOf (polytomy5 7) = .p7 ∧ sh_groupOf (polytomy5 8) = .p48 ∧
    sh_groupOf (polytomy5 9) = .p9 ∧ sh_groupOf balanced5 = .balP6 ∧
    sh_groupOf caterpillar5 = .cat ∧ sh_groupOf pseudocaterpillar5 = .pseudo := by
  decide +kernel

/-- Appendix C, l. 943–971: on the representatives of the twelve shapes, the rules give the group of
the shape. The sizes of the least probable class and of the class with the second smallest
probability are those of `appendixC_leastClass`; `P₂` and `P₃` are told apart by
`sh_P2_P3_rule`, `P₅` and `P₇` by `sh_P5_P7_rule`. -/
theorem sh_read_rep (τ : SpeciesTree (Fin 5)) (hτ : τ.clusters ∈ sh_reps) :
    sh_read τ = sh_groupOf τ.clusters := by
  obtain ⟨c1, c2, c3, c5, c7, cp, cc, cb, c4, c6, c8, c9⟩ := appendixC_leastClass τ
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, gb, gc, gp⟩ := sh_groupOf_reps
  simp only [sh_reps, mem_insert, mem_singleton] at hτ
  rcases hτ with h | h | h | h | h | h | h | h | h | h | h | h
  · -- `P₁`: `|𝒞| = 15`
    have e : #(cls_leastClass τ) = 15 := c1 h
    rw [sh_read, e, h, g1]
    rfl
  · -- `P₂`: `|𝒞| = 12`, and the gene trees of the 3-element class have different taxa in no
    -- cherry
    obtain ⟨e, e2, hd⟩ := sh_P2_P3_rule.1 τ h
    have hn : ¬ ∃ x : Fin 5, ∀ i ∈ cls_secondClass τ, sh_noCherry {i} = {x} := by
      rintro ⟨x, hx⟩
      obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.1 (by omega : 1 < #(cls_secondClass τ))
      exact hd i hi j hj hij ((hx i hi).trans (hx j hj).symm)
    rw [sh_read, e, decide_eq_false hn, h, g2]
    rfl
  · -- `P₃`: `|𝒞| = 12`, and the gene trees of the 3-element class have the same taxon in no
    -- cherry
    obtain ⟨e, -, hx⟩ := sh_P2_P3_rule.2 τ h
    rw [sh_read, e, decide_eq_true hx, h, g3]
    rfl
  · -- `P₄`: `|𝒞| = 6`, `|𝒞₂| = 6`
    obtain ⟨e, e2⟩ := c4 h
    have e' : #(cls_leastClass τ) = 6 := e
    have e2' : #(cls_secondClass τ) = 6 := e2
    rw [sh_read, e', e2', h, g4]
    rfl
  · -- `P₅`: `|𝒞| = 10`, four gene trees with a cherry in common
    have e : #(cls_leastClass τ) = 10 := c5 h
    rw [sh_read, e, ((sh_P5_P7_rule τ).1 h).2.2.2.2.2, h, g5]
    rfl
  · -- `P₆`: `|𝒞| = 6`, `|𝒞₂| = 4`
    obtain ⟨e, e2⟩ := c6 h
    have e' : #(cls_leastClass τ) = 6 := e
    have e2' : #(cls_secondClass τ) = 4 := e2
    rw [sh_read, e', e2', h, g6]
    rfl
  · -- `P₇`: `|𝒞| = 10`, two gene trees with a cherry in common
    have e : #(cls_leastClass τ) = 10 := c7 h
    rw [sh_read, e, ((sh_P5_P7_rule τ).2 h).2.2.2.2.2, h, g7]
    rfl
  · -- `P₈`: `|𝒞| = 6`, `|𝒞₂| = 6`
    obtain ⟨e, e2⟩ := c8 h
    have e' : #(cls_leastClass τ) = 6 := e
    have e2' : #(cls_secondClass τ) = 6 := e2
    rw [sh_read, e', e2', h, g8]
    rfl
  · -- `P₉`: `|𝒞| = 6`, `|𝒞₂| = 3`
    obtain ⟨e, e2⟩ := c9 h
    have e' : #(cls_leastClass τ) = 6 := e
    have e2' : #(cls_secondClass τ) = 3 := e2
    rw [sh_read, e', e2', h, g9]
    rfl
  · -- the balanced tree: `|𝒞| = 6`, `|𝒞₂| = 4`
    obtain ⟨e, e2⟩ := cb h
    have e' : #(cls_leastClass τ) = 6 := e
    have e2' : #(cls_secondClass τ) = 4 := e2
    rw [sh_read, e', e2', h, gb]
    rfl
  · -- the caterpillar: `|𝒞| = 6`, `|𝒞₂| = 2`
    obtain ⟨e, e2⟩ := cc h
    have e' : #(cls_leastClass τ) = 6 := e
    have e2' : #(cls_secondClass τ) = 2 := e2
    rw [sh_read, e', e2', h, gc]
    rfl
  · -- the pseudocaterpillar: `|𝒞| = 8`
    have e : #(cls_leastClass τ) = 8 := cp h
    rw [sh_read, e, h, gp]
    rfl

/-! ### Every species tree -/

/-- Every species tree on five taxa is a relabelling of one of the twelve representatives: after
relabelling, it is a rooting of `U5 0`, `U5 1` or `U5 2` (`exists_equiv_unroot_eq_U5`,
`classify_mem_rootings5`), and each of these is a relabelling of a representative. -/
theorem sh_exists_relabel_rep (τ : SpeciesTree (Fin 5)) :
    ∃ π : Equiv.Perm (Fin 5), (τ.relabel π).clusters ∈ sh_reps := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U5 (Fintype.card_fin 5) τ
  have hR := classify_mem_rootings5 _ k hk he
  have key : ∀ (π : Equiv.Perm (Fin 5)) (R : Finset (Finset (Fin 5))),
      (τ.relabel e.symm).clusters = R → relabelFamily π R ∈ sh_reps →
      ∃ π' : Equiv.Perm (Fin 5), (τ.relabel π').clusters ∈ sh_reps := fun π R hR' hπ =>
    ⟨e.symm.trans π, by
      rw [SpeciesTree.relabel_clusters, ← classify_relabelFamily_trans,
        ← SpeciesTree.relabel_clusters, hR']
      exact hπ⟩
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · simp only [rootings5, mem_insert, mem_singleton] at hR
    rcases hR with h | h | h | h | h | h
    · exact key 1 _ h (by decide +kernel)
    · exact key (Equiv.swap 0 4) _ h (by decide +kernel)
    · exact key (Equiv.swap 1 4) _ h (by decide +kernel)
    · exact key (Equiv.swap 2 4) _ h (by decide +kernel)
    · exact key (Equiv.swap 3 4) _ h (by decide +kernel)
    · exact key 1 _ h (by decide +kernel)
  · simp only [rootings5, mem_insert, mem_singleton] at hR
    rcases hR with h | h | h | h | h | h | h | h
    · exact key (Equiv.swap 0 3 * Equiv.swap 1 4) _ h (by decide +kernel)
    · exact key (Equiv.swap 0 3 * Equiv.swap 1 4) _ h (by decide +kernel)
    · exact key (Equiv.swap 0 3 * Equiv.swap 1 4) _ h (by decide +kernel)
    · exact key (Equiv.swap 0 4 * Equiv.swap 1 3) _ h (by decide +kernel)
    · exact key (Equiv.swap 0 3 * Equiv.swap 1 4) _ h (by decide +kernel)
    · exact key 1 _ h (by decide +kernel)
    · exact key (Equiv.swap 2 3) _ h (by decide +kernel)
    · exact key (Equiv.swap 2 4) _ h (by decide +kernel)
  · simp only [rootings5, mem_insert, mem_singleton] at hR
    rcases hR with h | h | h | h | h | h | h | h | h | h
    · exact key 1 _ h (by decide +kernel)
    · exact key (Equiv.swap 3 4) _ h (by decide +kernel)
    · exact key (Equiv.swap 0 4 * Equiv.swap 1 3) _ h (by decide +kernel)
    · exact key (Equiv.swap 0 3 * Equiv.swap 1 4) _ h (by decide +kernel)
    · exact key 1 _ h (by decide +kernel)
    · exact key 1 _ h (by decide +kernel)
    · exact key (Equiv.swap 0 3 * Equiv.swap 1 4) _ h (by decide +kernel)
    · exact key 1 _ h (by decide +kernel)
    · exact key 1 _ h (by decide +kernel)
    · exact key (Equiv.swap 0 3 * Equiv.swap 1 4) _ h (by decide +kernel)

/-- Appendix C, l. 943–971: on every species tree on five taxa, the rules applied to the classes of
gene trees give the group of its shape. By permuting labels (`sh_read_relabel`,
`sh_groupOf_relabel`) this reduces to the representatives (`sh_read_rep`). -/
theorem sh_read_eq_groupOf (τ : SpeciesTree (Fin 5)) : sh_read τ = sh_groupOf τ.clusters := by
  obtain ⟨π, hπ⟩ := sh_exists_relabel_rep τ
  rw [← sh_read_relabel τ π, sh_read_rep _ hπ, SpeciesTree.relabel_clusters, sh_groupOf_relabel]

/-- Appendix C, l. 943–971: "At this point we have determined the rooted unlabeled topology of the
species tree from the 5-taxon gene tree classes, except for the `P₄` versus `P₈` case and the
balanced versus `P₆` case." Two species trees on five taxa with the same unrooted gene tree
distribution have the same shape group: both are the group read off the classes of gene trees
(`sh_read_eq_groupOf`). The unrooted species tree (Corollary 6) is not used. -/
theorem sh_group_eq {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 5)
    (σ σ' : SpeciesTree X) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    sh_groupOf σ.clusters = sh_groupOf σ'.clusters := by
  let e : X ≃ Fin 5 := Fintype.equivFinOfCardEq hX
  have hd := (SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e).2 h
  have h1 := sh_read_eq_groupOf (σ.relabel e)
  have h2 := sh_read_eq_groupOf (σ'.relabel e)
  rw [SpeciesTree.relabel_clusters, sh_groupOf_relabel] at h1 h2
  rw [← h1, ← h2, sh_read_congr hd]

end ADR11
