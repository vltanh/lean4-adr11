module

public import ADR11.Computation.Caterpillar5

/-!
# Unrooted gene tree distributions of 5-taxon species trees

The fifteen unrooted gene tree probabilities `u σ i = ℙ_σ(T_i)` (`ADR11.u`, `1 ≤ i ≤ 15`) of the
twelve rooted 5-taxon species tree shapes of the paper, with one lineage per taxon, as
polynomials in the transformed lengths `e^{-x}` of the internal edges, verified by the engine of
`ADR11.Computation.Toolkit` (one certificate per shape):

* `u_bal5`, `u_cat5`, `u_pseudo5`: the balanced tree `(((a,b):x,c):y,(d,e):z)` (`balanced5`),
  the caterpillar `((((a,b):x,c):y,d):z,e)` (`caterpillar5`) and the pseudocaterpillar
  `(((a,b):x,(d,e):y):z,c)` (`pseudocaterpillar5`);
* `u_polytomy5`: the nine nonbinary representatives `P₁, …, P₉` of Table 6 (`polytomy5 k`).

Each states `u σ i = evalPoly σ.length (P i)` for `1 ≤ i ≤ 15`, where `P i` is a list of pairs
(coefficient, monomial) and a monomial is a list of pairs (code of a cluster `A`, exponent `e`)
standing for `(e^{-σ.length A})^e`. The codes are `3 = {0,1}`, `7 = {0,1,2}`, `15 = {0,1,2,3}`,
`24 = {3,4}`, `27 = {0,1,3,4}` (`decC_5_3`, `decC_5_7`, `decC_5_15`, `decC_5_24`, `decC_5_27`).
To get an explicit formula, rewrite with the lemma, then
`simp only [cat5Poly, evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, decC_5_3, …]`,
`push_cast` and `ring`; for instance `u σ 1` of the caterpillar is
`1 - 2/3 X - 2/3 Y + 1/3 X Y + 1/18 X Y³ + 1/90 X Y³ Z⁶` (equation (12)).

`u_eq_evalPoly_of_certAllB` is the general statement: one certificate gives the fifteen
probabilities of any 5-taxon tree shape. `T5_inj`: the fifteen gene trees `T_i` are distinct.
-/

@[expose] public section

namespace ADR11.Computation

open Finset Real

/-! ### The fifteen unrooted 5-taxon gene trees -/

/-- The codes of the unrooted 5-taxon tree with the nontrivial splits `B | Bᶜ` and `C | Cᶜ`,
`b` and `c` being the codes of `B` and `C`. -/
def t5Code (b c : ℕ) : List ℕ := unrootL 5 [1, 2, 4, 8, 16, b, c, 31]

/-- The codes of the paper's unrooted gene tree `T_i` (`ADR11.T5 i`). -/
def T5code : ℕ → List ℕ
  | 1 => t5Code 3 7 | 2 => t5Code 3 11 | 3 => t5Code 3 19 | 4 => t5Code 5 7
  | 5 => t5Code 5 13 | 6 => t5Code 5 21 | 7 => t5Code 9 11 | 8 => t5Code 9 13
  | 9 => t5Code 9 25 | 10 => t5Code 17 19 | 11 => t5Code 17 21 | 12 => t5Code 17 25
  | 13 => t5Code 6 7 | 14 => t5Code 10 11 | 15 => t5Code 18 19
  | _ => []

theorem decF_T5code : ∀ i ∈ Icc 1 15, decF 5 (T5code i) = T5 i := by decide +kernel

theorem valid_T5code : ∀ i ∈ Icc 1 15, Valid 5 (T5code i) := by decide +kernel

theorem T5code_sameSet : ∀ i ∈ Icc 1 15, ∀ j ∈ Icc 1 15,
    sameSet (T5code i) (T5code j) = true → i = j := by decide +kernel

/-- The fifteen unrooted gene trees `T_i` are distinct. -/
theorem T5_inj {i j : ℕ} (hi : i ∈ Icc 1 15) (hj : j ∈ Icc 1 15) (h : T5 i = T5 j) : i = j := by
  rw [← decF_T5code i hi, ← decF_T5code j hj,
    decF_eq_iff_sameSet (valid_T5code i hi) (valid_T5code j hj)] at h
  exact T5code_sameSet i hi j hj h

/-- The certificate targets for the fifteen gene trees `T_i`, `P i` giving `u σ i`. -/
def T5targets (P : ℕ → List (ℚ × List (ℕ × ℕ))) : List (List ℕ × List (ℚ × List (ℕ × ℕ))) :=
  (List.range' 1 15).map fun i => (T5code i, P i)

/-- One certificate gives the fifteen unrooted gene tree probabilities of a 5-taxon species tree:
`u σ i = evalPoly σ.length (P i)` for `1 ≤ i ≤ 15`. The certificate also checks that no other
unrooted gene tree is produced. -/
theorem u_eq_evalPoly_of_certAllB (σ : SpeciesTree (Fin 5)) {H : Finset (Finset (Fin 5))}
    (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB 5 H = true) (htop : T.code = 31)
    (P : ℕ → List (ℚ × List (ℕ × ℕ)))
    (hc : certAllB 5 (T.unrootedL 5 5 id) (T5targets P) = true) {i : ℕ} (hi : i ∈ Icc 1 15) :
    u σ i = evalPoly σ.length (P i) := by
  have hmem : ∀ j ∈ List.range' 1 15, j ∈ Icc 1 15 := by
    intro j hj
    rw [List.mem_range'_1] at hj
    rw [mem_Icc]
    omega
  rw [u, unrootedDist_eq_sum_targets σ hσ T hwf htop hc, T5targets, List.map_map]
  rw [show ((fun t : List ℕ × List (ℚ × List (ℕ × ℕ)) =>
      if decF 5 t.1 = T5 i then evalPoly σ.length t.2 else 0) ∘ fun j => (T5code j, P j)) =
      fun j => if decF 5 (T5code j) = T5 i then evalPoly σ.length (P j) else 0 from rfl]
  have hterm : ∀ j ∈ List.range' 1 15,
      (if decF 5 (T5code j) = T5 i then evalPoly σ.length (P j) else 0) =
        if j = i then evalPoly σ.length (P j) else 0 := by
    intro j hj
    rw [decF_T5code j (hmem j hj)]
    by_cases h : j = i
    · subst h
      simp
    · rw [ite_eq_right (fun h' => h (T5_inj (hmem j hj) hi h')), ite_eq_right h]
  rw [List.map_congr_left hterm, ← List.sum_toFinset _ List.nodup_range', Finset.sum_ite_eq',
    ite_eq_left (List.mem_toFinset.2 (List.mem_range'_1.2 (by rw [mem_Icc] at hi; omega)))]

/-- With a certificate, the whole unrooted gene tree distribution of a 5-taxon species tree, as a
function of the gene tree: only the fifteen `T_i` have positive probability. -/
theorem unrootedDist_eq_sum_T5 (σ : SpeciesTree (Fin 5)) {H : Finset (Finset (Fin 5))}
    (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB 5 H = true) (htop : T.code = 31)
    (P : ℕ → List (ℚ × List (ℕ × ℕ)))
    (hc : certAllB 5 (T.unrootedL 5 5 id) (T5targets P) = true) (U : Finset (Finset (Fin 5))) :
    σ.unrootedDist id U = ∑ i ∈ Icc 1 15, if T5 i = U then evalPoly σ.length (P i) else 0 := by
  have hmem : ∀ j ∈ List.range' 1 15, j ∈ Icc 1 15 := by
    intro j hj
    rw [List.mem_range'_1] at hj
    rw [mem_Icc]
    omega
  rw [unrootedDist_eq_sum_targets σ hσ T hwf htop hc U, T5targets, List.map_map]
  rw [show ((fun t : List ℕ × List (ℚ × List (ℕ × ℕ)) =>
      if decF 5 t.1 = U then evalPoly σ.length t.2 else 0) ∘ fun j => (T5code j, P j)) =
      fun j => if decF 5 (T5code j) = U then evalPoly σ.length (P j) else 0 from rfl]
  rw [List.map_congr_left (fun j hj => by rw [decF_T5code j (hmem j hj)]),
    ← List.sum_toFinset _ List.nodup_range']
  congr 1

/-- With a certificate, a 5-taxon unrooted gene tree that is none of the `T_i` has probability
`0`. -/
theorem unrootedDist_eq_zero_of_ne_T5 (σ : SpeciesTree (Fin 5)) {H : Finset (Finset (Fin 5))}
    (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB 5 H = true) (htop : T.code = 31)
    (P : ℕ → List (ℚ × List (ℕ × ℕ)))
    (hc : certAllB 5 (T.unrootedL 5 5 id) (T5targets P) = true) {U : Finset (Finset (Fin 5))}
    (hU : ∀ i ∈ Icc 1 15, T5 i ≠ U) : σ.unrootedDist id U = 0 := by
  rw [unrootedDist_eq_sum_T5 σ hσ T hwf htop P hc U]
  exact Finset.sum_eq_zero fun i hi => ite_eq_right (hU i hi)

/-! ### Codes of the clusters -/

theorem decC_5_3 : decC 5 3 = {0, 1} := by decide +kernel

theorem decC_5_7 : decC 5 7 = {0, 1, 2} := by decide +kernel

theorem decC_5_15 : decC 5 15 = {0, 1, 2, 3} := by decide +kernel

theorem decC_5_24 : decC 5 24 = {3, 4} := by decide +kernel

theorem decC_5_27 : decC 5 27 = {0, 1, 3, 4} := by decide +kernel

/-! ### Tree shapes -/

/-- The tree shape of the balanced tree `(((a,b),c),(d,e))`. -/
def bal5Shape : PTree :=
  .node 31 [.node 7 [.node 3 [.leaf 0, .leaf 1], .leaf 2], .node 24 [.leaf 3, .leaf 4]]

/-- The tree shape of the pseudocaterpillar `(((a,b),(d,e)),c)`. -/
def pseudo5Shape : PTree :=
  .node 31 [.node 27 [.node 3 [.leaf 0, .leaf 1], .node 24 [.leaf 3, .leaf 4]], .leaf 2]

/-- The tree shapes of the nonbinary representatives `P₁, …, P₉` (`polytomy5`). -/
def polytomy5Shape : ℕ → PTree
  | 1 => .node 31 [.leaf 0, .leaf 1, .leaf 2, .leaf 3, .leaf 4]
  | 2 => .node 31 [.leaf 0, .leaf 1, .leaf 2, .node 24 [.leaf 3, .leaf 4]]
  | 3 => .node 31 [.node 15 [.leaf 0, .leaf 1, .leaf 2, .leaf 3], .leaf 4]
  | 4 => .node 31 [.node 7 [.leaf 0, .leaf 1, .leaf 2], .leaf 3, .leaf 4]
  | 5 => .node 31 [.node 3 [.leaf 0, .leaf 1], .node 24 [.leaf 3, .leaf 4], .leaf 2]
  | 6 => .node 31 [.node 7 [.node 3 [.leaf 0, .leaf 1], .leaf 2], .leaf 3, .leaf 4]
  | 7 => .node 31 [.node 27 [.node 3 [.leaf 0, .leaf 1], .leaf 3, .leaf 4], .leaf 2]
  | 8 => .node 31 [.node 7 [.leaf 0, .leaf 1, .leaf 2], .node 24 [.leaf 3, .leaf 4]]
  | 9 => .node 31 [.node 15 [.node 7 [.leaf 0, .leaf 1, .leaf 2], .leaf 3], .leaf 4]
  | _ => .node 31 []

theorem bal5Shape_wfB : bal5Shape.wfB 5 balanced5 = true := by decide +kernel

theorem pseudo5Shape_wfB : pseudo5Shape.wfB 5 pseudocaterpillar5 = true := by decide +kernel

theorem polytomy5Shape_wfB : ∀ k ∈ Icc 1 9, (polytomy5Shape k).wfB 5 (polytomy5 k) = true := by
  decide +kernel

theorem polytomy5Shape_code (k : ℕ) : (polytomy5Shape k).code = 31 := by
  unfold polytomy5Shape
  split <;> rfl

/-! ### The three binary shapes -/

/-- `u₁, …, u₁₅` for the balanced tree, with `X = e^{-x}` (code `3`), `Y = e^{-y}` (code `7`),
`Z = e^{-z}` (code `24`): equation (11). -/
def bal5Poly : ℕ → List (ℚ × List (ℕ × ℕ))
  | 1 => [(1, []), (-2/3, [(3, 1)]), (-2/3, [(7, 1), (24, 1)]), (1/3, [(3, 1), (7, 1), (24, 1)]),
      (1/15, [(3, 1), (7, 3), (24, 1)])]
  | 2 | 3 => [(1/3, [(7, 1), (24, 1)]), (-1/6, [(3, 1), (7, 1), (24, 1)]),
      (-1/10, [(3, 1), (7, 3), (24, 1)])]
  | 4 | 13 => [(1/3, [(3, 1)]), (-1/3, [(3, 1), (7, 1), (24, 1)]),
      (1/15, [(3, 1), (7, 3), (24, 1)])]
  | 5 | 6 | 9 | 12 => [(1/6, [(3, 1), (7, 1), (24, 1)]), (-1/10, [(3, 1), (7, 3), (24, 1)])]
  | _ => [(1/15, [(3, 1), (7, 3), (24, 1)])]

/-- `u₁, …, u₁₅` for the caterpillar, with `X = e^{-x}` (code `3`), `Y = e^{-y}` (code `7`),
`Z = e^{-z}` (code `15`): equation (12). -/
def cat5Poly : ℕ → List (ℚ × List (ℕ × ℕ))
  | 1 => [(1, []), (-2/3, [(3, 1)]), (-2/3, [(7, 1)]), (1/3, [(3, 1), (7, 1)]),
      (1/18, [(3, 1), (7, 3)]), (1/90, [(3, 1), (7, 3), (15, 6)])]
  | 2 => [(1/3, [(7, 1)]), (-1/6, [(3, 1), (7, 1)]), (-1/9, [(3, 1), (7, 3)]),
      (1/90, [(3, 1), (7, 3), (15, 6)])]
  | 3 => [(1/3, [(7, 1)]), (-1/6, [(3, 1), (7, 1)]), (-1/18, [(3, 1), (7, 3)]),
      (-2/45, [(3, 1), (7, 3), (15, 6)])]
  | 4 | 13 => [(1/3, [(3, 1)]), (-1/3, [(3, 1), (7, 1)]), (1/18, [(3, 1), (7, 3)]),
      (1/90, [(3, 1), (7, 3), (15, 6)])]
  | 5 | 12 => [(1/6, [(3, 1), (7, 1)]), (-1/9, [(3, 1), (7, 3)]),
      (1/90, [(3, 1), (7, 3), (15, 6)])]
  | 6 | 9 => [(1/6, [(3, 1), (7, 1)]), (-1/18, [(3, 1), (7, 3)]),
      (-2/45, [(3, 1), (7, 3), (15, 6)])]
  | _ => [(1/18, [(3, 1), (7, 3)]), (1/90, [(3, 1), (7, 3), (15, 6)])]

/-- `u₁, …, u₁₅` for the pseudocaterpillar, with `X = e^{-x}` (code `3`), `Y = e^{-y}`
(code `24`), `Z = e^{-z}` (code `27`): equation (13). -/
def pseudo5Poly : ℕ → List (ℚ × List (ℕ × ℕ))
  | 1 => [(1, []), (-2/3, [(3, 1)]), (-2/3, [(24, 1)]), (4/9, [(3, 1), (24, 1)]),
      (-2/45, [(3, 1), (24, 1), (27, 6)])]
  | 2 | 3 => [(1/3, [(24, 1)]), (-5/18, [(3, 1), (24, 1)]), (1/90, [(3, 1), (24, 1), (27, 6)])]
  | 4 | 13 => [(1/3, [(3, 1)]), (-5/18, [(3, 1), (24, 1)]), (1/90, [(3, 1), (24, 1), (27, 6)])]
  | 8 | 11 => [(1/9, [(3, 1), (24, 1)]), (-2/45, [(3, 1), (24, 1), (27, 6)])]
  | _ => [(1/18, [(3, 1), (24, 1)]), (1/90, [(3, 1), (24, 1), (27, 6)])]

theorem bal5_cert : certAllB 5 (bal5Shape.unrootedL 5 5 id) (T5targets bal5Poly) = true := by
  decide +kernel

theorem cat5_cert : certAllB 5 (cat5Shape.unrootedL 5 5 id) (T5targets cat5Poly) = true := by
  decide +kernel

theorem pseudo5_cert :
    certAllB 5 (pseudo5Shape.unrootedL 5 5 id) (T5targets pseudo5Poly) = true := by
  decide +kernel

/-- The unrooted gene tree probabilities of the balanced species tree (equation (11)). -/
theorem u_bal5 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = balanced5) {i : ℕ}
    (hi : i ∈ Icc 1 15) : u σ i = evalPoly σ.length (bal5Poly i) :=
  u_eq_evalPoly_of_certAllB σ hσ bal5Shape bal5Shape_wfB rfl bal5Poly bal5_cert hi

/-- The unrooted gene tree probabilities of the caterpillar species tree (equation (12)). -/
theorem u_cat5 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) {i : ℕ}
    (hi : i ∈ Icc 1 15) : u σ i = evalPoly σ.length (cat5Poly i) :=
  u_eq_evalPoly_of_certAllB σ hσ cat5Shape cat5Shape_wfB rfl cat5Poly cat5_cert hi

/-- The unrooted gene tree probabilities of the pseudocaterpillar species tree (equation (13)). -/
theorem u_pseudo5 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) {i : ℕ}
    (hi : i ∈ Icc 1 15) : u σ i = evalPoly σ.length (pseudo5Poly i) :=
  u_eq_evalPoly_of_certAllB σ hσ pseudo5Shape pseudo5Shape_wfB rfl pseudo5Poly pseudo5_cert hi

/-! ### The nine nonbinary shapes (Table 7) -/

/-- `u₁, …, u₁₅` for `P₁ = (a,b,c,d,e)` (Table 7). -/
def polytomy5Poly₁ : ℕ → List (ℚ × List (ℕ × ℕ))
  | _ => [(1/15, [])]

/-- `u₁, …, u₁₅` for `P₂ = (a,b,c,(d,e):z)`, `Z` of code `24` (Table 7). -/
def polytomy5Poly₂ : ℕ → List (ℚ × List (ℕ × ℕ))
  | 1 | 4 | 13 => [(1/3, []), (-4/15, [(24, 1)])]
  | _ => [(1/15, [(24, 1)])]

/-- `u₁, …, u₁₅` for `P₃ = ((a,b,c,d):z,e)`, `Z` of code `15` (Table 7). -/
def polytomy5Poly₃ : ℕ → List (ℚ × List (ℕ × ℕ))
  | 3 | 6 | 9 => [(1/9, []), (-2/45, [(15, 6)])]
  | _ => [(1/18, []), (1/90, [(15, 6)])]

/-- `u₁, …, u₁₅` for `P₄ = ((a,b,c):y,d,e)`, `Y` of code `7` (Table 7). -/
def polytomy5Poly₄ : ℕ → List (ℚ × List (ℕ × ℕ))
  | 1 | 4 | 13 => [(1/3, []), (-1/3, [(7, 1)]), (1/15, [(7, 3)])]
  | 2 | 3 | 5 | 6 | 9 | 12 => [(1/6, [(7, 1)]), (-1/10, [(7, 3)])]
  | _ => [(1/15, [(7, 3)])]

/-- `u₁, …, u₁₅` for `P₅ = ((a,b):x,(d,e):y,c)`, `X`, `Y` of codes `3`, `24` (Table 7). -/
def polytomy5Poly₅ : ℕ → List (ℚ × List (ℕ × ℕ))
  | 1 => [(1, []), (-2/3, [(3, 1)]), (-2/3, [(24, 1)]), (2/5, [(3, 1), (24, 1)])]
  | 2 | 3 => [(1/3, [(24, 1)]), (-4/15, [(3, 1), (24, 1)])]
  | 4 | 13 => [(1/3, [(3, 1)]), (-4/15, [(3, 1), (24, 1)])]
  | _ => [(1/15, [(3, 1), (24, 1)])]

/-- `u₁, …, u₁₅` for `P₆ = (((a,b):x,c):y,d,e)`, `X`, `Y` of codes `3`, `7` (Table 7). -/
def polytomy5Poly₆ : ℕ → List (ℚ × List (ℕ × ℕ))
  | 1 => [(1, []), (-2/3, [(3, 1)]), (-2/3, [(7, 1)]), (1/3, [(3, 1), (7, 1)]),
      (1/15, [(3, 1), (7, 3)])]
  | 2 | 3 => [(1/3, [(7, 1)]), (-1/6, [(3, 1), (7, 1)]), (-1/10, [(3, 1), (7, 3)])]
  | 4 | 13 => [(1/3, [(3, 1)]), (-1/3, [(3, 1), (7, 1)]), (1/15, [(3, 1), (7, 3)])]
  | 5 | 6 | 9 | 12 => [(1/6, [(3, 1), (7, 1)]), (-1/10, [(3, 1), (7, 3)])]
  | _ => [(1/15, [(3, 1), (7, 3)])]

/-- `u₁, …, u₁₅` for `P₇ = (((a,b):x,d,e):z,c)`, `X`, `Z` of codes `3`, `27` (Table 7). -/
def polytomy5Poly₇ : ℕ → List (ℚ × List (ℕ × ℕ))
  | 1 => [(1/3, []), (-2/9, [(3, 1)]), (-2/45, [(3, 1), (27, 6)])]
  | 2 | 3 => [(1/3, []), (-5/18, [(3, 1)]), (1/90, [(3, 1), (27, 6)])]
  | 8 | 11 => [(1/9, [(3, 1)]), (-2/45, [(3, 1), (27, 6)])]
  | _ => [(1/18, [(3, 1)]), (1/90, [(3, 1), (27, 6)])]

/-- `u₁, …, u₁₅` for `P₈ = ((a,b,c):y,(d,e):z)`, `Y`, `Z` of codes `7`, `24` (Table 7). -/
def polytomy5Poly₈ : ℕ → List (ℚ × List (ℕ × ℕ))
  | 1 | 4 | 13 => [(1/3, []), (-1/3, [(7, 1), (24, 1)]), (1/15, [(7, 3), (24, 1)])]
  | 2 | 3 | 5 | 6 | 9 | 12 => [(1/6, [(7, 1), (24, 1)]), (-1/10, [(7, 3), (24, 1)])]
  | _ => [(1/15, [(7, 3), (24, 1)])]

/-- `u₁, …, u₁₅` for `P₉ = (((a,b,c):y,d):z,e)`, `Y`, `Z` of codes `7`, `15` (Table 7). -/
def polytomy5Poly₉ : ℕ → List (ℚ × List (ℕ × ℕ))
  | 1 | 4 | 13 => [(1/3, []), (-1/3, [(7, 1)]), (1/18, [(7, 3)]), (1/90, [(7, 3), (15, 6)])]
  | 2 | 5 | 12 => [(1/6, [(7, 1)]), (-1/9, [(7, 3)]), (1/90, [(7, 3), (15, 6)])]
  | 3 | 6 | 9 => [(1/6, [(7, 1)]), (-1/18, [(7, 3)]), (-2/45, [(7, 3), (15, 6)])]
  | _ => [(1/18, [(7, 3)]), (1/90, [(7, 3), (15, 6)])]

/-- `u₁, …, u₁₅` for the nonbinary representative `P_k` (Table 7). -/
def polytomy5Poly : ℕ → ℕ → List (ℚ × List (ℕ × ℕ))
  | 1 => polytomy5Poly₁ | 2 => polytomy5Poly₂ | 3 => polytomy5Poly₃ | 4 => polytomy5Poly₄
  | 5 => polytomy5Poly₅ | 6 => polytomy5Poly₆ | 7 => polytomy5Poly₇ | 8 => polytomy5Poly₈
  | 9 => polytomy5Poly₉ | _ => fun _ => []

theorem polytomy5_cert : ∀ k ∈ Icc 1 9,
    certAllB 5 ((polytomy5Shape k).unrootedL 5 5 id) (T5targets (polytomy5Poly k)) = true := by
  decide +kernel

/-- The unrooted gene tree probabilities of the nonbinary representatives `P₁, …, P₉`
(Table 7). -/
theorem u_polytomy5 {k : ℕ} (hk : k ∈ Icc 1 9) (σ : SpeciesTree (Fin 5))
    (hσ : σ.clusters = polytomy5 k) {i : ℕ} (hi : i ∈ Icc 1 15) :
    u σ i = evalPoly σ.length (polytomy5Poly k i) :=
  u_eq_evalPoly_of_certAllB σ hσ (polytomy5Shape k) (polytomy5Shape_wfB k hk)
    (polytomy5Shape_code k) (polytomy5Poly k) (polytomy5_cert k hk) hi

end ADR11.Computation
