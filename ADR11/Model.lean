module

public import ADR11.SmallTrees

/-!
# Section 3: the multispecies coalescent model

* `rootedDist_nonneg`, `rootedDist_sum`, `unrootedDist_nonneg`, `unrootedDist_sum`: the model
  defines probability distributions on rooted and on unrooted gene trees (Section 1).
* `equation2`: Tavaré's formula [Tavaré 1984] for `g_ij(t)`, the probability that `i` lineages
  coalesce into `j` lineages within time `t` (`ADR11.coalescenceProb`).
* `coalescenceProb_nonneg`, `coalescenceProb_sum`: for `i > 1` and `t > 0`, the `g_ij(t)`,
  `j = 1, …, i`, form a probability distribution; `tendsto_coalescenceProb_one`:
  `g_i1(t) → 1` as `t → ∞`; `tendsto_coalescenceProb_self`: `g_ii(t) → 1` as `t → 0`;
  `coalescenceProb_self`: `g_ii(t) = exp(-i(i-1)t/2)`.
* `section3_example1`, `section3_example2`: the two worked examples of rooted gene tree
  probabilities in the caterpillar species tree `((((a,b):x,c):y,d):z,e)`.
* `equation3`: gene tree probabilities are sums, over finitely many coalescent histories, of a
  constant depending only on the topologies times a product of `g`'s, as in equation (3).
* `section3_polynomial`: rooted and unrooted gene tree probabilities are polynomials, with
  rational coefficients, in the transformed branch lengths `exp(-x_b)`.
-/

@[expose] public section

namespace ADR11

open Finset Real Filter Topology

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The multispecies coalescent defines a probability distribution on rooted gene trees: the
probabilities are nonnegative. -/
theorem rootedDist_nonneg {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) (G : Finset (Finset L)) : 0 ≤ σ.rootedDist s G := by
  sorry

/-- The multispecies coalescent defines a probability distribution on rooted gene trees: the
probabilities sum to `1`. -/
theorem rootedDist_sum {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X) (s : L → X) :
    ∑ G, σ.rootedDist s G = 1 := by
  sorry

/-- Section 1: the unrooted gene tree probabilities form a well-defined probability distribution:
they are nonnegative ... -/
theorem unrootedDist_nonneg {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) (T : Finset (Finset L)) : 0 ≤ σ.unrootedDist s T := by
  sorry

/-- ... and sum to `1`. -/
theorem unrootedDist_sum {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) : ∑ T, σ.unrootedDist s T = 1 := by
  sorry

/-- **Equation (2)** [Tavaré 1984]: for `1 ≤ j ≤ i` and `t > 0`,
`g_ij(t) = ∑_{k=j}^{i} exp(-k(k-1)t/2) (2k-1)(-1)^{k-j} / (j!(k-j)!(j+k-1)) ∏_{m=0}^{k-1}
(j+m)(i-m)/(i+m)`. -/
theorem equation2 (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (t : ℝ) (ht : 0 < t) :
    coalescenceProb i j t =
      ∑ k ∈ Icc j i, exp (-((k.choose 2 : ℕ) : ℝ) * t) *
        ((2 * k - 1) * (-1) ^ (k - j) / ((j.factorial : ℝ) * (k - j).factorial * (j + k - 1))) *
          ∏ m ∈ range k, (((j : ℝ) + m) * ((i : ℝ) - m) / ((i : ℝ) + m)) := by
  sorry

/-- The `g_ij(t)` are nonnegative. -/
theorem coalescenceProb_nonneg (i j : ℕ) (t : ℝ) (ht : 0 < t) : 0 ≤ coalescenceProb i j t := by
  sorry

/-- For `i > 1` and `t > 0`, the `g_ij(t)`, `j = 1, …, i`, form a probability distribution. -/
theorem coalescenceProb_sum (i : ℕ) (hi : 1 < i) (t : ℝ) (ht : 0 < t) :
    ∑ j ∈ Icc 1 i, coalescenceProb i j t = 1 := by
  sorry

/-- Given enough time, all lineages coalesce: `g_i1(t) → 1` as `t → ∞`, for `i > 1`. -/
theorem tendsto_coalescenceProb_one (i : ℕ) (hi : 1 < i) :
    Tendsto (coalescenceProb i 1) atTop (𝓝 1) := by
  sorry

/-- Over short times no coalescence is likely: `g_ii(t) → 1` as `t → 0⁺`. -/
theorem tendsto_coalescenceProb_self (i : ℕ) :
    Tendsto (coalescenceProb i i) (𝓝[>] 0) (𝓝 1) := by
  sorry

/-- `g_ii(t) = exp(-i(i-1)t/2)`. -/
theorem coalescenceProb_self (i : ℕ) (t : ℝ) (ht : 0 < t) :
    coalescenceProb i i t = exp (-((i : ℝ) * (i - 1) * t / 2)) := by
  sorry

/-- First worked example of Section 3: in the caterpillar species tree
`((((a,b):x,c):y,d):z,e)`, the rooted gene tree `((((B,E),A),C),D)` has probability
`X Y³ Z⁶ / 180`, where `X = e^{-x}`, `Y = e^{-y}`, `Z = e^{-z}`. -/
theorem section3_example1 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    σ.rootedDist id (hierarchyOf {{1, 4}, {0, 1, 4}, {0, 1, 2, 4}}) =
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 *
        exp (-σ.length {0, 1, 2, 3}) ^ 6 / 180 := by
  sorry

/-- Second worked example of Section 3: in the same caterpillar species tree, the rooted gene tree
`(((B,E),A),(C,D))` has probability `X Y³ Z³ / 54 - X Y³ Z⁶ / 540`. -/
theorem section3_example2 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    σ.rootedDist id (hierarchyOf {{1, 4}, {0, 1, 4}, {2, 3}}) =
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 *
          exp (-σ.length {0, 1, 2, 3}) ^ 3 / 54 -
        exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 *
          exp (-σ.length {0, 1, 2, 3}) ^ 6 / 540 := by
  sorry

/-- **Equation (3)** and the history decomposition [Degnan–Salter 2005]: for a species tree
topology `H` and a rooted gene tree `G`, there are finitely many coalescent histories `h`, with
constants `c(h)` and numbers `i(h,b) ≥ j(h,b)` of lineages entering and leaving each internal
population `b`, depending only on `H` and `G`, such that for every species tree with topology `H`,
`ℙ(G) = ∑_h c(h) ∏_b g_{i(h,b) j(h,b)}(x_b)`. -/
theorem equation3 (H : Finset (Finset X)) (G : Finset (Finset X)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℚ) (i j : ι → Finset X → ℕ),
      ∀ σ : SpeciesTree X, σ.clusters = H →
        σ.rootedDist id G =
          ∑ h : ι, (c h : ℝ) * ∏ b ∈ H with b ≠ univ ∧ 2 ≤ #b,
            coalescenceProb (i h b) (j h b) (σ.length b) := by
  sorry

/-- Gene tree probabilities, rooted and unrooted, are polynomials with rational coefficients in
the transformed branch lengths `X_b = exp(-x_b)`, depending only on the topologies. -/
theorem section3_polynomial (H : Finset (Finset X)) (G : Finset (Finset X)) :
    ∃ p q : MvPolynomial (Finset X) ℚ,
      ∀ σ : SpeciesTree X, σ.clusters = H →
        σ.rootedDist id G = MvPolynomial.aeval (fun b => exp (-σ.length b)) p ∧
        σ.unrootedDist id G = MvPolynomial.aeval (fun b => exp (-σ.length b)) q := by
  sorry

end ADR11
