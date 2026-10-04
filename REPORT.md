# Audit of the paper and the formalization

Paper: Elizabeth S. Allman, James H. Degnan, John A. Rhodes, *Identifying the rooted species tree
from the distribution of unrooted gene trees under the coalescent*, J. Math. Biol. 62 (2011)
833–862, [arXiv:0912.4472v2](https://arxiv.org/abs/0912.4472v2). The audit was made against the
arXiv LaTeX source of v2. That source continues after its first `\end{document}` with draft
material (proofs of the inequalities, a table of numerical examples) that is not part of the
paper; it is not used here. Section, result, equation and table numbers are the paper's, and
line numbers (l.) refer to the TeX source.

Status of the formalization:

- Every numbered result of the paper is proved: Propositions 1, 3, 7, 8 and 11, Lemmas 4 and 5,
  Corollaries 2, 6 and 10, and Theorem 9 (both parts), together with the displayed equations that
  the proofs use ((1)–(9) and (11)–(13)), Tables 1–7, and the unnumbered claims of Sections 1–5,
  except those listed in Section 9.
- The results that the paper cites and uses are proved too: Tavaré's formula (equation (2)) in
  [`ADR11/External/Tavare`](ADR11/External/Tavare), the reconstruction of unrooted trees from quartets (Steel 1992, also
  for nonbinary trees as in Bandelt–Dress 1986 and Semple–Steel 2003) in [`ADR11/External/Quartets`](ADR11/External/Quartets),
  and Cayley's count of rooted shapes in [`ADR11/External/Cayley`](ADR11/External/Cayley). Nothing is assumed: the
  formalization is unconditional.
- `lake build` succeeds with no `sorry` outside [`Challenge.lean`](Challenge.lean), no `axiom`, and no
  `native_decide`; [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration of the library, every
  numbered result and every theorem compared by Palomar's Comparator depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- Every proof follows the paper's argument, with one departure, forced by a gap of the paper: the
  choice of five taxa that locates the root on a pendant edge in Theorem 9, and in its extension in
  Proposition 11 (Section 7, E4). The route check (Section 8) confirms that every formal proof
  uses the results that the paper's proof cites; its two recorded differences are Proposition 11's
  reuse of the proofs, not the statements, of Theorem 9 and Corollary 10, as in the paper.
- [`Challenge.lean`](Challenge.lean) states the main results in the vocabulary of Mathlib; [`Solution.lean`](Solution.lean) proves them
  from the library, and Comparator accepts the pair (Lean's kernel and NanoDa).
- No result of the paper had to be corrected. A few statements make explicit an assumption that the
  paper leaves implicit: at least one sampled gene (that gene trees of positive probability are
  binary), a nonempty set of taxa `S` in Lemma 5 (for `σ⁺(S)` to exist), and the ranges of `n` in
  the counts of Section 1 (Section 6).

## 1. Summary

- **Errors.** Two slips, both outside the results: the Discussion states an inequality between
  two split probabilities the wrong way round (E5), and the "near the root" explanation for the
  pseudocaterpillar names the wrong population (E2). No result, formula or table contains an
  error: every explicit formula of the paper (Section 3, Section 4.1, Appendix B, Tables 5 and 7)
  agrees with the model, and every claimed inequality, equality class and invariant basis holds.
- **Gaps.** The claims that the inequalities (4)–(6) are the only ones rest on numerical examples
  that the paper does not give (E1); Lemma 5 is stated without proof (E3); the root-location
  argument of Theorem 9 uses a quartet that distinguishes the edge, which exists only for internal
  edges (E4); Proposition 11 is proved by a sketch (E6). All the statements hold.
- **Typos.** Twelve Newick strings with unbalanced parentheses, and a few misspellings (E7).
- **Missing hypotheses.** None.
- **Redundant hypotheses.** `t > 0` in equation (2) and two of the properties listed after it;
  `n ≥ 3` in Proposition 1 and Corollary 2; the standing binary assumption of Section 4, as the
  paper itself shows in Proposition 11 (Section 5).
- **Use of cited results.** Every cited result used in a proof is applied correctly, except that
  the quartet of Steel's Proposition 6 is also invoked for pendant edges, where it does not exist
  (E4).
- **Proofs.** Every proof follows the paper's, with one departure that E4 forces (Section 7).

## 2. Results from prior work and how the paper uses them

### Proved in `ADR11/External/`

| Result | Where the paper uses it | Source | Theorem in `External/` |
| --- | --- | --- | --- |
| The probability `g_ij(t)` that `i` lineages coalesce into `j` within time `t` | Equation (2), Section 3; the computations of Sections 4.1 and 4.2 and Appendices B, C | Tavaré 1984 | [`deathPow_eq_tavare`](ADR11/External/Tavare/Formula.lean#L133), [`deathProb_eq_tavare`](ADR11/External/Tavare/Formula.lean#L163); equation (2) is [`equation2`](ADR11/Model.lean#L64) |
| An unrooted tree is determined by its quartets; a quartet "distinguishes" each internal edge | Corollary 6; Theorem 9 (Steel's Proposition 6); Proposition 11 for nonbinary trees | Steel 1992; Bandelt–Dress 1986; Semple–Steel 2003, Thm 6.3.5 | [`mem_unroot_iff_quartets`](ADR11/External/Quartets/Steel.lean#L106), [`exists_distinguishing_quartet`](ADR11/External/Quartets/Steel.lean#L282) |
| There are 2, 5 and 12 rooted shapes on 3, 4 and 5 taxa | Section 5, proof of Proposition 11 (Appendix C) | Cayley 1857 | [`cayley_shapes`](ADR11/External/Cayley/Shapes.lean#L215) (no proof needs the count) |

In Theorem 9 the paper uses a quartet that "distinguishes `e`" (l.667) without saying more;
the formalization reads it as a quartet `aa'|bb'` for which `e` is the only edge of `ψ⁻`
separating `aa'` from `bb'` ([`exists_distinguishing_quartet`](ADR11/External/Quartets/Steel.lean#L282)), which is what the argument needs.
Corollary 6 combines the reconstruction with its own argument for the edge lengths ("each
internal edge of `ψ⁻` is the internal edge for some induced quartet tree"), which is
[`SpeciesTree.sameUnrootedMetricTree_of_restrict`](ADR11/Identifiability/Quartets.lean#L147) in [`ADR11/Identifiability/Quartets.lean`](ADR11/Identifiability/Quartets.lean).

### Cited results stated in the paper and proved as its results

| Result | Where | Source | In the formalization |
| --- | --- | --- | --- |
| Rooted gene trees on 3 taxa: `p₁ = 1 - (2/3)e^{-t}`, `p₂ = p₃ = (1/3)e^{-t}`; `t = -log((3/2)(1-p))` | Equation (1), Proposition 1 | Nei 1987; Wakeley 2008 | [`equation1`](ADR11/Introduction.lean#L29), [`equation1_iff`](ADR11/Introduction.lean#L52), [`introduction_tripleLength`](ADR11/Introduction.lean#L79) |
| Rooted triples determine the species tree | Proposition 1, Corollary 2 | Degnan et al. 2009 | [`proposition1`](ADR11/Introduction/Proposition1.lean#L503), [`corollary2`](ADR11/Introduction/Proposition1.lean#L513) |
| Gene tree probabilities as sums over coalescent histories | Equation (3) | Degnan–Salter 2005 | [`equation3`](ADR11/Model.lean#L136), [`section3_polynomial`](ADR11/Model.lean#L148) |
| `(2n−3)!!` rooted binary topologies | Section 1 | Felsenstein 2004 | [`section1_card_rooted`](ADR11/Introduction/Counts.lean#L759) |
| An unrooted gene tree occurs when one of its rooted versions occurs | Section 1 | Heled–Drummond 2010 | the definition [`SpeciesTree.unrootedDist`](Challenge.lean#L164) |

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| Each unrooted binary tree has `2n−3` rootings; there are `(2n−5)!!` unrooted binary trees | Section 1 (l.198) | [`section1_card_rootings`](ADR11/Introduction/Counts.lean#L775), [`section1_card_unrooted`](ADR11/Introduction/Counts.lean#L783) |
| Kingman's coalescent is consistent: the forest formed by a subset of the lineages is Kingman's coalescent on the subset | Lemma 5 ("clear from the structure of the coalescent model") | [`kingmanTransition_lump`](ADR11/MSC/Marginal.lean#L375), [`kingmanAbsorption_lump`](ADR11/MSC/Marginal.lean#L383), [`forestDist_comp_embedding`](ADR11/MSC/Marginal.lean#L505) |
| A sequence of populations with the same lineages acts as one population of the total length; populations above the most recent common ancestor merge into the root population | Lemma 5 | [`kingmanTransition_add`](ADR11/Coalescent/Factorization.lean#L338), [`kingmanTransition_mul_kingmanAbsorption`](ADR11/Coalescent/Absorption.lean#L161), [`SpeciesTree.rootedDist_restrict`](ADR11/MSC/Marginal.lean#L982) |
| The number of lineages and the sequence of merges are independent; the merges are uniform | Section 3 ("enumerating all possible specifications of branches…") | [`kingmanTransition_apply`](ADR11/Coalescent/Factorization.lean#L321) (factorization through the pure death process and the jump chain) |
| Relabelling taxa relabels the distribution ("permuting labels immediately gives the distribution for other choices", l.319) | Sections 4.1, 4.2 and Appendix C | [`SpeciesTree.unrootedDist_relabel`](ADR11/MSC/Relabel.lean#L436), [`forestDist_relabel`](ADR11/MSC/Relabel.lean#L290) |
| With one gene per taxon, pendant edge lengths do not matter | Section 2 | [`rootedDist_eq_of_sameRootedMetricTree`](ADR11/Model.lean#L158) |
| A branch of length 0 is a polytomy | Section 5 | [`forestDist_erase_of_len_eq_zero`](ADR11/MSC/Contract.lean#L228), [`section5_limit`](ADR11/Nonbinary.lean#L43) |

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Tavaré 1984 | Equation (2) | Correct: the paper's product form is equivalent to Tavaré's formula. |
| Nei 1987; Wakeley 2008 | Equation (1), Proposition 1 | Correct. |
| Degnan–Salter 2005 | Equation (3) | Correct. |
| Steel 1992, Proposition 6 | Theorem 9 | Applied loosely: the quartet distinguishing an edge exists for internal edges only, and the argument invokes it for every edge (E4). The conclusion holds. |
| Steel 1992 (quartets determine the tree) | Corollary 6 | Correct. |
| Bandelt–Dress 1986; Semple–Steel 2003, Thm 6.3.5 | Proposition 11 | Correct. |
| Cayley 1857 | Section 5, Appendix C | Correct. |
| Degnan et al. 2009 | Proposition 1 | Correct. |
| Felsenstein 2004 | Section 1 | Correct. |

The other citations give context and are not used in proofs: on incomplete lineage sorting and
inference methods, anomalous gene trees (Degnan–Rosenberg 2006), the multi-sample models of
gene tree probabilities (Takahata 1989; Rosenberg 2002; Degnan 2010), outgroups, molecular clocks,
invariants of sequence models, midpoint rooting, empirical data sets, and Singular.

## 3. Errors and gaps in the paper

**E1. Sections 4.2.1–4.2.3: the inequalities (4)–(6) are the only ones.** For each of the three
binary shapes the paper states that no other inequality `u_i > u_j` holds for all branch lengths.
For the balanced tree it says (l.460) "Numerical examples can be used to show that there are no
inequalities of the form `u_i > u_j` … that are not listed in (4)", but gives no example; for the
caterpillar it refers to "arguments similar to those for the balanced tree" (l.510); for the
pseudocaterpillar it gives no justification (l.551). The claims are true: every pair of classes
that the inequalities leave incomparable changes order for suitable branch lengths. The
formalization proves them with explicit branch lengths ([`equation4_exhaustive`](ADR11/FiveTaxa/Balanced.lean#L347),
[`equation5_exhaustive`](ADR11/FiveTaxa/Caterpillar.lean#L434), [`equation6_exhaustive`](ADR11/FiveTaxa/Pseudocaterpillar.lean#L363)).

**E2. Section 4.2.3, l.517–518: the wrong population.** For the pseudocaterpillar
`(((a,b),(d,e)),c)` the paper says that `T₁₅` "can be realized … by 1, 2, or 3 events occurring in
a specific order in the population ancestral to species `a,b,c`, and `d` but not to `e`". This
species tree has no such population; the population meant is the one ancestral to `a, b, d, e`
but not to `c`, as the order given next ("1) `BE` coalesce, 2) `ABE` coalesce, 3) `ABDE`
coalesce") confirms. The phrase repeats the caterpillar's (l.467–468). The explanation, and the
invariant `u₁₂ = u₁₅` it explains, are correct with the right population.

**E3. Lemma 5 is stated without proof.** The paper calls it "clear from the structure of the
coalescent model" (l.559). It needs the consistency of Kingman's coalescent under subsampling
(restricting the forest to a subset of the lineages lumps the chain) and the pruning of the
species tree: populations without sampled lineages are inert, populations in a chain with the same
lineages merge, and populations above the most recent common ancestor of `S` merge into the root
population. The lemma is true. Lean: [`lemma5`](ADR11/Identifiability/Lemma5.lean#L72), [`lemma5_rooted`](ADR11/Identifiability/Lemma5.lean#L84), from [`ADR11/MSC/Marginal.lean`](ADR11/MSC/Marginal.lean).

**E4. Theorem 9: no quartet distinguishes a pendant edge.** The proof considers "a specific edge
`e` of `ψ⁻`" (l.667) and, when the root `ρ` is not on `e`, takes "any set `Q ⊂ X` of four taxa which
distinguishes `e` [Steel 1992, Proposition 6]" and `x` with `S = Q ∪ {x}` rooted at `ρ`. The edge
`e` must range over pendant edges too, since `ρ` lies on a pendant edge whenever a child of the
root is a leaf; but a quartet tree has a single internal edge, which splits it 2|2, so no quartet
distinguishes a pendant edge. For a pendant edge `e` to a taxon `ℓ` (whose parent is then not `ρ`),
take `S` containing `ℓ`, a taxon of the sibling clade of `ℓ`, a taxon on the other side of `ρ`, and
two more taxa: `e` is an edge of `ψ⁻(S)`, and the root of `ψ⁺(S)` is `ρ`, which is not on `e`. The
rest of the argument is sound, and the theorem holds. The formalization follows the paper's
argument, with this repair for pendant edges ([`rl_exists_five_not_rootOn_pendant`](ADR11/Identifiability/Theorem9.lean#L45); Section 7),
which also serves the extension of Theorem 9 in Proposition 11.

**E5. Discussion, l.739: an inequality reversed.** "if the species tree is
`(((a,b):x,c):y,d):z,e)`, … Being able to determine that `e` is the outgroup would require
observing conflicting splits, such as that `ABD|CE` is more probable than `ABE|CD`." For this
species tree (with the parenthesis of E7 restored) the split `ABE|CD` is the more probable one: it
is displayed by `T₃`, `T₁₀`, `T₁₅`, and `ABD|CE` by `T₂`, `T₇`, `T₁₄`, and since `u₇ = u₁₀` and
`u₁₄ = u₁₅` by Table 2, equation (12) gives the difference `u₃ - u₂ = XY³(1 - Z⁶)/18 > 0`. This
agrees with the proof of Proposition 7, which uses `ℙ(T₃) > ℙ(T₂)` to recognize `e` as the outgroup
(l.602). The sentence is right with `d` and `e` exchanged, and the remark's point survives.
Lean: [`discussion_splits`](ADR11/Discussion.lean#L50).

**E6. Proposition 11 is proved by a sketch (Appendix C).** The class sizes, and the rules that
identify the shape and the labelling of each of the twelve rooted 5-taxon shapes from the
cherries of the trees in the classes, are asserted, with some cases outlined only ("by counting
the number of trees with a cherry in common in the larger degenerate class", l.965). The extension
of Theorem 9 is one sentence (l.995: "if the root of the species tree has degree greater than 2,
then its location will be identified by some 5-taxon subtree with the same property"), and it
inherits E4. All the stated cardinalities and rules hold, and the formal proof uses them in the
paper's order (shape, then labelling, then lengths): [`appendixC_leastClass`](ADR11/Nonbinary/AppendixC.lean#L770), [`table6`](ADR11/Nonbinary/AppendixC.lean#L671),
[`table7_classes`](ADR11/Nonbinary/AppendixC.lean#L749), [`appendixC_degenerate`](ADR11/Nonbinary/AppendixC.lean#L871), [`sh_P2_P3_rule`](ADR11/Nonbinary/FiveTaxa/Shapes.lean#L408), [`sh_P5_P7_rule`](ADR11/Nonbinary/FiveTaxa/Shapes.lean#L431), [`ac1_P3_outgroup`](ADR11/Nonbinary/FiveTaxa/StarOneSplit.lean#L68),
[`ac1_P7_outgroup`](ADR11/Nonbinary/FiveTaxa/StarOneSplit.lean#L82), [`ac1_P9_distinguished`](ADR11/Nonbinary/FiveTaxa/StarOneSplit.lean#L95), [`ac1_P9_outgroup`](ADR11/Nonbinary/FiveTaxa/StarOneSplit.lean#L106), [`ac1_P4_P8_rule`](ADR11/Nonbinary/FiveTaxa/StarOneSplit.lean#L121), [`ac2_T7_rule`](ADR11/Nonbinary/FiveTaxa/TwoSplits.lean#L127),
[`ac2_balanced_P6_rule`](ADR11/Nonbinary/FiveTaxa/TwoSplits.lean#L193), assembled in [`appC_sameRootedMetricTree`](ADR11/Nonbinary/FiveTaxa.lean#L39).

**E7. Typos.** Twelve Newick strings have unbalanced parentheses, each with an evident correction:
l.286 `(((a,b):x,c):y,d):z,e)` for `((((a,b):x,c):y,d):z,e)`; l.324 `(((a,b):x,(c,d):y)` for
`((a,b):x,(c,d):y)`; ll.350–353 `((a,b):x,c):y₁,d)` and three similar strings, for
`(((a,b):x,c):y₁,d)` and so on; l.620 `(((a,b):x,c):y),(d,e):z)` for `(((a,b):x,c):y,(d,e):z)`;
l.739 `(((a,b):x,c):y,d):z,e)`, `(((a,b),c),d),e)` and `(((a,b),c),e),d)`, each missing one opening
parenthesis; Table 6, `P₇ = ((a,b):x, d,e):z, c)` for `(((a,b):x,d,e):z,c)` and
`P₈ = (((a,b,c):y, (d,e):z)` for `((a,b,c):y,(d,e):z)` (the corrections agree with l.343 and
Table 7, where `P₇` is the pseudocaterpillar at `Y = 1` and `P₈` the balanced tree at `X = 1`).
Misspellings: "multspecies" (l.663), "inequalties" (l.510), "the the" (l.689), "one of more
species" (l.202), "kudriavzevil" for *kudriavzevii* (l.736), "HDP" for HPD (l.737); and both
`l_i` and `ℓ_i` for the number of lineages of taxon `i` (l.682, 689). The formalization uses the
corrected trees ([`ADR11/SmallTrees.lean`](ADR11/SmallTrees.lean)).

## 4. Missing hypotheses

None: no statement of the paper needs an added hypothesis. Apart from the slips E2 and E5, which
are not results, every statement holds under the paper's conventions: binary species trees in
Sections 1–4, a nonempty set of taxa `S` in Lemma 5 (for `σ⁺(S)` to exist), and `n ≥ 2` for the
count of rootings at l.198.

## 5. Redundant hypotheses

| Result | Hypothesis that is not needed | Lean |
| --- | --- | --- |
| Equation (2), `∑_j g_ij(t) = 1` and `g_ii(t) = e^{-i(i-1)t/2}` (l.272–276) | `t > 0`: these identities hold for every real `t` (only the nonnegativity of the `g_ij` needs `t ≥ 0`); also `i > 1` can be `i ≥ 1` in the second | Dropped from [`equation2`](ADR11/Model.lean#L64), [`coalescenceProb_sum`](ADR11/Model.lean#L80), [`coalescenceProb_self`](ADR11/Model.lean#L106) |
| Proposition 1, Corollary 2, and their extension in Section 5 | `n ≥ 3`: on fewer taxa the species tree has no internal edge | Dropped from [`proposition1`](ADR11/Introduction/Proposition1.lean#L503), [`corollary2`](ADR11/Introduction/Proposition1.lean#L513), [`section5_proposition1`](ADR11/Nonbinary/Triples.lean#L119), [`section5_corollary2`](ADR11/Nonbinary/Triples.lean#L126) |
| Section 4: Propositions 3, 7, 8, Corollaries 6, 10, Theorem 9 | the species tree is binary, a standing assumption of Section 4 (l.312), which the paper itself lifts in Proposition 11 (and Section 5 lifts it for Proposition 1 and Corollary 2) | Kept in the Section 4 statements, whose proofs follow the paper's binary arguments; the statements of Proposition 11 (`proposition11_*`) and [`section5_proposition1`](ADR11/Nonbinary/Triples.lean#L119), [`section5_corollary2`](ADR11/Nonbinary/Triples.lean#L126) drop it |

## 6. How the formalization reads the paper

**The model.** The paper describes the multispecies coalescent in words (Sections 1–3, with
references to Degnan–Salter 2005). The formalization defines it from Kingman's coalescent:

- A *forest* on a finite set `L` of gene lineages is a finite set of clusters (subsets of `L`);
  its *roots*, the maximal clusters, are the lineages present at a given moment. Kingman's
  coalescent is the continuous-time Markov chain on forests in which each pair of roots `A, B`
  merges at rate 1, adding the cluster `A ∪ B` ([`kingmanGenerator`](Challenge.lean#L78)). Its transition matrix over a
  time `t` is the matrix exponential `exp(tQ)` ([`kingmanTransition`](Challenge.lean#L85)). Above the root of the
  species tree lineages coalesce without a time limit: [`kingmanAbsorption`](Challenge.lean#L90) is the entrywise limit
  of `exp(tQ)` as `t → ∞`, which exists from every forest ([`tendsto_kingmanTransition`](ADR11/Coalescent/Absorption.lean#L110)).
- A *species tree* on the taxa `X` is a hierarchy of clusters of taxa (it contains `X` and every
  singleton, and any two clusters are nested or disjoint) with a length for every cluster other
  than `X`, positive on all of them ([`SpeciesTree`](Challenge.lean#L132)). A cluster `A` stands for the population on
  the edge above the node whose descendants are `A`, and `X` for the population above the root.
  The paper's binary trees are those with [`SpeciesTree.IsBinary`](Challenge.lean#L153): every cluster with at least two
  taxa is the union of two disjoint clusters.
- The paper leaves pendant edge lengths unspecified (l.181, 233). The formalization gives them
  positive lengths, which do not affect the distribution with one lineage per taxon
  ([`rootedDist_eq_of_sameRootedMetricTree`](ADR11/Model.lean#L158)) and are the pendant lengths that Corollary 10 recovers
  when several lineages are sampled.
- Lineages are sampled through a map `s : L → X` that gives the taxon of each lineage (`id` for one
  lineage per taxon, `Sigma.fst` for `ℓ_x` lineages from taxon `x`). [`forestDist`](Challenge.lean#L120) computes, by
  recursion over the hierarchy, the distribution of the forest at the top of each population: the
  forests leaving the child populations are combined independently, the lineages sampled in the
  population are added, and the population's Kingman transition is applied (its limit, above the
  root). `SpeciesTree.rootedDist σ s G` is the probability that the rooted gene tree, the set of
  clusters of the final forest, is `G`. `SpeciesTree.unrootedDist σ s T` sums it over the rooted
  trees `G` with `unroot G = T`, as the paper does in Section 1.
- A distribution is a function on all sets of clusters, binary trees or not. The model gives
  probability zero to everything except binary trees ([`rootedDist_support`](ADR11/Model.lean#L165)), which is the paper's
  remark that nonbinary gene trees have probability zero. That statement needs at least one
  lineage: with no lineage the gene tree is empty and has probability 1, and the empty set of
  clusters is not a tree. The formalization states it with `[Nonempty L]`; the paper always
  samples at least one lineage.

**Trees.** A rooted tree is its set of clusters, including the full set and the singletons. An
unrooted tree is the set of the sides of its splits, including the trivial splits ([`unroot`](Challenge.lean#L146)
removes the full set and adds the complements). The induced trees `σ⁺(S)` and `T(S)` of
Section 2 are [`SpeciesTree.restrict`](ADR11/Basic.lean#L99) and [`restrictSplits`](ADR11/Basic.lean#L36): the traces of the clusters, or of the
split sides, on `S`. The length of a cluster of `σ⁺(S)` is the sum of the lengths of the clusters
of `σ⁺` with that trace, which is the paper's suppression of nodes of degree 2. `σ⁺(S)` is defined
for nonempty `S` only, so [`lemma5`](ADR11/Identifiability/Lemma5.lean#L72) assumes that `S` is nonempty.

**What "determines" means.** "`ℙ_{σ⁺}` determines `σ⁺`" is read as injectivity: two species
trees with the same distribution of unrooted gene trees have the same rooted metric tree
([`SpeciesTree.SameRootedMetricTree`](Challenge.lean#L180): the same clusters, and the same length on every internal
cluster, that is every cluster other than `X` with at least two taxa). "Determines `σ⁻`" means the
same unrooted metric tree ([`SpeciesTree.SameUnrootedMetricTree`](Challenge.lean#L174): the same splits, and the same
length on every internal split, where the length of a split is the sum of the lengths of the
clusters that induce it, so that the two edges at the root add up when the root is suppressed).
"`σ⁺` is not identifiable" is the existence of two species trees with the same distribution and
different rooted metric trees. The recovery formulas of Section 4.1 and equations (7)–(9) are
stated as identities, together with the paper's claim that the arguments of the logarithms exceed
1.

**Small trees.** Statements about particular trees use the taxa `Fin 3`, `Fin 4` and `Fin 5`, with
`a, b, c, d, e` numbered `0, …, 4`. The species trees of Fig. 2, the fifteen unrooted 5-taxon gene
trees `T₁, …, T₁₅` of Table 5 and the nine nonbinary shapes `P₁, …, P₉` of Table 6 are given by
their clusters or splits ([`ADR11/SmallTrees.lean`](ADR11/SmallTrees.lean)), and `u σ i` is `u_i = ℙ_σ(T_i)`.
Newick strings with unbalanced parentheses are read as described in E7.

**Section 1.** The counts of rooted binary trees (`(2n−3)!!`, for `n ≥ 1`), of the rootings of an
unrooted binary tree (`2n−3`, for `n ≥ 2`) and of unrooted binary trees (`(2n−5)!!`, for `n ≥ 3`)
are stated for binary hierarchies on `Fin n`.

**Section 3.**

- `g_ij(t)` is defined from the model, as the probability that Kingman's coalescent started from
  `i` lineages has `j` lineages after time `t` ([`coalescenceProb`](ADR11/Basic.lean#L123)). Equation (2), Tavaré's
  formula, is then a theorem rather than a definition, and so are the properties the paper lists
  after it.
- Equation (3) is stated as the existence of a finite set of coalescent histories with positive
  rational coefficients `c(h)` and lineage counts `1 ≤ j_h(b) ≤ i_h(b) ≤ |b|` for each internal
  population `b`, such that `ℙ(G) = ∑_h c(h) ∏_b g_{i_h(b) j_h(b)}(x_b)` for all branch lengths.
  It does not identify the histories with the combinatorial objects of Degnan and Salter, which the
  paper uses only to conclude that the probabilities are polynomials in the `X_b = e^{-x_b}`;
  that conclusion is [`section3_polynomial`](ADR11/Model.lean#L148), with polynomials over `ℚ`.
- The two worked examples are stated for the caterpillar tree with its three internal lengths as
  parameters.

**Section 4.**

- Lemma 4 ("all coalescent events occur above the root") is stated for Kingman's coalescent
  absorbed from five singletons, which is that situation exactly. The remark after it, that the
  analogue fails for six taxa, is [`lemma4_six`](ADR11/FiveTaxa/Lemma4.lean#L314), with two explicit trees of different
  probabilities.
- Tables 1–3 are read as bases: the listed invariants are linearly independent and span the space
  of vectors `c` with `∑ c_i u_i = 0` for all branch lengths ([`linearInvariants`](ADR11/FiveTaxa/Basic.lean#L23)). The equality
  classes are stated as "`u_i = u_j` for all branch lengths if and only if `T_i` and `T_j` lie in
  the same class".
- Inequalities (4)–(6) and Table 6 use a list notation, such as `u₁ > u₂, u₄ > u₅ > u₇`, which is
  read as `u₁ > {u₂, u₄} > u₅ > u₇`: each element of a list exceeds each element of the next
  one. This is the reading under which the paper's consequences follow (for (4), that the
  4-element class `{T₅, T₆, T₉, T₁₂}` has the second smallest probability needs `u₂ > u₅` and
  `u₄ > u₅`), and under which no other inequality holds. All the inequalities hold in this
  reading. The claims that no other inequality holds are stated as: `u_i > u_j` for all branch
  lengths if and only if the classes of `T_i` and `T_j` are in the order generated by the
  inequalities.
- The statements about the sizes of the least probable classes take "the least probable class" to
  be the set of `T_i` of minimal probability, for given branch lengths, and claim it equals a
  fixed set for all branch lengths.
- Theorem 9 for `|X| = 4` says that `ℙ_{σ⁺}` determines "only" `σ⁻`. It is stated as the
  equivalence of equal distributions and equal unrooted metric trees ([`theorem9_four`](ADR11/Identifiability/Theorem9.lean#L241)), which
  contains both parts: `σ⁻` is determined, and every other species tree with the same `σ⁻` has the
  same distribution, so nothing more is determined.
- Corollary 10 samples `ℓ_x ≥ 1` lineages from taxon `x`; the lineages are the pairs `(x, k)` with
  `k < ℓ_x`.

**Section 5 and the binary assumption.** The paper obtains the probabilities for a nonbinary
species tree as limits of those of binary trees as branch lengths go to zero (l.699, 944), and
also speaks of the coalescent on a tree with polytomies. The formalization defines them by the
same model, in which a polytomy is a population with three or more children, proves that they
are these limits ([`section5_limit`](ADR11/Nonbinary.lean#L43), and [`lim_tendsto_rootedDist`](ADR11/MSC/Contract.lean#L416) for rooted gene trees), and
obtains the paper's explicit nonbinary probabilities from the binary formulas as the paper does:
the three-taxon star from equation (1) as `t → 0` ([`section5_threeTaxa`](ADR11/Nonbinary.lean#L151)), the nonbinary four-taxon
trees as contractions of the caterpillar ([`section5_fourTaxa`](ADR11/Nonbinary.lean#L227), [`ADR11/Nonbinary/FourTaxa.lean`](ADR11/Nonbinary/FourTaxa.lean)),
and Table 7 from Appendix B with lengths set to 0 ([`table7`](ADR11/Nonbinary/AppendixC.lean#L175)). Section 5's test for polytomies (l.706–707: "A species tree node has three
or more descendants if the three rooted gene trees obtained from sampling one gene from three
distinct descendants of the node have equal probabilities") is read with the three genes taken
below three distinct children of the node: with three leaves below one polytomous child of a
binary node, the triple probabilities are equal as well. [`section5_triples`](ADR11/Nonbinary/Triples.lean#L88) states it in this
form. Proposition 11 is stated without the binary assumption. The binary results of Section 4
keep it and are proved by the paper's binary arguments; Proposition 11 builds on them as the paper
does.

**Hypotheses can be met.** Every structure in the statements is inhabited: [`SpeciesTree.ofLengths`](ADR11/SmallTrees.lean#L116)
builds a species tree with any hierarchy and any positive internal lengths, and the existence
statements (the second part of Proposition 3, the claims that the inequalities (4)–(6) are the
only ones, the degenerate classes) exhibit explicit species trees. A species tree's fields are
the laws of a hierarchy with positive lengths; no field holds an assumed result.

**Results from prior work.** Tavaré's formula is proved by factoring the transition matrix through
the pure death process of the number of lineages and the uniform jump chain of merges
([`kingmanTransition_apply`](ADR11/Coalescent/Factorization.lean#L321)), and computing the death process's transition probabilities in closed
form, by a telescoping identity. The reconstruction of a tree from its quartets is proved for
hierarchies and split systems directly, for nonbinary trees as well.

## 7. Departures from the paper's proofs

Every proof follows the paper's argument except at one step.

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| Theorem 9 ([`theorem9`](ADR11/Identifiability/Theorem9.lean#L201)), and its extension in Proposition 11 ([`proposition11_theorem9`](ADR11/Nonbinary/Proposition11.lean#L80)) | To show that the root `ρ` does not lie on an edge `e`, take a quartet distinguishing `e` (Steel's Proposition 6) and a fifth taxon making `ρ` the most recent common ancestor (l.667–669) | The same for an internal edge; for the pendant edge of a taxon `ℓ`, five taxa: `ℓ`, another taxon of the child of the root containing `ℓ`, a taxon on the other side of the root, and two more ([`rl_exists_five_not_rootOn_pendant`](ADR11/Identifiability/Theorem9.lean#L45)) | No quartet distinguishes a pendant edge, and the root may lie on one; the step is repaired, the rest of the argument kept | E4 |

Some statements that the paper uses without proof or computes are proved by the means that
their nature allows: the explicit gene tree distributions of Section 4.1 and Appendix B by a
verified evaluation of the model ([`ADR11/Computation/`](ADR11/Computation), "permuting labels" for other labellings,
l.319), Lemma 5 from the consistency of Kingman's coalescent (E3), and the claims that no other
inequalities hold by explicit branch lengths (E1).

## 8. What each result depends on

[`scripts/Audit.lean`](scripts/Audit.lean) lists, for every result of the paper, the results from prior work that its
proof uses. In summary:

| Results | Results from prior work used |
| --- | --- |
| Corollary 6, Propositions 7, 8, Theorem 9, Corollary 10, and Proposition 11's versions of Corollary 6, Propositions 7, 8, Theorem 9, Corollary 10 | Tavaré 1984 ([`deathProb_eq_tavare`](ADR11/External/Tavare/Formula.lean#L163)); Steel 1992, Bandelt–Dress 1986 ([`mem_unroot_iff_quartets`](ADR11/External/Quartets/Steel.lean#L106), [`exists_distinguishing_quartet`](ADR11/External/Quartets/Steel.lean#L282)) |
| The Section 1 counts, `∑_j g_ij = 1`, the properties of `g_ii`, [`section5_limit`](ADR11/Nonbinary.lean#L43), the count of labelled four-taxon shapes, Table 4 | none |
| Every other result | Tavaré 1984 ([`deathProb_eq_tavare`](ADR11/External/Tavare/Formula.lean#L163)), through the transition probabilities of the coalescent |

Cayley's count of shapes ([`cayley_shapes`](ADR11/External/Cayley/Shapes.lean#L215)) is proved but used by no other result. Every result
depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).

The route check ([`scripts/route_check.py`](scripts/route_check.py), run in CI) compares, for every numbered result, the
numbered results that its formal proof uses with those that the paper's proof cites
([`docs/paper_routes.tsv`](docs/paper_routes.tsv), extracted from the TeX source). They agree, except for the two
differences recorded with their reasons in [`docs/route_differences.tsv`](docs/route_differences.tsv): Proposition 11 extends
the proofs of Theorem 9 and Corollary 10 to nonbinary trees, not their statements, which assume
binary trees, and the formal proofs apply the same arguments.

## 9. Not formalized

- The remark after Proposition 3 that ultrametric 4-taxon gene trees with known branch lengths
  determine `σ⁺` by midpoint rooting (Kim 1993): the model formalized here produces topological
  gene trees only.
- The remark after Theorem 9 that Theorem 9 gives another proof of Corollary 2 for `|X| ≥ 5`.
  Both statements are proved; the alternative derivation is not.
- The existence of nonlinear invariants of the gene tree distributions (l.214, 657, 734), which the
  paper mentions without stating them.
- The claims about which rooted versions of `T₁₅` can be realized with events below the root, in
  the caption of Fig. 1 (l.173).
- That the symmetry group of `σ⁺` is exactly the group generated by `(ab)` and `(de)` for generic
  lengths (l.397, 463, 515). The invariants of Tables 1–3 only need these permutations to be
  symmetries, which is proved ([`ADR11/FiveTaxa/Explanations.lean`](ADR11/FiveTaxa/Explanations.lean)).
- The Discussion's remarks on inference from finite data, the yeast and rice data sets, the
  likelihood (10) and its approximations, and the use of invariants to test the fit of the model
  are methodological; its claim about split probabilities is E5.
