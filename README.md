# Identifying the rooted species tree from unrooted gene trees, in Lean 4

A formalization in Lean 4 and Mathlib of

> Elizabeth S. Allman, James H. Degnan, John A. Rhodes, *Identifying the rooted species tree from
> the distribution of unrooted gene trees under the coalescent*, J. Math. Biol. 62 (2011)
> 833–862, [doi:10.1007/s00285-010-0355-7](https://doi.org/10.1007/s00285-010-0355-7),
> [arXiv:0912.4472v2](https://arxiv.org/abs/0912.4472v2).

Under the multispecies coalescent, gene trees evolve inside a species tree: lineages coalesce by
Kingman's coalescent within each ancestral population. Rooted gene trees determine the rooted
species tree, but in practice gene trees are often inferred without their roots. The paper shows
that the distribution of *unrooted* topological gene trees, with one lineage sampled per taxon,
still determines the rooted species tree and all its internal branch lengths when there are at
least five taxa (Theorem 9), while for four taxa it determines only the unrooted species tree
(Proposition 3). With several lineages sampled from some taxa, fewer taxa suffice and the
corresponding pendant branch lengths are determined too (Corollary 10), and all of this holds for
nonbinary species trees as well (Proposition 11). The proofs rest on explicit formulas for the
gene tree probabilities of all 5-taxon species trees, their linear invariants and inequalities,
and a reduction of the general case to five taxa by marginalization.

## What is proved

- **Every result of the paper**: Propositions 1, 3, 7, 8 and 11, Lemmas 4 and 5, Corollaries 2, 6
  and 10, Theorem 9, the displayed equations that the proofs use, Tables 1–7, and the unnumbered
  claims of Sections 1–5, among them the four-taxon formulas, the five rooted species trees with
  one unrooted distribution, the bases of linear invariants and the inequalities between gene tree
  probabilities with the claims that there are no others, and the discussion's comparison of two
  split probabilities. The report lists them all ([`REPORT.md`](REPORT.md), Section 8).
- **The results the paper cites and uses**, in [`ADR11/External/`](ADR11/External): Tavaré's
  formula for the number of lineages of Kingman's coalescent (equation (2)), the reconstruction of
  unrooted trees from their quartets (Steel 1992; Bandelt–Dress 1986 for nonbinary trees), and
  Cayley's count of rooted tree shapes. The formalization assumes nothing: it is unconditional.
- **The model itself.** Kingman's coalescent on forests of lineages is defined by its generator,
  its transition probabilities by the matrix exponential, and the multispecies coalescent by a
  recursion over the species tree. Facts the paper uses as evident, such as the consistency of the
  coalescent under subsampling (Lemma 5) and the limit of a polytomy as a branch length tends to
  zero, are proved from these definitions.
- **The paper's arguments.** Each proof follows the paper's proof: the same intermediate claims,
  case distinctions and cited results, with one departure forced by a gap of the paper (the
  report's Section 7). [`scripts/route_check.py`](scripts/route_check.py) checks in CI that every
  formal proof of a numbered result uses the results that the paper's proof cites
  ([`docs/paper_routes.tsv`](docs/paper_routes.tsv), extracted from the TeX source; the two
  reviewed differences are in [`docs/route_differences.tsv`](docs/route_differences.tsv)).
- `lake build` succeeds with no `sorry` outside [`Challenge.lean`](Challenge.lean), no `axiom` and
  no `native_decide`. [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration of
  the library, every result of the paper and every compared theorem depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and prints the table of which cited results each paper
  result uses: `lake env lean scripts/Audit.lean`.

## The main results

[`Challenge.lean`](Challenge.lean) states them with the model's definitions, in Mathlib's
vocabulary; [`Solution.lean`](Solution.lean) proves them from the library.

| Theorem | Statement |
| --- | --- |
| [`ADR11.Challenge.theorem9`](Challenge.lean#L235) | Theorem 9: for binary species trees on at least five taxa, with one lineage per taxon, equal distributions of unrooted gene trees imply the same rooted topology and the same internal branch lengths. |
| [`ADR11.Challenge.theorem9_four`](Challenge.lean#L242) | Theorem 9, four taxa: two binary species trees give the same distribution of unrooted gene trees if and only if they have the same unrooted metric tree. |
| [`ADR11.Challenge.proposition3`](Challenge.lean#L249) | Proposition 3: on four taxa the unrooted metric species tree is determined, and the rooted one is not. |
| [`ADR11.Challenge.corollary10`](Challenge.lean#L260) | Corollary 10: with `ℓ_x ≥ 1` lineages from each taxon `x`, if `\|X\| ≥ 4` and some `ℓ_x ≥ 2`, or `\|X\| = 3` and two of them are, the distribution determines the rooted species tree, its internal branch lengths, and the pendant length of every taxon with `ℓ_x ≥ 2`. |
| [`ADR11.Challenge.proposition11_theorem9`](Challenge.lean#L270), [`ADR11.Challenge.proposition11_theorem9_four`](Challenge.lean#L275), [`ADR11.Challenge.proposition11_corollary10`](Challenge.lean#L280) | Proposition 11: the same results for species trees that need not be binary. |
| [`ADR11.Challenge.unrootedDist_nonneg`](Challenge.lean#L197), [`ADR11.Challenge.unrootedDist_sum`](Challenge.lean#L202) | The model's gene tree probabilities form a probability distribution. |
| [`ADR11.Challenge.fourTaxa_balanced`](Challenge.lean#L209), [`ADR11.Challenge.fourTaxa_caterpillar`](Challenge.lean#L222) | The four-taxon formulas of Section 4.1, which tie the definitions to known values: for `((a,b):x,(c,d):y)` the unrooted gene tree `AB\|CD` has probability `1 − (2/3)e^{−(x+y)}` and the other two `(1/3)e^{−(x+y)}`; for `(((a,b):x,c):y,d)`, `1 − (2/3)e^{−x}` and `(1/3)e^{−x}`. |

The Challenge's module docstring explains the conventions: a rooted tree is its set of clusters,
an unrooted tree the set of the sides of its splits, and a species tree carries a positive length
on every edge, pendant edges included, as Corollary 10 needs.

## Palomar

The project is packaged for the [Palomar](https://palomar-registry.org) registry:
[`Challenge.lean`](Challenge.lean) (the statements, with `sorry`), [`Solution.lean`](Solution.lean)
(the same statements, proved), [`comparator.json`](comparator.json) and
[`formalization.yaml`](formalization.yaml). The definitions that the statements need are kept
between two marker comments in [`ADR11/Defs.lean`](ADR11/Defs.lean) and copied verbatim into the
Challenge by [`scripts/sync_challenge_defs.py`](scripts/sync_challenge_defs.py). To check the pair
locally, in a bubblewrap sandbox:

```sh
lake env lake comparator --config=comparator.json
```

## Audit summary

The full audit is in [`REPORT.md`](REPORT.md).

- **Errors.** Two slips, neither in a result: the Discussion states an inequality between split
  probabilities the wrong way round (E5), and an explanation of an invariant names the wrong
  population (E2). No result, formula or table of the paper is wrong.
- **Gaps.** The claims that the inequalities (4)–(6) are the only ones rest on numerical examples
  that the paper does not give (E1); Lemma 5 is stated without proof (E3); the root-location
  argument of Theorem 9 needs a separate step for pendant edges (E4); Proposition 11 has a
  sketched proof (E6). All the statements hold.
- **Typos.** Twelve Newick strings with unbalanced parentheses, and a few misspellings (E7).
- **Missing hypotheses.** None.
- **Redundant hypotheses.** `t > 0` in equation (2); `n ≥ 3` in Proposition 1 and Corollary 2;
  the binary assumption of Section 4, as the paper itself shows in Proposition 11.
- **Use of cited results.** All correct, except that the quartet of Steel's Proposition 6 is
  invoked for pendant edges, where it does not exist (E4).
- **Proofs.** Every proof follows the paper's argument, except one step forced by E4: in
  Theorem 9, the five taxa that locate the root on a pendant edge are chosen differently, since no
  quartet distinguishes a pendant edge (the report's Section 7).

## Credits

The formalization, the audit of the paper and the packaging were made by Claude Opus 5.5
(`claude-opus-5-5`, Anthropic) in Claude Code 2.1.288 (VS Code extension), from the paper's arXiv
source, a request naming the paper and one later message asking to continue, under the direction
of The-Anh Vu-Le. The work followed the
procedure of the skill [`formalize-math-paper`](https://github.com/vltanh/formalize-math-paper),
version 1.4.0. The skill was updated to that version during the run; its rule that every proof
follow the paper's own argument led to a second phase, in which the proofs of Propositions 3, 7, 8
and 11, Corollaries 6 and 10, Theorem 9, Lemma 4 and Tables 1–3 were rewritten along the paper's
arguments and compared with them by independent readers.

From the session transcript:

- **Elapsed time:** from 2026-10-03 13:25 to 19:51 (UTC−5), 6.4 hours, from the start to the
  commit that completes the audit report.
- **Sub-agents:** 32, at most 7 at a time, 2 of them resumed for follow-up work: 1 reviewed the
  statements against the TeX source before any proof was written, 28 wrote proofs (the model and
  its infrastructure, the paper's results, then the rewrite along the paper's arguments), and 3
  read independently (one checked the audit's findings against the TeX source, two compared the
  formal proofs with the paper's). Their total working time was 14.6 hours.
- **Effort:** the sub-agents made 2,084 model calls and 2,287 tool calls, with 5.10 M output
  tokens, 13.08 M input tokens (uncached input and cache writes) and 470 M cache reads; the main
  session made 492 model calls and 502 tool calls, with 1.02 M output tokens, 2.10 M input tokens
  and 268 M cache reads.

## Related work

The question of what gene tree distributions reveal about species trees goes back to the
probabilities of rooted gene trees under the multispecies coalescent (Pamilo–Nei 1988; Degnan and
Salter 2005) and to the identifiability of species trees from rooted triples (Degnan et al.
2009), which the paper cites. Its four-taxon result, that the most probable unrooted quartet gene
tree displays the species tree's quartet, is used to prove the statistical consistency of
quartet-based species tree methods such as ASTRAL (Mirarab et al. 2014).

We found no earlier formalization of this paper or of its results. The Lean library
[SauersML/Descent](https://github.com/SauersML/Descent) formalizes parts of coalescent theory,
including the probability of discordance of a three-taxon rooted gene tree; it has no
multispecies coalescent and no unrooted gene trees, and it was not used here.

## Building

```sh
lake exe cache get    # download Mathlib's build outputs
lake build            # build the library, the Challenge and the Solution
lake env lean scripts/Audit.lean    # axiom and dependency audit
```

The toolchain is Lean `v4.35.0-rc3` with Mathlib's tag `v4.35.0-rc3`. From a fresh clone, the
build takes about four minutes on a 20-core machine after downloading Mathlib's cache.

Two Lean files are generated, and their generators are in [`scripts/`](scripts):

- [`ADR11/AppendixA.lean`](ADR11/AppendixA.lean), Tables 4 and 5, from the paper's TeX source:
  `python3 scripts/gen_appendixA.py PAPER.tex > ADR11/AppendixA.lean`;
- [`ADR11/Rootings/Statements.lean`](ADR11/Rootings/Statements.lean), the gene tree
  distributions of all rootings of the 4- and 5-taxon unrooted trees, computed exactly by an
  independent implementation of the model ([`scripts/msc_model.py`](scripts/msc_model.py), which
  needs `sympy`): `python3 scripts/gen_rootings.py > ADR11/Rootings/Statements.lean`.

After editing the code, rerun the route check (`python3 scripts/route_check.py check
docs/paper_routes.tsv --accept docs/route_differences.tsv`, after the audit, which writes
`.lake/route_deps.tsv`), update the documentation's links with `python3 scripts/linkify_docs.py`
(after `lake build`), and check the Markdown tables with
`python3 scripts/check_md_tables.py README.md REPORT.md`. The routes of the paper's proofs were
extracted with `python3 scripts/route_check.py extract PAPER.tex > docs/paper_routes.tsv` from the
published part of the arXiv source (its first 1077 lines; the rest is draft material).

## Layout

| Module | Content |
| --- | --- |
| [`ADR11.Defs`](ADR11/Defs.lean) | The model: forests and Kingman's coalescent, species trees, the multispecies coalescent, unrooted trees, identifiability (shared with the Challenge) |
| [`ADR11.Basic`](ADR11/Basic.lean), [`ADR11.SmallTrees`](ADR11/SmallTrees.lean) | Induced trees `σ(S)` and `T(S)`, `g_ij`, rooted triples; the paper's named small trees and `T₁, …, T₁₅` |
| [`ADR11.Introduction`](ADR11/Introduction.lean), [`ADR11.Introduction.Proposition1`](ADR11/Introduction/Proposition1.lean), [`ADR11.Introduction.Counts`](ADR11/Introduction/Counts.lean) | Section 1: equation (1), Proposition 1, Corollary 2, the counts of gene trees |
| [`ADR11.Model`](ADR11/Model.lean), [`ADR11.Model.History`](ADR11/Model/History.lean) | Sections 2 and 3: equations (2) and (3), the worked examples, polynomiality, the support of the distribution |
| [`ADR11.FourTaxa`](ADR11/FourTaxa.lean), [`ADR11.Identifiability.FourTaxaAnalysis`](ADR11/Identifiability/FourTaxaAnalysis.lean), [`ADR11.Identifiability.Proposition3`](ADR11/Identifiability/Proposition3.lean) | Section 4.1 and Proposition 3 |
| [`ADR11.FiveTaxa.Lemma4`](ADR11/FiveTaxa/Lemma4.lean), [`ADR11.FiveTaxa.Basic`](ADR11/FiveTaxa/Basic.lean), [`ADR11.FiveTaxa.Explanations`](ADR11/FiveTaxa/Explanations.lean), [`ADR11.FiveTaxa.Balanced`](ADR11/FiveTaxa/Balanced.lean), [`ADR11.FiveTaxa.Caterpillar`](ADR11/FiveTaxa/Caterpillar.lean), [`ADR11.FiveTaxa.Pseudocaterpillar`](ADR11/FiveTaxa/Pseudocaterpillar.lean) | Section 4.2 and Appendix B: Lemma 4, Tables 1–3 with their explanations (symmetries, above and near the root, marginalization), inequalities (4)–(6), equations (11)–(13) |
| [`ADR11.Identifiability.Lemma5`](ADR11/Identifiability/Lemma5.lean), [`ADR11.Identifiability.Quartets`](ADR11/Identifiability/Quartets.lean), [`ADR11.Identifiability.Corollary6`](ADR11/Identifiability/Corollary6.lean) | Lemma 5 and Corollary 6 |
| [`ADR11.Identifiability.FiveTaxa.Classes`](ADR11/Identifiability/FiveTaxa/Classes.lean), [`ADR11.Identifiability.FiveTaxa.Binary`](ADR11/Identifiability/FiveTaxa/Binary.lean), [`ADR11.Identifiability.FiveTaxa.Common`](ADR11/Identifiability/FiveTaxa/Common.lean), [`ADR11.Identifiability.Proposition8`](ADR11/Identifiability/Proposition8.lean) | Propositions 7 and 8, equations (7)–(9): classes of gene trees, their sizes and cherries |
| [`ADR11.Trees.RootLocation`](ADR11/Trees/RootLocation.lean), [`ADR11.Identifiability.Theorem9`](ADR11/Identifiability/Theorem9.lean), [`ADR11.Identifiability.Corollary10`](ADR11/Identifiability/Corollary10.lean) | Theorem 9 (the location of the root) and Corollary 10 |
| [`ADR11.Nonbinary`](ADR11/Nonbinary.lean), [`ADR11.Nonbinary.Triples`](ADR11/Nonbinary/Triples.lean), [`ADR11.Nonbinary.FourTaxa`](ADR11/Nonbinary/FourTaxa.lean) | Section 5: the small nonbinary trees as limits, polytomies through rooted triples, Proposition 3 for nonbinary trees |
| [`ADR11.Nonbinary.AppendixC`](ADR11/Nonbinary/AppendixC.lean), [`ADR11.Nonbinary.FiveTaxa`](ADR11/Nonbinary/FiveTaxa.lean), [`ADR11/Nonbinary/FiveTaxa/`](ADR11/Nonbinary/FiveTaxa) | Appendix C: Tables 6 and 7, the shape read off the classes, the labelling rules, the lengths |
| [`ADR11.Identifiability.Unrooted`](ADR11/Identifiability/Unrooted.lean), [`ADR11.Nonbinary.Theorem9`](ADR11/Nonbinary/Theorem9.lean), [`ADR11.Nonbinary.Proposition11`](ADR11/Nonbinary/Proposition11.lean) | Proposition 11 |
| [`ADR11.Discussion`](ADR11/Discussion.lean) | Section 6: the comparison of two split probabilities |
| [`ADR11.AppendixA`](ADR11/AppendixA.lean) | Appendix A: Tables 4 and 5 (generated) |
| [`ADR11/Coalescent/`](ADR11/Coalescent) | Kingman's coalescent: forests, the factorization through the number of lineages and the jump chain, the limit above the root, the unrooted tree it produces |
| [`ADR11/MSC/`](ADR11/MSC) | The multispecies coalescent: basic properties, relabelling, marginalization, several lineages per taxon, edges of length zero and continuity in the lengths |
| [`ADR11/Trees/`](ADR11/Trees) | Hierarchies, rooted triples, normal forms of unrooted trees on four and five taxa |
| [`ADR11/Computation/`](ADR11/Computation) | A verified evaluator of gene tree distributions of small species trees, checked by the kernel |
| [`ADR11/Rootings/`](ADR11/Rootings) | The distributions of all rootings of the standard 4- and 5-taxon unrooted trees (generated statements) |
| [`ADR11/External/Tavare/`](ADR11/External/Tavare) | Tavaré 1984: equation (2) |
| [`ADR11/External/Quartets/`](ADR11/External/Quartets) | Steel 1992, Bandelt–Dress 1986, Semple–Steel 2003: trees from quartets |
| [`ADR11/External/Cayley/`](ADR11/External/Cayley) | Cayley 1857: rooted shapes on 3, 4 and 5 taxa |
| [`Challenge`](Challenge.lean), [`Solution`](Solution.lean) | The statements of record and their proofs |

## GitHub configuration

[`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml) builds the project
on every push and pull request, checks that the audit imports every module of the library, runs
the axiom audit, checks that the proofs follow the routes of the paper's proofs, and checks that
the Challenge's copy of the shared definitions, the documentation's links to the code and its
Markdown tables are current. It needs no settings.

## License

[Apache-2.0](LICENSE).
