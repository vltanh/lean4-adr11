module

public meta import Lean.Elab.Command
public meta import Lean.DocString
-- One `import all` line per module of the library, so that proofs are visible to the dependency
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find ADR11 -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all ADR11.AppendixA
import all ADR11.Basic
import all ADR11.Coalescent.Absorption
import all ADR11.Coalescent.Factorization
import all ADR11.Coalescent.Forest
import all ADR11.Coalescent.Outcome
import all ADR11.Computation.Caterpillar5
import all ADR11.Computation.Codes
import all ADR11.Computation.Engine
import all ADR11.Computation.FiveTaxa
import all ADR11.Computation.FourTaxa
import all ADR11.Computation.ThreeTaxa
import all ADR11.Computation.Toolkit
import all ADR11.Defs
import all ADR11.Discussion
import all ADR11.External.Cayley.Shapes
import all ADR11.External.Quartets.Steel
import all ADR11.External.Tavare.Formula
import all ADR11.FiveTaxa.Balanced
import all ADR11.FiveTaxa.Basic
import all ADR11.FiveTaxa.Caterpillar
import all ADR11.FiveTaxa.Explanations
import all ADR11.FiveTaxa.Lemma4
import all ADR11.FiveTaxa.Pseudocaterpillar
import all ADR11.FourTaxa
import all ADR11.Identifiability.Corollary10
import all ADR11.Identifiability.Corollary6
import all ADR11.Identifiability.FiveTaxa.Binary
import all ADR11.Identifiability.FiveTaxa.Classes
import all ADR11.Identifiability.FiveTaxa.Common
import all ADR11.Identifiability.FourTaxaAnalysis
import all ADR11.Identifiability.Lemma5
import all ADR11.Identifiability.Proposition3
import all ADR11.Identifiability.Proposition8
import all ADR11.Identifiability.Quartets
import all ADR11.Identifiability.Theorem9
import all ADR11.Identifiability.Unrooted
import all ADR11.Introduction
import all ADR11.Introduction.Counts
import all ADR11.Introduction.Proposition1
import all ADR11.MSC.Basic
import all ADR11.MSC.Contract
import all ADR11.MSC.Marginal
import all ADR11.MSC.MultiSample
import all ADR11.MSC.Relabel
import all ADR11.Model
import all ADR11.Model.History
import all ADR11.Nonbinary
import all ADR11.Nonbinary.AppendixC
import all ADR11.Nonbinary.FiveTaxa
import all ADR11.Nonbinary.FiveTaxa.Ac1Classes
import all ADR11.Nonbinary.FiveTaxa.StarOneSplit
import all ADR11.Nonbinary.FiveTaxa.TwoSplits
import all ADR11.Nonbinary.Proposition11
import all ADR11.Nonbinary.Theorem9
import all ADR11.Nonbinary.Triples
import all ADR11.Rootings.Proofs
import all ADR11.Rootings.Statements
import all ADR11.Rootings.Support
import all ADR11.SmallTrees
import all ADR11.Trees.Classify
import all ADR11.Trees.Hierarchy
import all ADR11.Trees.RootLocation
import all Solution

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`ADR11/External/`) that it uses, whether proved there or, in a conditional
formalization, assumed as hypotheses of its statement. It then checks every declaration
of the library and the theorems that Palomar's comparator checks. The run fails if any of them
depends on an axiom other than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a
`sorry` shows up as the axiom `sorryAx`). Its table of results is the source of the report's
dependency table.

It also writes the *route* of every numbered result to `.lake/route_deps.tsv`: the other
numbered results that its proof uses, found by following the proof through the library's helper
lemmas and stopping at numbered results, together with the TeX label that the result's docstring
names in backticks. `route_check.py` (in the skill's `scripts/`) compares these routes with the
results that the paper's proofs cite.

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

To adapt: generate the `import all` lines, fill in the three lists, and set the library's root
name in `isLibraryModule`. Keep one `import all` line per module of the library, each on its own
line: a module that is missing is still imported through the others, but without its proofs, and
the audit then misses the axioms and the routes inside them. The CI template checks the list.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work in `ADR11/External/`, with a short label: the theorems proved
there and, in a conditional formalization, the propositions assumed as hypotheses. The traversal
stops at them. -/
meta def externalResults : List (String × Name) :=
  [("Tavaré 1984 (powers of the generator)", ``ADR11.deathPow_eq_tavare),
   ("Tavaré 1984 (number of lineages)", ``ADR11.deathProb_eq_tavare),
   ("Steel 1992; Semple–Steel 2003, Thm 6.3.5 (splits from quartets)",
     ``ADR11.mem_unroot_iff_quartets),
   ("Steel 1992, Prop. 6 (distinguishing quartets)", ``ADR11.exists_distinguishing_quartet),
   ("Cayley 1857 (rooted shapes)", ``ADR11.cayley_shapes)]

/-- The numbered results of the paper, in the order of the paper. -/
meta def paperResults : List (String × Name) :=
  [("Eq (1)", ``ADR11.equation1),
   ("Eq (1), converse", ``ADR11.equation1_iff),
   ("Sec 1, triple branch length", ``ADR11.introduction_tripleLength),
   ("Prop 1", ``ADR11.proposition1),
   ("Cor 2", ``ADR11.corollary2),
   ("Sec 1, (2n-3)!! rooted trees", ``ADR11.section1_card_rooted),
   ("Sec 1, 2n-3 rootings", ``ADR11.section1_card_rootings),
   ("Sec 1, (2n-5)!! unrooted trees", ``ADR11.section1_card_unrooted),
   ("Sec 1, distribution (nonnegative)", ``ADR11.unrootedDist_nonneg),
   ("Sec 1, distribution (sum 1)", ``ADR11.unrootedDist_sum),
   ("Sec 1, nonbinary gene trees have probability 0", ``ADR11.rootedDist_support),
   ("Sec 2, pendant lengths do not matter", ``ADR11.rootedDist_eq_of_sameRootedMetricTree),
   ("Eq (2)", ``ADR11.equation2),
   ("Eq (2), g sums to 1", ``ADR11.coalescenceProb_sum),
   ("Eq (2), g_i1 limit", ``ADR11.tendsto_coalescenceProb_one),
   ("Eq (2), g_ii limit", ``ADR11.tendsto_coalescenceProb_self),
   ("Eq (2), g_ii", ``ADR11.coalescenceProb_self),
   ("Sec 3, example 1", ``ADR11.section3_example1),
   ("Sec 3, example 2", ``ADR11.section3_example2),
   ("Eq (3)", ``ADR11.equation3),
   ("Sec 3, polynomials", ``ADR11.section3_polynomial),
   ("Sec 4.1, balanced", ``ADR11.fourTaxa_balanced),
   ("Sec 4.1, caterpillar", ``ADR11.fourTaxa_caterpillar),
   ("Sec 4.1, recovery", ``ADR11.fourTaxa_recovery),
   ("Sec 4.1, five trees", ``ADR11.fourTaxa_sameDistribution),
   ("Sec 4.1, labelled shapes", ``ADR11.fourTaxa_card_shapes),
   ("Prop 3", ``ADR11.proposition3),
   ("Lemma 4", ``ADR11.lemma4),
   ("Lemma 4, six taxa", ``ADR11.lemma4_six),
   ("Table 1", ``ADR11.table1),
   ("Sec 4.2.1, classes", ``ADR11.balanced_classes),
   ("Eq (4)", ``ADR11.equation4),
   ("Eq (4), exhaustive", ``ADR11.equation4_exhaustive),
   ("Sec 4.2.1, extreme classes", ``ADR11.balanced_extremeClasses),
   ("Sec 4.2.1, degenerate", ``ADR11.balanced_degenerate),
   ("Table 2", ``ADR11.table2),
   ("Sec 4.2.2, marginalization", ``ADR11.caterpillar_marginalization),
   ("Sec 4.2.2, classes", ``ADR11.caterpillar_classes),
   ("Eq (5)", ``ADR11.equation5),
   ("Eq (5), exhaustive", ``ADR11.equation5_exhaustive),
   ("Sec 4.2.2, extreme classes", ``ADR11.caterpillar_extremeClasses),
   ("Table 3", ``ADR11.table3),
   ("Sec 4.2.3, classes", ``ADR11.pseudocaterpillar_classes),
   ("Eq (6)", ``ADR11.equation6),
   ("Eq (6), exhaustive", ``ADR11.equation6_exhaustive),
   ("Sec 4.2.3, least class", ``ADR11.pseudocaterpillar_minClass),
   ("Lemma 5", ``ADR11.lemma5),
   ("Lemma 5, rooted", ``ADR11.lemma5_rooted),
   ("Cor 6", ``ADR11.corollary6),
   ("Prop 7", ``ADR11.proposition7),
   ("Prop 8", ``ADR11.proposition8),
   ("Eq (7)", ``ADR11.equation7),
   ("Eq (8)", ``ADR11.equation8),
   ("Eq (9)", ``ADR11.equation9),
   ("Thm 9", ``ADR11.theorem9),
   ("Thm 9, four taxa", ``ADR11.theorem9_four),
   ("Cor 10", ``ADR11.corollary10),
   ("Sec 5, three taxa", ``ADR11.section5_threeTaxa),
   ("Sec 5, triples", ``ADR11.section5_triples),
   ("Sec 5, Prop 1", ``ADR11.section5_proposition1),
   ("Sec 5, Cor 2", ``ADR11.section5_corollary2),
   ("Sec 5, four taxa", ``ADR11.section5_fourTaxa),
   ("Sec 5, limits", ``ADR11.section5_limit),
   ("Prop 11 (Prop 3)", ``ADR11.proposition11_proposition3),
   ("Prop 11 (Cor 6)", ``ADR11.proposition11_corollary6),
   ("Prop 11 (Prop 7)", ``ADR11.proposition11_proposition7),
   ("Prop 11 (Prop 8)", ``ADR11.proposition11_proposition8),
   ("Prop 11 (Thm 9)", ``ADR11.proposition11_theorem9),
   ("Prop 11 (Thm 9, four taxa)", ``ADR11.proposition11_theorem9_four),
   ("Prop 11 (Cor 10)", ``ADR11.proposition11_corollary10),
   ("Sec 6, split probabilities", ``ADR11.discussion_splits),
   ("Table 4", ``ADR11.table4),
   ("Table 5", ``ADR11.table5),
   ("Eqs (11)", ``ADR11.equation11),
   ("Eqs (12)", ``ADR11.equation12),
   ("Eqs (13)", ``ADR11.equation13),
   ("Table 6", ``ADR11.table6),
   ("Table 7", ``ADR11.table7),
   ("Table 7, classes", ``ADR11.table7_classes),
   ("App C, least classes", ``ADR11.appendixC_leastClass),
   ("App C, degenerate", ``ADR11.appendixC_degenerate)]

/-- The theorems that Palomar's comparator checks (`theorem_names` of `comparator.json`). -/
meta def solutionResults : List Name :=
  [``ADR11.Challenge.unrootedDist_nonneg,
   ``ADR11.Challenge.unrootedDist_sum,
   ``ADR11.Challenge.fourTaxa_balanced,
   ``ADR11.Challenge.fourTaxa_caterpillar,
   ``ADR11.Challenge.theorem9,
   ``ADR11.Challenge.theorem9_four,
   ``ADR11.Challenge.proposition3,
   ``ADR11.Challenge.corollary10,
   ``ADR11.Challenge.proposition11_theorem9,
   ``ADR11.Challenge.proposition11_theorem9_four,
   ``ADR11.Challenge.proposition11_corollary10]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool := (`ADR11).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter library.contains
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

/-- Where `#audit` writes the routes, relative to the project root (`.lake/` is not committed). -/
meta def routeFile : System.FilePath := ".lake/route_deps.tsv"

/-- The numbered results that the proof of `root` uses: those reached from it through constants
of the library, without looking inside the proofs of numbered results themselves. -/
meta def resultUses (env : Environment) (library results : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c || c == root then continue
      visited := visited.insert c
      if results.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

/-- The code spans of the docstring of `c` that contain no space or comma: the candidates for its
TeX label. -/
meta def docLabels (env : Environment) (c : Name) : IO (Array String) := do
  let some doc ← findDocString? env c | return #[]
  let mut out : Array String := #[]
  let mut inside := false
  for part in doc.splitOn "`" do
    if inside && !part.isEmpty && !part.any (fun ch => ch.isWhitespace || ch == ',') then
      out := out.push part
    inside := !inside
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library, including private and auxiliary ones.
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  -- The routes: for each numbered result, its docstring's labels and the results it uses.
  let results : NameSet := paperResults.foldl (fun s p => s.insert p.2) {}
  let mut routes : Array String := #[]
  for (label, n) in paperResults do
    let labels ← docLabels env n
    let uses := resultUses env library results n
    routes := routes.push (s!"{label}\t{n}\t{",".intercalate labels.toList}\t" ++
      ",".intercalate (uses.map toString).toList)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile routeFile ("\n".intercalate routes.toList ++ "\n")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
