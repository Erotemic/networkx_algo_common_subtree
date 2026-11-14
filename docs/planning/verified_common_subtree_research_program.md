# Verified common-subtree algorithms: research program and engineering charter

Status: active planning; formalization underway; no end-to-end verified solver yet  
Updated: 2026-11-13 (after the successful local Lean 4.35.0 build was reported)  
Project: `networkx_algo_common_subtree`

This document records the intended destination and the decisions behind it. It
is the program-level reference, not a claim of completed formal verification.
Detailed work packages live in:

- [Lozano-Valiente (2004) plan](lozano_valiente_2004_verified_rust_lean.md)
- [Droschinsky, Kriege, Mutzel (2016 and 2018) plan](droschinsky_2016_2018_verified_rust_lean.md)
- [Planning index and evidence map](README.md)

## 1. What we intend to accomplish

Build a serious mathematical and implementation verification project for **three
papers, two algorithm families, and their useful shared foundations**:

1. **Lozano and Valiente (2004):** maximum common embedded subtrees of rooted,
   **ordered** trees via balanced sequences, including the paper's mathematical
   characterization, dynamic-programming algorithm, witness construction, and
   qualified complexity bound.
2. **Droschinsky, Kriege, Mutzel (2016):** maximum-weight common subtree
   **isomorphism** of unordered trees, including optimal child matching and the
   paper's faster matching strategy, rather than stopping at the straightforward
   Hungarian-backed reference algorithm.
3. **Droschinsky, Kriege, Mutzel (2018):** largest-weight common subtree
   **embeddings with distance penalties**, including paths with skipped vertices,
   the paper's exact reward/penalty semantics, optimized algorithms, and their
   actual assumptions and bounds.

For each paper, the long-term result should comprise:

- An independent, readable Lean mathematical specification of the *problem*.
- A theorem-by-theorem account of the *paper*, with corrections where a printed
  statement, assumption, or interpretation is inadequate.
- Executable algorithms with machine-checked functional correctness and valid,
  independently checkable witnesses; separately machine-checked complexity
  statements under an explicit computational cost model.
- A maintained Rust implementation whose **actual translated source** is
  connected to the Lean specification using Charon/Aeneas.
- Independent exhaustive/differential testing, performance measurements, and
  appropriate Python/NetworkX integration.

These are distinct deliverables. Implementing a paper-like recurrence, translating
Rust into Lean, checking agreement with another implementation, and proving
optimality are four different accomplishments. None automatically implies the
others. Full paper coverage includes its key combinatorial and algorithmic
results, not merely verification of an implementation that happens to return
correct answers.

The standards are proof strength, correctness of the mathematical problem,
practical utility, clarity of the code, and reproducibility. We are also
interested in extracting **reusable formal mathematics** that could contribute
upstream to Mathlib or TauCeti where it genuinely belongs.

## 2. Decisions already made

| Decision | Consequence |
| --- | --- |
| **Restart the Lean proof development** | Historical `Lozano-v3` through `Lozano-v6` and the old `proofs` branch are research history, not dependencies or migration targets. No copying their theorem statements or architecture into the new proof. |
| **Keep existing implementation work** | The reset did not discard Python, Cython, optimized PyO3/Rust, Droschinsky Rust, test data, or benchmarks. They remain useful baselines and regression targets. |
| **Start with independent mathematics** | Ordered-tree contraction and valid witnesses are defined before and independently of Dyck words, DP tables, or Rust types. |
| **Formalize papers *and* Rust** | A direct Rust-to-spec correctness proof is valuable, but it alone would not formalize the paper's algorithm and complexity argument. |
| **Parallelize the Aeneas feasibility spike** | Translate a small genuine Rust function early, while the mathematical tree/encoding proofs are developed. Do not postpone the toolchain feasibility check until all of the paper is proved. |
| **Mathlib first, selective additional dependencies** | Mathlib's Dyck-word and finite-combinatorics machinery is the first candidate. TauCeti and CLRS-Lean require concrete theorem/compatibility evaluations before being hard dependencies. |
| **The ordered and unordered problems stay distinct** | Share honest general tree, path, matching, finiteness, and optimization lemmas; do not force one embedding definition or scoring rule across incompatible paper semantics. |
| **Published objectives are authoritative** | If a Python/Rust implementation disagrees with the 2018 paper's path-weight rule, fix or separately name that implementation's alternative objective. |
| **Correctness and performance both matter** | A verified but extremely slow prototype is a milestone, not the finished library. Keep optimized baselines and measure speed, memory, and scaling before integration decisions. |
| **No speculative history cleanup** | Keep valuable commits and branches available. Review old C/Cython/packaging experiments selectively rather than merging stale branches wholesale. |

## 3. Current baseline: implemented is not yet proved

The status below summarizes inspections and tests in the November 13 discussion
against the supplied `af0bbdb` archive. These are **historical observations**,
not claims about a subsequent local worktree or a fresh CI run.

| Component | What exists | What still blocks acceptance |
| --- | --- | --- |
| Ordered LCBE / balanced embedding | Native `Solver::emb` in `rust/src/lib.rs`, state interning/memoization, PyO3 exposure | Independent optimum proof; extraction-friendly verified core; comprehensive witness tests; complexity refinement |
| Ordered LCBS / balanced isomorphism | Native `Solver::iso` in the same Rust backend; Python API dispatch | Its own exact mathematical contract and correctness coverage; verified Rust refinement |
| Python/Cython ordered implementations | Existing reference and accelerated backends | Independent oracles and parity over full supported semantics |
| Droschinsky 2016 isomorphism | Standalone graph-only Rust DP and Hungarian-style matching | Full parameter testing, verified recurrence and Rust code, specialized fast matching, Python adapter |
| Droschinsky 2018 embedding | Experimental Rust and Python implementations | **Known paper-semantic scoring/feasibility discrepancy**, independent oracle, optimized paper algorithm, verification |
| Weighted bipartite matching | Rust implementation with small exhaustive matrix tests | Formal matching specification, optimality of a verified implementation, reductions for forbidden/unmatched vertices |
| New Lean foundation | Lean 4.35.0 / Mathlib project with `OrderedTree` and Dyck-word source | **Local `lake build` now reported passing**; reproducible clean-checkout build and axiom audit outstanding; no containment/optimality/complexity proof |
| Aeneas translation | Planned | No demonstrated checked Rust-to-Lean refinement in this project |
| Benchmarks | Tree/model-like fixtures and benchmark drivers exist | Reproducible pinned baseline measurements and optimized-paper scaling evidence |

The prior audit reported 46 passing Python tests and two skipped extension tests
in one run; a separate targeted Rust-backend test had two passed and two skipped.
It also identified 1,764 enumerated small-tree pairs in the 2016 Rust test source,
64 additional case pairs, and 1,600 deterministic matching test instances. The
Rust suites were **inspected, not successfully executed** in that environment.
These numbers are an inventory of historical test coverage, not a certification
of paper fidelity. The 2018 tests share the incorrect scoring convention with
its implementation and thus do not resolve the known discrepancy.

### Initial Lean build and corrected foundation

The initial `OrderedTree.lean` required repairs to automatic `DecidableEq`
derivation, mutual declaration syntax, contraction induction/kernel declaration,
edge-count arithmetic, and ambiguous `.node` elaboration. The resulting
contraction representation uses an explicit one-hole ordered-tree context.
**The user has now reported a successful local `lake build` after those repairs.**
A fresh-checkout rerun and public theorem-axiom inventory are still needed.

**Immediate priority:** preserve the compiling baseline, commit the Lake
manifest, audit accepted theorem dependencies, and set up actual Lean CI.
Proceed with the small contraction oracle and the encoding/containment
correspondence proofs; the foundation build is no longer a blocking error.
Track claim-by-claim assurance in `proofs/PROOF_STATUS.md`.

## 4. Verification architecture

```text
                      Independent mathematical problem specifications
                     /                |                   \
       ordered contractions     unrooted weighted       topological paths
               |                 isomorphism           + distance penalties
      tree <-> Dyck word           |                   |
               |                 maximum-weight partial matching
      balanced-sequence DP         |                   |
               |             paper-level DPs and witness proofs
               +------------------+-------------------+
                                  |
                   executable Lean/reference algorithms
                                  |
                      proof-friendly Rust core(s)
                                  |
                  Charon/Aeneas translated Lean code
                                  |
                         representation/refinement
                                  |
                    checked API and performance evidence
```

The drawing represents logical dependencies, not an order to put all code into
one crate or one Lean module. For every solver distinguish the following proof
levels:

1. **Semantics:** validity, feasibility, score, optimum, and full witnesses from
   independent finite mathematical objects.
2. **Paper correspondence:** exact definition/lemma/theorem crosswalk; proof of
   representation equivalence; recurrence soundness and completeness; witnesses.
3. **Algorithm:** a terminating executable computation proven equal to the
   independently specified optimum. A recurrence proved by unfolding itself
   does not pass this level.
4. **Complexity:** operation counts tied to *that computation*, finite state
   bounds, and explicit accounting for dictionary, matching, arithmetic,
   memory, and reconstruction operations.
5. **Rust refinement:** proofs about Aeneas-generated semantics of real Rust
   source, plus representation, input validation, overflow/index safety,
   memoization, error behavior, and translated witnesses.
6. **Integration:** actual Python/NetworkX input/output mapping, optional
   callback/label semantics, fallback behavior, and measured performance.

A paper-level mathematical theorem is not automatically a theorem about the
optimized PyO3 extension. Aeneas-generated definitions are not the definition
of the mathematical problem. A fast baseline need not be thrown away while a
verification-friendly implementation is built.

## 5. Formal foundations and dependency selection

### Mathlib: default mathematical substrate

Investigate and reuse (checking names/signatures against the pinned version):

- `Mathlib.Combinatorics.Enumerative.DyckWord`: balanced words, semilength,
  inside/outside decomposition, and existing tree correspondences.
- `Mathlib.Data.Tree.Basic`: binary trees and structural recursion/induction;
  adapt carefully because the paper uses arbitrarily branching ordered trees.
- `List`, `List.Sublist`, finite functions, `Finset`, `Fintype`, decidability,
  well-founded recursion, `Relation.ReflTransGen`, `omega`, `grind`.
- `SimpleGraph.IsTree`, paths, uniqueness of simple paths, combinatorial
  matching and graph theory for the unordered weighted problems.
- `Asymptotics.IsBigO` for a statement of a proven operation-count bound;
  asymptotic notation is not itself a cost semantics.

Mathlib's Dyck-word order should **not** be assumed identical to the paper's
edge-annotation containment or tree edge contraction. The bridge is a theorem
to prove in both directions.

### TauCeti: deliberate reuse, not a dependency by default

Candidate modules from the prior audit:

- `TauCeti.Combinatorics.Enumerative.DyckWord`: supplementary Dyck-word results;
  probably modest incremental value for Lozano.
- `TauCeti.Combinatorics.Tree.ReducedPlanar`: ordered rooted reduced trees and
  leaf/internal bounds. Its no-unary-vertex restriction prevents using it as
  the general ordered-tree specification without a separate equivalence.
- `TauCeti.Combinatorics.SimpleGraph.Paths`: path-decomposition ideas for the
  2018 skipped-vertex proofs.
- `TauCeti.Combinatorics.Graph.Matching.Basic`: matching validity/perfectness;
  not itself a verified weighted Hungarian solver.

Audit exact APIs, assumptions, and compatibility against the chosen Mathlib pin
before importing. If a general lemma is missing, decide whether to contribute
upstream or keep it locally based on actual reuse; do not recreate existing
foundations merely for architectural independence.

### CLRS-Lean: candidate for the 2016 matching subproblem

The previously inspected
[`CLRS-Lean` Hungarian development](https://github.com/TankTechnology/CLRS-Lean)
contains potential, but its equal-sided complete assignment with real costs
requires a theorem connecting it to the partial, forbidden-edge, possibly
negative-weight maximum matching used here. It does not establish correctness
of the existing Rust solver. The earlier audit reported a Mathlib `v4.32.0-rc1` pin, distinct from our `v4.35.0` selection; recheck the current state. Perform a
real build/API and theorem-dependency compatibility spike before making it a
required dependency.

### Std/Batteries and Aeneas

Use Lean `Std`/Batteries for executable collections as needed. Select Rust
representations by both computational merit and the subset supported by a
**pinned, executable Charon/Aeneas pipeline**; do not assume all of Rust's
containers, closures, borrowing patterns, Python callbacks, or allocation
models translate. Keep PyO3 and NetworkX conversion outside the initial
verified core. Make the trusted boundary explicit.

**Dependency rule:** no mandatory TauCeti/CLRS dependency without a concrete
saved example showing an imported theorem materially simplifies a proof and
all relevant toolchains build together.

## 6. Mathematical issues that must remain visible

### 2004: leaf count and state complexity

The printed recurrence discussed in the previous audit is
`ell(nil) = 1` and `ell(0 x 1 y) = ell(x) + ell(y)`. Under its stated
semilength grammar, the measure is `semilength + 1`, rather than the true
number of leaves. For the one-edge rooted tree `01`, it gives 2 while the
actual number of tree leaves is 1. It cannot justify a claimed
leaf-sensitive bound merely by renaming it `leaves`.

The target theorem has the advertised scale

`O(n1 * n2 * min(d1, l1) * min(d2, l2))`,

with `l1` and `l2` the *actual* leaf counts if that is the intended paper
statement. Rebuild the state-count proof with a correct measure, produce a
counterexample if it fails, and record any corrected theorem. The previous
small exhaustive search reportedly checked 23,714 balanced sequences through
10 edge pairs without finding a counterexample to a stronger candidate bound;
this is evidence to investigate, not a proof.

The paper's dictionary-based expected-time argument must be separated from a
Rust worst-case cost claim. A symbolic bound on a chosen cost formula is not
an operation-count theorem about an algorithm.

### 2004: true contraction, witness, and DP semantics

The old `Lozano-v6` work bypassed key results by defining embedding via
sequence containment and proving the recurrence from its own definition.
The replacement needs both directions of contraction/sequence containment,
root and order conventions, and an independently optimized *tree* witness.
Do not import the retired proof architecture.

### 2016: matching optimality versus faster matching

An ordinary Hungarian-style child-matching DP can be a correct reference
while failing to achieve the paper's advertised `O(n^2 Delta)` bound. Prove
the matching recurrence and then the faster relationship/reuse between
matching instances, including its own cost model. Score-only results are
insufficient; returned partial mappings must be feasible and optimal.

### 2018: published scoring and feasibility differ from current code

The earlier audit identified that a mapped skeleton edge realized by a path
of length greater than one **does not receive the direct edge-pair similarity
reward** under the paper's convention; it instead incurs the applicable
skipped-vertex penalty. Existing Rust/Python reference implementations
award an initial-edge match and can also reject permitted longer-path
embeddings based on that edge label. See the dedicated [Droschinsky plan](droschinsky_2016_2018_verified_rust_lean.md)
for two discriminating regression cases. This is a semantic blocker, not a
performance issue. The paper's rule is authoritative for the verified
paper solver; any alternative objective gets its own name and tests.

## 7. Testing and independent evidence

The mathematical oracle must **not reuse the production recurrence**, and
witness scoring must **not reuse the production scorer**. For manageable small
instances, enumerate valid candidates and mappings; for larger instances,
validate each witness independently and compare available exact solver values.

Core test families:

- Ordered trees: singleton, one edge, unary chain, stars, binary/fanout,
  combs, brooms, reordered siblings, embedded contractions at any depth,
  equal-score alternative witnesses, and malformed encodings.
- Unordered weighted trees: incompatible node/edge labels, duplicate labels,
  positive/zero/negative weights, partial and forbidden matchings, empty versus
  nonempty mapping policies, symmetry where the scoring contract warrants it.
- 2018 embeddings: paths of length one versus longer paths, different edge
  labels along skipped paths, zero and nonzero penalties, overlapping paths,
  branch disjointness, and witness skeleton rescoring.
- Rust and APIs: index/size errors, arithmetic overflow and NaN/nonfinite
  weights (where applicable), deterministic ties, adapter label conversions,
  callbacks, extensions unavailable, and fallback dispatch.
- Performance: chains, high-degree stars, balanced and asymmetric trees,
  adversarial matching instances, random trees, and the existing ResNet-like
  module-containment fixtures. Record hardware, flags, versions, sample
  distributions, allocations, peak RSS, CPU time and state/matching counts.

Distinguish theorem verification, property testing, oracle comparison,
translation/regeneration checks, and statistical benchmarks in reports.
Keep CI focused on actual source and theorem behavior; do not add brittle
source-text guards or tests-of-tests.

## 8. Implementation and repo boundaries

Maintain separate areas for:

- **Paper-independent specifications:** tree structures, paths, valid
  embeddings/isomorphisms, matching, weights and finite optima.
- **Paper-specific mathematics:** Dyck words/decomposition for 2004;
  weighted partial matching/reuse for 2016; topological paths and penalties
  for 2018.
- **Executable Lean algorithms:** explicit recurrences, witnesses, and cost
  semantics, independent of Rust-generated structures.
- **Aeneas-generated semantics and refinement:** generated modules, adapters,
  termination/safety, representation relations, and final theorems.
- **Rust implementation:** proof-friendly core crate(s), current optimized
  PyO3 backend as benchmark, and Droschinsky graph-only crate.
- **Python integrations:** NetworkX adapters and optional behaviors, without
  contaminating the abstract spec with Python representations.

Favor comprehensible APIs and domain-specific, grep-friendly function names.
Avoid module-level generic helpers duplicating method names. Do not invent a
common generic graph abstraction if it obscures the ordered/unordered
semantic distinctions. Optimize only after establishing a reference theorem
and test baseline; avoid accumulating compatibility shims to preserve past
implementation mistakes.

## 9. Workstreams and order

| Track | Early deliverable | Full completion criterion |
| --- | --- | --- |
| L0: build discipline | Local Lean 4.35.0 build reported passing; audit theorem axioms and reproduce in CI | Reproducible pinned mathematical project |
| L1: 2004 semantics | Edge contraction, encoding round-trip, two-way containment theorem and a tiny oracle | Independent problem/representation bridge |
| L2: 2004 algorithm | Paper decomposition and LCBE/LCBS DP optimality with a witness | Theorems for paper correctness and combinatorics |
| L3: 2004 complexity | True-leaf state bound and computation-tied operation counter | Justified published or precisely corrected complexity bound |
| R0: Aeneas feasibility | A small translated Rust example with a proved refinement lemma | Pinned generator and checked generated modules |
| R1: verified ordered core | Executable Rust/Lean representation correspondence, DP and witness correctness | End-to-end theorem about translated Rust entry point |
| D0: 2016 matching foundation | Independent partial matching and small exhaustive oracle | Checked matching optimum theorem and feasible witness |
| D1: 2016 isomorphism | Rooted/unrooted DP proof and complete Rust reference tests | Correct and then optimized `O(n^2 Delta)` paper algorithm |
| D2: 2018 semantics | Correct paper scorer, path oracle and two counterexample fixtures | Independent embedding feasibility/optimum specification |
| D3: 2018 algorithm | Branch/path recurrence, witness, optimized paper method, extracted Rust | Functional and computational correctness under published assumptions |
| I: integration/evaluation | Baselines, test runner/CI, benchmarking and Python dispatch | Reproducible performance, verified adapter and release evidence |

**Suggested execution order:** complete L0 reproducibility and axiom auditing while advancing L1 and R0 in parallel;
start D0's mathematical matching groundwork independently. Do not let the
2018 prototype's current scorer define D2, and do not wait for all paper
proofs to finish before testing extraction feasibility. Put D1 ahead of D3
because 2018 adds path constraints and penalty accounting.

Each paper plan contains finer-grained packages and dependency gates. The
program is finished only when paper correctness, verified actual Rust,
qualified complexity, independent witnesses, tested integration and usable
performance are present for the claimed scopes. It is acceptable to publish
intermediate, accurately scoped results without calling them completion of
all three papers.

## 10. Branches, history and provenance

The `af0bbdb` snapshot already contains the substantive native Rust LCBE/LCBS
work and the Droschinsky crate. The prior branch audit found no hidden
Droschinsky implementation stranded on a different branch.

- `Droschinsky-algos`: the active development line; keep the work and history.
- `proofs`: retired Lean experiment; use for historical comparison only.
- `codex/implement-pure-c-algorithms-with-bindings`: restricted C backend;
  optional comparison, not a Rust/Aeneas dependency.
- `codex/improve-efficiency-of-cython-code`: possible small Cython
  optimization and benchmark ideas; avoid importing obsolete packaging.
- `codex/configure-cibuildwheel-for-abi3-wheels`: revisit during release/wheels.
- `codex/modernize-build-to-pep517-with-rust-backend`: incorporated ancestor
  of the inspected development line; no re-merge.
- Others: historical/ancestor/redundant in the previous audit; verify actual
  current PR status before deleting branches remotely.

The notes in `dev/notes/notes.txt` mention reference implementations supplied
by an author in 2025 and a later selective Rust port. The notes themselves did
not expose private code in the inspected snapshot. Maintain a provenance and
permissions record for anything translated from nonpublic implementations;
prefer paper-based independent reimplementations for the public artifact.
No history rewrite is justified by the inspected notes alone.

## 11. Working and acceptance discipline

1. **One accepted proof chain:** avoid versioned `-v6`, `-final`, duplicate
   mathematical definitions, legacy support directories, and unbounded
   speculative scaffolds. Retain dead research in Git, not active imports.
2. **Build before describing as proved:** when Lean elaboration fails, fix the
   earliest error, rerun `lake build`, then record accepted theorem names and
   check axioms. A source file with written `by` blocks is not kernel-checked.
3. **Proof obligations are statements about real objects:** no local `sorry`, `admit`, arbitrary `axiom` or unverified opaque operation in an accepted proof chain; no theorem named
   `correct` whose meaning is only equality to a self-defined recurrence or
   a symbolic cost variable. State assumptions and actual witnesses.
4. **Historical tests are evidence, not definitions:** source and tests may
   contain the same bug. Make paper discriminators and exhaustive oracles
   independent of the production algorithm.
5. **Pin and reproduce:** Lean/Mathlib/TauCeti/CLRS revisions (as used),
   Charon/Aeneas/Rust versions, generated Lean artifacts, Cargo lockfiles,
   test commands and benchmark configuration. Record trusted boundaries.
6. **Keep optimization contracts explicit:** reference algorithm, verified
   algorithm and optimized baseline can coexist temporarily; compare them
   on the same mathematical objective before substituting a backend.
7. **Repository changes are reviewable:** text-only planning overlays, exact
   staging/commit instructions, no bundled screenshots/binaries, and no
   gratuitous guardrails or process tests.

## 12. References to pin in the paper ledgers

- Lozano and Valiente (2004), original PDF:
  https://www.cs.upc.edu/~antoni/subtree.pdf
- Droschinsky, Kriege and Mutzel (2016):
  https://arxiv.org/abs/1602.07210
- Droschinsky, Kriege and Mutzel (2018):
  https://arxiv.org/abs/1805.00821
- Mathlib Dyck words:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Enumerative/DyckWord.html
- TauCeti: https://github.com/TauCetiProject/TauCeti
- CLRS-Lean: https://github.com/TankTechnology/CLRS-Lean
- Charon: https://github.com/AeneasVerif/charon
- Aeneas: https://github.com/AeneasVerif/aeneas

The paper ledgers should ultimately pin exact versions/sections, enumerate
original statements and their corresponding Lean theorems, and mark any
mathematical corrections explicitly. URLs and informal notes alone are not a
proof provenance record.
