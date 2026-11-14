# Lozano-Valiente (2004): fresh Lean formalization and verified Rust implementation

Status: tree/Dyck encoding and forward contraction direction compile locally; converse authored, pending local build; algorithmic proofs pending
Last revised: 2026-11-13 (after successful local Lean build was reported)
Paper: Antoni Lozano and Gabriel Valiente, *On the Maximum Common Embedded Subtree Problem for Ordered Trees* (2004)
Repository: `networkx_algo_common_subtree`
Program charter: [Verified common-subtree research program](verified_common_subtree_research_program.md)

## 0. Present state and immediate milestone

The old `proofs` branch and v3-v6 proof sources are retired from active imports.
The restart **has already occurred**; do not run the earlier removal/reset
instructions again. Existing Rust/Python/Cython algorithms and Git history
remain intact. As of commit `b94593e`, the new Lean source and Lake project have
been committed.

The fresh Lake workspace requests Lean 4.35.0 and Mathlib `v4.35.0`.
The first drafted sources are:

- `proofs/SubtreeProofs/Paper2004/OrderedTree.lean`: finite rooted ordered
  trees, true leaf/edge counts, one-hole contexts and arbitrary-depth edge
  contractions, reflexive-transitive embedding and independent optimum.
- `proofs/SubtreeProofs/Paper2004/BalancedSequence.lean`: encoding into
  Mathlib `DyckWord` and a proposed semilength theorem.
- `proofs/PROOF_STATUS.md`: intended theorem-level evidence inventory.

**Observed build status:** the user reports that `cd proofs && lake build`
**now succeeds** after the constructor-elaboration correction. The initial
build failures (automatic `DecidableEq`, mutual syntax, the kernel-invalid
mutual contraction relation, arithmetic and `.node` elaboration) have been
resolved sufficiently for the current Lean sources to compile. This is a
reported local build result; a fresh-checkout reproducibility run, the exact
build log, and theorem-axiom audit have not yet been recorded. Prior Mathlib
module-system import warnings were nonfatal.

**Latest Lean build reported by maintainer:** the original ordered-tree
foundation, `EncodingEquivalence.lean` (including both round trips) and
`ContractionSoundness.lean` (including `embeds_encodeDyck`) now compile under
Lean 4.35.0 following the successive parser and constructor fixes. This
supersedes the earlier statement that these two modules were build-pending.

**New converse increment (pending local compilation):**
`ContractionCompleteness.lean` introduces forest decoding, proves decoding
respects concatenation and nesting, relates deletions in a `DyckContext` to
ordinary tree contractions, and states the two-way bridge
`embeds_iff_dyckEmbeds`. It is included as authored source, not yet reported as
accepted by Lean. The result concerns our explicit Dyck deletion relation;
agreement with the paper's exact balanced-containment convention still needs
independent review.

**Next action:** compile the new converse module and run `#print axioms` on
the two-way theorem. Then add an independent tiny-tree contraction oracle and
check the exact containment definition against the 2004 paper. Preserve the
passing baseline and lockfile, and add focused Lean CI. A passing build establishes Lean
acceptance of the current declarations; it does not establish the 2004
paper's contraction/sequence equivalence, recurrence, complexity claim, or any
Rust refinement.

Do not conflate the existing `ContractStep` implementation with proof of
agreement with the paper's exact root/edge contraction convention; that
correspondence is still a first-phase mathematical obligation.

## 1. Research goal and boundaries

Formalize the **original 2004 paper**, including its problem specification,
mathematical correspondence to balanced sequences, decomposition lemmas,
correctness of the dynamic program, constructive witnesses and the genuine
complexity argument. Then prove that an executable **Rust implementation**
translates through Charon/Aeneas and refines the independent Lean optimum.
Finally measure and integrate a competitive solver into the existing
NetworkX-facing API.

Verification is layered: the independently defined maximum, the paper
algorithm's recurrence and complexity, the Aeneas-translated Rust entry point,
and the Python integration are separate results. A proof of each is required
for a corresponding completion claim. Mathlib is the initial foundation;
TauCeti is optional pending exact theorem/dependency evidence. Neither the
old Lean experiments nor the existing Rust solver defines the problem.

The reset applies **only to old proof code**. Keep the optimized ordered Rust
baseline (`rust/src/lib.rs` with `Solver::emb`, `Solver::iso`, `decompose1`,
`decompose2`, memoization and PyO3 bindings), Python/Cython variants, tests,
benchmarks, relevant Git commits and history. No need to reimplement the
already working native algorithm before doing semantics; the future
proof-friendly Rust core will be compared against it. Do not merge the old
`proofs` branch or copy its declarations.

Targets:

1. Independent finite-tree embedding and optimization specifications.
2. Two-way tree contraction / Dyck-word containment equivalence and exact
   encoding/decoding round trips.
3. Real DP optimality (including witness soundness/completeness), not merely
   a recurrence defined to equal itself.
4. Paper definitions, Facts, Lemmas, Corollaries and Theorems crosswalk,
   including any necessary correction to a printed statement.
5. Complexity expressed as operations of an actual algorithm with finite
   decomposition-state bounds and explicit dictionary assumptions.
6. Verified translated Rust solver, including accepted-input safety and
   output witness, with reproducible generation and theorem dependencies.
7. Independent tests, measured scaling, and production integration.

Avoid proof-specific shims inside the mathematical specification, vague generic
helper names, one-off optimized Rust changes without semantic evidence, and
claims of verification based only on tests or authored uncompiled Lean.

## 2. Lessons from the retired proofs

These are hard requirements for the fresh development, not a plan to resurrect
old files:

- `Lozano-v6` used an encoded-containment relation as its notion of embedding;
  it therefore did not prove the missing edge-contraction correspondence.
- Its `lcsLen` recurrence was unfolded from the way `lcsLen` was defined;
  it did not prove equality with an independent maximum common embedding.
- Its runtime result was conditional on a cost formula and state hypotheses
  rather than operation counts derived from an executable algorithm.
- The printed `ell(nil)=1`, `ell(0 x 1 y)=ell(x)+ell(y)` recurrence yields
  `semilength+1`, **not actual tree leaves**; this matters for the claimed
  leaf-sensitive running time. The one-edge tree `01` has one leaf but the
  recurrence gives two. Resolve the correct combinatorial bound explicitly.

Retain historical examples only as evidence of what needs checking. Never
inherit their proof assumptions, theorem names or architecture.

## 3. Precisely define the first verified problem

Begin with finite, rooted, **ordered**, unlabeled trees. An embedding is obtained by contracting edges while preserving left-to-right child order, with the root convention established from the paper before proceeding. Measure optimality in **edges**, stating the corresponding node-count relation. Distinguish the one-vertex tree (zero edges) from an empty forest or invalid input. Precisely define valid trees and the domain of every public function.

The first theorem must have no dependence on NetworkX objects, labels, Python callbacks, optional affinity functions, weighted scores, unordered trees, or Droschinsky-style algorithms. Later extensions will have separate specifications and theorems. Retain the existing implementations as comparison targets only; behavioral agreement with them is not the definition of correctness.

Required independently defined objects:

- `OrderedTree`, forest, child order, size, depth, and **actual number of leaves**;
- contraction at any permitted edge/position, its reflexive-transitive closure, and the common-embedding relation;
- feasibility of a proposed answer, score, optimal value, and optimal witness;
- balanced-sequence grammar, sequence operations, length, encoding and decoding;
- sequence containment stated independently of the future DP;
- an executable exhaustive oracle for tiny trees based on contraction enumeration (not the paper's DP).

**Specification gate:** handwritten examples and exhaustive small-tree oracle outputs agree with the selected interpretation. Every edge/root/leaf convention is documented with at least one discriminating example. No production algorithm is imported by the specification.

## 4. Proof architecture and theorem obligations

Work in dependency order. Create modules only when their mathematical boundary is clear; prefer descriptive, grep-friendly theorem and function names over generic helpers that duplicate names elsewhere.

### A. Trees, encodings, and semantics

1. Define finite ordered rooted trees, forests and edge contractions in Lean without balanced sequences.
2. Define balanced sequences and their algebra, then prove encode/decode correspondence and structural invariants.
3. Define paper-style containment and an operational deletion relation independently. Prove both directions of their equivalence.
4. Prove **both directions** of the correspondence between sequence containment and the reflexive-transitive closure of tree contractions, including contractions inside nested children and splicing order.
5. Prove the stated relation between sequence semilength and the number of tree edges.

**Gate A:** `u` embeds into `t` under the independent tree relation if and only if `encode u` is contained in `encode t`; neither side is defined as the other.

### B. Decomposition combinatorics and the paper's bounds

1. Reconstruct the decomposition state set and auxiliary families (`D`, `R`, `S`) as mathematical finite sets; prove their recurrences and the paper's inclusion lemmas.
2. Inventory the paper's Definitions 1-5, Facts 1-2, Lemmas 1-8, Corollaries, and Theorems 1-3. Maintain one paper-to-Lean ledger identifying literal statements, clarified statements, and any required correction.
3. Derive cardinality bounds for decomposition states from the new definitions. Pay particular attention to `nil`, single-child trees, degenerate tails, chains, stars and high branching.
4. Verify the meaning of the paper's printed leaf recurrence. If it counts something other than actual tree leaves, define both measures explicitly and prove the bound needed for the final theorem with *actual tree leaves*; do not substitute one for the other by name.
5. Prove a suitable bound in terms of `n * min(depth, leaves)` (up to the constants or lower-order terms actually supported), or document a demonstrated counterexample and a corrected theorem before proceeding.

**Gate B:** a closed theorem bounds the actual state set in the tree parameters that appear in the claimed asymptotic result. It has no unexplained combinatorial hypothesis. Counterexamples or corrections are preserved as small mathematical tests.

### C. Optimality of the dynamic program (embedding and isomorphism)

1. Identify the exact paper-level LCBE (balanced embedding) and LCBS/LCSI
   (balanced isomorphism) result contracts, and distinguish them from the
   NetworkX-facing routine names `Solver::emb` and `Solver::iso`.
   Define each optimum independently over valid finite witnesses or a proved
   equivalent finite characterization. Do not assume the two recurrences
   solve the same problem.
2. Define the paper's numeric recurrence as a *separate* executable function; prove the recurrence returns that independent optimum by soundness, completeness, and well-founded induction.
3. Give an explicit witness-producing algorithm for each promised solver;
   prove its returned witness is feasible and has the optimal score, including
   base cases, order constraints, and tie choices. Show tree witnesses and
   sequence-index witnesses correspond.
4. Prove the resulting tree witness solves the contraction-based MCES problem using Gate A, without defining `MCES` via the DP result.

**Gate C:** checked theorems establish the specified embedding/isomorphism optima and independently valid tree witnesses for every covered algorithm. Unfolding a recurrence is insufficient.

### D. Cost semantics and the 2004 complexity claim

1. Define the DP state domain, transition count and a concrete work model for state construction, table operations, coding/decoding and witness reconstruction.
2. Prove termination, state uniqueness/canonicalization, and that each required state is evaluated a bounded number of times.
3. Relate the state count to Gate B, and the work counter to the algorithm of Gate C.
4. Prove the advertised form `O(n1*n2*min(d1,l1)*min(d2,l2))` **only if** its operations and data-structure assumptions justify it. Explicitly distinguish expected-time hashing from deterministic worst-case operations; state memory use separately.
5. If actual implementation operations entail an extra logarithmic or representation factor, prove that bound and document the difference. Do not force a desired asymptotic statement by silently postulating constant-cost operations.

**Gate D:** the complexity theorem names an executable algorithm and cost model and has no free assumption asserting the very state-size inequality it intends to prove.

### E. Rust via Charon/Aeneas

1. Run an **early small feasibility spike** translating a real Rust tree/sequence state operation to Lean, establishing toolchain versions and supported data representations before a major Rust rewrite.
2. Create a small safe Rust core independent of PyO3, Python callbacks, runtime trait objects, concurrent scheduling and third-party container internals. Keep the public I/O contract explicit and deterministic.
3. Translate the maintained Rust source using pinned, compatible Charon/Aeneas revisions and compile its generated Lean; do not manually modify generated definitions to obtain a proof.
4. Prove representation/validation, index safety, memo-table invariants, DP transition correctness and witness reconstruction against the independent Lean specification.
5. Establish an end-to-end theorem about the **translated Rust entry point**: for accepted inputs under stated bounds, it succeeds (or returns only documented errors), its witness is valid and its score is optimal.
6. Add a clean regeneration check comparing extracted Lean against checked-in/generated proof dependencies. Include `#print axioms` or an equivalent audit on the public theorem's dependencies.

**Gate E:** Rust source -> Charon/Aeneas -> generated Lean -> proved refinement to the independent optimum, with reproducible tool pins and documented trusted boundaries. An extraction-only demo does not meet the gate.

### F. Performance and application integration

1. Preserve existing Python, Cython and PyO3/Rust implementations as unverified comparison baselines; do not replace them just because the proof code is complete.
2. Use an independently enumerating contraction oracle for tiny instances and independent witness validation for all sizes. Differentially compare optimal values across all available backends; permit different equally optimal witnesses.
3. Measure CPU time, allocations, peak RSS, state counts, memory and scaling on chains, stars, balanced trees, combs, brooms, random trees and existing applied module-tree cases.
4. Profile before optimizing. Each optimization requires a refined correctness argument or a verified equivalent representation, and a before/after benchmark.
5. Integrate the verified Rust core behind the existing NetworkX-facing ordered-tree API with explicit conversion/witness mapping. Treat labels, affinities and weighted scoring as separately specified extensions.
6. Keep the unordered weighted algorithm family distinct; its matching and distance-penalty semantics are outside the 2004 proof.

**Gate F:** verified Rust matches the independent oracle in its feasible exhaustive domain, is usable through the intended API, and has measured performance sufficient to justify its use.

## 5. Work packages and proposed order

| ID | Deliverable | Depends on | Done when |
| --- | --- | --- | --- |
| W0 | Stabilize the fresh Lean build, toolchain and baseline inventory | none | `lake build` passes from clean checkout; dependency lockfile and exact status recorded |
| W1 | Independent tree and contraction-based specification plus exhaustive oracle | W0 | edge/root conventions explicit, examples and small oracle checked |
| W2 | Fresh balanced-sequence definitions and full contraction/containment equivalence | W1 | Gate A |
| W3 | State decomposition mathematics, actual-leaf cardinality bound | W2 | Gate B |
| W4 | Independent DP optimality and witness construction | W2; W3 for paper theorem chain | Gate C |
| W5 | Algorithm-specific cost semantics, corrected Theorem 3 | W3, W4 | Gate D |
| W6 | Minimal Aeneas translation spike and pinned workspace | W0; parallel to W1-W3 | a real Rust function translates, generated Lean builds, basic refinement theorem checks |
| W7 | Proof-friendly Rust implementation and proof of translated entry point | W4, W6 | Gate E |
| W8 | Complexity refinement for actual Rust data structures, if needed | W5, W7 | quantified and proved cost claim within stated model |
| W9 | Independent tests, API adapter, benchmarks, optimization | W7 | Gate F |
| W10 | CI, theorem inventory, full paper coverage audit and documentation | all | fresh checkout reproduces results and claims |

Work can be parallel where dependencies permit, but **never let Rust implementation details dictate the abstract theorem statements**. Conversely, do not design an elegant but non-extractable Lean-only algorithm and assume an implementation proof will be easy afterward. Use the early W6 spike to inform representation decisions.

## 6. Assurance ledger

Track accepted claims in a small `proofs/PROOF_STATUS.md` once there are actual proof targets. Give exact theorem identifier, hypothesis list, source file, build command and classification: `specified`, `proved`, `conditional`, `extracted`, `tested`, or `open`. An item is `proved` only after the fresh Lake build and theorem-dependency review.

Status after the user-reported successful local `lake build` (dependency audit still pending):

| Target | Status |
| --- | --- |
| Independent tree/embedded-subtree specification | compiled in the reported local build; paper-semantics equivalence and axiom audit pending |
| Tree/Dyck encoding and forward contraction soundness | compiled locally (maintainer-reported) |
| Converse contraction/completeness and two-way equivalence | authored; local build pending |
| Equivalence to the paper's exact annotated containment relation | open |
| Paper combinatorial results and actual-leaf state bound | open |
| LCBS DP optimality vs. independent optimum | open |
| Tree witness correctness | open |
| Algorithm-specific Theorem 3 complexity | open |
| Charon/Aeneas extraction of new Rust core | open |
| Generated-Rust-to-spec refinement | open |
| Rust valid-input safety and error contract | open |
| Python adapter correctness | open |
| End-to-end benchmark comparison | open |

**No theorem from the retired proof tree is part of the new trusted result.** We do not inherit its build status or proof claims. Keep legitimate external assumptions (Lean kernel, standard mathematics libraries, tested translation-tool semantics and explicitly modeled data-structure contracts) visible. The goal is no local `sorry`, `admit`, arbitrary `axiom`, or opaque unverified operation in the accepted correctness chain.

## 7. Repository layout: build as needed

```text
proofs/
  README.md
  lean-toolchain, lakefile.toml, lake-manifest.json
  SubtreeProofs/
    Paper2004/
      OrderedTree.lean
      BalancedSequence.lean
      Containment.lean
      Decomposition.lean
      Cardinality.lean
      Optimality.lean
      Complexity.lean
    Algorithm/
      DP.lean
      Witness.lean
      Correctness.lean
    Rust/
      Generated/                 # reproducible translator output
      Refinement.lean
      Safety.lean
rust/
  crates/
    lozano_valiente_core/       # future proof-friendly crate
  src/lib.rs                    # existing PyO3/backend; unchanged by proof reset
networkx_algo_common_subtree/  # existing API and independent Python reference
```

This is a responsibility map, not a mandate to create empty modules. Make choices after W1 and W6, and avoid speculative compatibility shims and generic loose symbol names. There should be one canonical specification and one accepted production proof chain, not a series of `v2`, `v3`, `final` modules.

## 8. Testing and release gates

- **Mathematics:** enumerate all small ordered trees/pairs within a fixed practical bound; compare DP with a distinct contraction-based oracle and validate each reported witness. Retain minimized counterexamples, especially those that separate actual leaf counts, order constraints, and root semantics.
- **Rust:** tests for valid/invalid encodings, score boundaries, equal-score ties, overflow/index handling, degenerate tree shapes, reproducibility and any deterministic container invariants.
- **Formal:** `lake build`, explicit theorem dependency/axiom audits, generated-code regeneration, Rust test/fmt/clippy, and a clean-build compatibility matrix pinned after the W6 spike. The critical theorems must compile without importing legacy code.
- **Performance:** compare against actual Python/Cython/PyO3 baselines with recorded hardware, versions, flags, warmup policy, distributions and state counts. Prove asymptotics through the model; report measured performance separately.
- **Integration:** verify the ordered API's representation and output mapping. Do not silently change semantics of unordered, labeled or weighted calls to match the new core.

Keep CI proportional to real failures: target core invariants and regressions, avoid source-text/process meta-tests, and keep full exhaustive or large benchmark runs optional outside appropriate release jobs.

## 9. First execution cycle: concrete acceptance checklist

1. Preserve the passing `OrderedTree.lean` foundation. Reproduce `lake build`
   on Lean 4.35.0 from a fresh checkout, inspect accepted theorem dependencies
   with `#print axioms`, and keep `PROOF_STATUS.md` current. The first local
   build success has been reported; clean-checkout reproducibility is still open.
2. Pin toolchain and commit `lake-manifest.json`. Add a minimal CI job running
   the actual Lean build (not a test of file text or theorem names).
3. Write a tiny **contraction-enumerating** oracle independent of the Dyck-word
   recurrence. Fix root conventions and examples for contraction of a root
   child, a nested edge, and sibling splicing. Exhaustively compare true leaf
   and edge counts on small trees.
4. Prove tree/forest encoding and decoding round trips, with semilength, edge,
   depth, and true-leaf invariants. Then prove both directions of sequence
   containment versus the tree contraction closure.
5. In parallel, translate a small real Rust state/encoding operation with
   Charon/Aeneas. Compile the generated Lean and prove a nontrivial
   representation/refinement lemma; pin the compatible revisions.
6. Derive decompositions and finite state sets `D`, `R`, `S` and the true-leaf
   cardinality bound, with exhaustive discriminators for chains, stars, and
   unary cases.
7. Prove independent LCBE/LCBS numeric DP optimality and witness correctness,
   then connect exact operation counts to the corrected complexity statement.
8. Isolate a proof-friendly Rust core without disrupting the currently
   integrated optimized baseline; prove its translated entry point correct,
   benchmark on adversarial and practical trees, then integrate deliberately.

The next milestone is **a successful local check of the converse theorem,
then an independent contraction oracle and the paper-containment crosswalk**, with axiom auditing and clean-checkout CI for the
now-compiling foundation. Build success alone leaves the central mathematical
correspondence and the paper algorithm unproved.

## 10. Sources

- Lozano & Valiente (2004): https://www.cs.upc.edu/~antoni/subtree.pdf
- Aeneas / Charon project: https://github.com/AeneasVerif/aeneas and https://github.com/AeneasVerif/charon
- Aeneas getting started (verify commands against pinned revision): https://github.com/AeneasVerif/aeneas/blob/main/documentation/getting-started.md
- Existing application code, tests and benchmark suite in this repository (not a source of mathematical truth)

The historical `proofs` branch remains accessible through Git, but it is intentionally excluded from the new work plan and formal dependency graph. Cross-paper reuse and verification principles live in the [program charter](verified_common_subtree_research_program.md).
