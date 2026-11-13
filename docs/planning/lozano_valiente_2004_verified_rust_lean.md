# Verified Lozano-Valiente Common Subtree Algorithm: Rust, Aeneas, and Lean

Status: revised after source and proof-claim audit (2026-11-13)
Prepared: 2026-11-13
Primary paper: Antoni Lozano and Gabriel Valiente, *On the Maximum Common Embedded Subtree Problem for Ordered Trees*, 2004.
Repository: `networkx_algo_common_subtree`

## 1. Goal and definition of done

Deliver a practical, fast Rust implementation of the Lozano-Valiente (2004) maximum common embedded subtree algorithm for rooted **ordered** trees, with a machine-checked Lean development of the paper and a machine-checked connection from the actual Rust implementation to its mathematical specification using Charon and Aeneas.

The final result must establish, separately:

1. **Mathematical correctness:** the formal statement of longest common balanced sequence (LCBS) agrees with maximum common embedded subtree under the paper's edge-contraction semantics, and its recurrence computes an optimum.
2. **Paper coverage:** definitions, auxiliary cardinality/decomposition results, correctness, and the stated complexity theorem have Lean proofs with a checked dependency chain and accurately scoped assumptions.
3. **Implementation correctness:** extracted Lean definitions come from the maintained Rust source; for valid inputs, the implementation succeeds, returns a structurally valid witness, and attains the optimum.
4. **Performance:** the Rust algorithm is benchmarked against the present Python, Cython, and PyO3/Rust implementations, with reproducible methodology and regression thresholds derived from measured baselines.
5. **Integration:** the verified core is accessible behind the existing NetworkX-facing API without changing the meaning of public options, or any remaining differences are explicit, tested, and documented.
6. **Reproducibility:** pinned toolchains, regeneration checks, Lean builds, Rust tests, differential tests, and representative benchmarks work from a fresh checkout.

A Lean proof of an abstract recurrence alone does not satisfy item 3. Successful Aeneas extraction without an implementation-to-spec theorem also does not satisfy item 3. A measured speedup does not establish the paper's asymptotic bound.

## 2. Source audit: 2026-11-13 snapshot

The supplied `git-well` archive has detached HEAD `54a5cebb20dc22a193820585f3e3f35ddd16f7e8`. The archive retains the history of that HEAD but not the repository's other branch refs. The snapshot is sufficient to assess its committed files; it is not evidence that another branch's work was lost.

### 2.1 Useful history to retain

| Commit | Content | Disposition |
| --- | --- | --- |
| `9d67c41` | Experimental Droschinsky/Kriege/Mutzel unordered, weighted algorithms, Rust crate, independent Python reference and tests | Retain as a distinct algorithm family; do not conflate with Lozano-Valiente |
| `ddd902c` | Lozano-Valiente write-up, reusable Lean helpers, Aristotle attempts | Preserve as historical formalization material; distinguish experiment/prompt files from accepted proofs |
| `efea2dd` | Correctness docs, independent witness validation, Rust/Python reference tests, fixtures | Retain; extend with ordered-tree paper-specific oracles |
| `54a5ceb` | PyTorch-sized benchmark trees, reporting, benchmark scripts, notes | Retain useful authored material; review and isolate incidental build output |

Earlier PyO3/Rust implementation and tuning commits (`52c2a04` through `fee67db`) are relevant performance history. The reverted range-list state-pool experiment (`48fa742` and `fee67db`) should remain discoverable as evidence of a tested design choice. There is no present reason to rewrite this historical sequence.

**Specific cleanup:** `networkx_algo_common_subtree/cmake_install.cmake` was committed in `54a5ceb` and contains generated, machine-specific install paths. Remove it from tracking in a separate, reviewable cleanup commit and ignore that generated path. Do not discard the benchmark source/tests together with this generated file.

### 2.2 Formalization recovery: high priority

The current snapshot's `next_steps.md` (text dated 2026-03-01) describes a much more advanced `proofs/SubtreeProofs/Lozano-v6.lean` than is included **in the current checked-out branch**. The local `proofs/` directory does exist: it holds reusable libraries, `Attempts/`, and a pinned manifest, but not `Lozano-v6.lean` or a `lakefile.toml`. `proofs/Main.lean` imports `SubtreeProofs`, which is also absent from that snapshot. The separate `proofs` GitHub branch contains the mature experimental version:

- branch: `proofs`
- observed branch HEAD: `f147a30a2d1e8a3c0e03a00caddc4a8f93db24df`
- `proofs/SubtreeProofs/Lozano-v6.lean`: approximately 2,530 lines, with an implementation of paper-level definitions and extensive proof/runtime scaffolding;
- `proofs/lakefile.toml`, `proofs/SubtreeProofs.lean`, older Lozano versions, and additional companion modules are also on that branch.

The archived `next_steps.md` reports that the v6 development built successfully at the time and reduced the remaining leaf-bound obstacle to a degenerate-tail inequality. This build has **not** been rerun during this audit. Text inspection of the recovered v6 source found no `axiom` declaration and one `sorry` token in commentary; neither observation substitutes for a fresh elaboration or dependency audit.

Start by fetching and inspecting the branch, preferably using a temporary worktree or a file-level comparison. Do **not** merge the complete `proofs` branch over the current tree blindly. Its module layout, Lake files, and version pins need reconciliation with the later May and November commits.

Useful non-destructive inspection commands:

```bash
git fetch origin proofs
git show origin/proofs:proofs/SubtreeProofs/Lozano-v6.lean | head -45
git show origin/proofs:proofs/lakefile.toml
git diff --stat HEAD origin/proofs -- proofs/
```

Bring the needed proof source, its imports and Lake configuration into a functioning Lean workspace while retaining original provenance. The task is **selective integration and proof repair**, not rediscovery from scratch. Audit older variants for additional useful theorems rather than indiscriminately deleting them. Keep superseded attempts in an `Attempts`/historical area, excluded from the trusted build target.

### 2.3 Independent critical review of the existing `Lozano-v6.lean`

**Do not equate the absence of `sorry` with a completed formalization of the paper.** The most mature file has about 2,530 lines, nontrivial proofs of the `D`/`R`/`S` decomposition machinery, and an older reported successful build. It also contains important specification shortcuts. Audit the theorem **statements**, not merely their proof terms or names.

| Priority | Existing declaration / source location on `proofs` branch | What is established / remaining requirement |
| --- | --- | --- |
| P0 | `BSeq.leaves` (around line 364), `lemma7` (743), `theorem1` (778) | The recurrence `leaves nil = 1; leaves (cons x y) = leaves x + leaves y` implies `leaves x = semilen x + 1`. Thus the proof that `depth x <= leaves x` makes `lemma7` a corollary of the depth bound; it does **not** prove the bound with real tree leaves. Prove a corrected tree/forest-leaf theorem separately. |
| P0 | `Contract1` (906), `EmbSub` (911), `theorem2` (987) | `Contract1` describes root-level contractions only. `EmbSub` is *defined* as `encode u ⊑ encode t`, so Theorem 2 bypasses the equivalence to the reflexive-transitive closure of contractions at **arbitrary child positions**. Establish that equivalence in both directions. |
| P0 | `lcsLen` (301), `LCBS` (294), `lemma8` (1008) | `lcsLen` is **defined by** the Lemma 8 recurrence, while `LCBS` is a separate noncomputable choice of a maximum. `lemma8` unfolds `lcsLen`; prove `lcsLen s t = semilen (LCBS s t)` or an equivalent independent optimality statement. |
| P0 | `ContainedDef2` (165), `ContainedRTC` (193) | The paper's inductive containment and the operational deletion-closure relation are both present, but no equivalence bridge was found in v6. Prove both implications, independently of the DP. |
| P0 | `mcesAlgPaper` (1037), `mcesExpectedCost` (1894), runtime theorems (1997+) | `mcesAlgPaper` uses noncomputable `Classical.choose` through `LCBS`; it is not an executable DP. `mcesExpectedCost` is a synthetic operation-count expression. Prove runtime against an actual executable state machine with a justified step/cost correspondence. |
| P1 | `lemma7_tree_of_nil_tail_bound` (1372), tree-leaf theorem wrappers | The stronger, tree-leaf-specific Lemma 7 is only conditional on the `cons x nil` case. This is a genuine unresolved combinatorial obligation, distinct from the already proved weaker `lemma7`. |
| P1 | `SubtreeProofs.Lib.OrderedTree.Tree` and `LozanoValiente2004.OTree` | Two tree datatypes exist. Pick a canonical one or prove an explicit isomorphism and transfer of node, depth, leaves, encoding, and contractions. |
| P1 | Current branch `proofs/README.md`, `Main.lean`, and missing `lakefile.toml` | The checked-out source tree does not reproduce the historical `v6` build. Reconcile configurations and replace the stale README with a truthful module/build inventory. |

**Mathematical source discrepancy requiring its own issue and resolution.** On page 7 of the published PDF (PDF page index 6), the paper prints `ell(lambda)=1` and `ell(0x1y)=ell(x)+ell(y)` while describing `ell` as the number of tree leaves. For a one-edge tree (`0 lambda 1 lambda`), these equations yield `2`, but the tree has `1` leaf. Inductively they imply `ell(x)=|x|+1` for *every* balanced sequence. Therefore the printed recurrence cannot represent the number of leaves of the rooted tree. Its written Lemma-7 derivation does not directly justify the claimed dependence on true leaves. Keep the printed algebraic recurrence as a distinctly named **paper measure** if needed for textual correspondence. Formalize actual tree leaves via a tree/forest distinction, repair the proof, and record whether the final theorem is identical, corrected, or weakened. Do not silently substitute a new definition into a theorem that claims literal correspondence to the printed paper.

The v6 file already includes `leavesPairOfSeq`, `treeLeavesOfSeq`, `forestLeavesOfSeq`, a nonempty-tail proof, and the conditional reduction to the empty-tail case; those are the right pieces to reuse. They do not yet remove that final hypothesis.

**Small independent diagnostic (2026-11-13):** enumerated every balanced sequence with 0 through 10 edge pairs (Catalan counts totaling **23,714**); computed `R`, `S`, `D` as sets and the actual leaves of the decoded rooted tree. No counterexample was found to `|S(x)| <= |x| * actualLeaves(x) + 1` or the corresponding `D` bound using `min(actualDepth,actualLeaves)`. This is exploratory evidence for the corrected statement, not a Lean proof or a checked-in regression suite. Convert this check to a small independent, reviewed test/oracle during W1.

**Acceptance rule:** the public theorem index must identify the exact *independent specification* each theorem establishes. Names like `theorem2`, `lemma8`, and `theorem3_runtime_bound` cannot be marked `paper_proved` merely because Lean checks their current statements. Prefer positive, explicit theorem names and separate `paper_printed`, `mathematically_corrected`, `abstract_algorithm`, and `rust_refinement` views.

### 2.4 Baseline validation

From the supplied snapshot, with Python 3.13.5, `PYTHONPATH=. pytest -q -o addopts='' tests` yielded **46 passed and 2 skipped**. The two skipped tests require the compiled `networkx_algo_common_subtree._rust` extension. The normal pytest configuration requests `--xdoctest`, which was not installed in the review environment; the command above overrides only that configuration for a focused audit.

`python dev/bench_pytorch_sized_common_subtree.py --summary` produced seven deterministic ResNet-like cases (166 left nodes, 166-319 right nodes). That checks fixture generation, **not** Rust performance. Rust, Lean, Charon, and Aeneas were unavailable in this review environment, so native compilation/extraction and proof status remain to be established in the project's normal toolchain.

### 2.5 Architectural inventory

- `networkx_algo_common_subtree/tree_embedding.py`: public ordered-tree embedding API and balanced-sequence conversion.
- `networkx_algo_common_subtree/balanced_embedding.py`: pure-Python recursive/iterative LCBS implementations.
- `rust/src/lib.rs`: existing optimized PyO3 Rust backend; includes interned states, memoization, Python-object interoperability, affinity caches, and floating-point scoring.
- `networkx_algo_common_subtree/tree_isomorphism.py` and balanced isomorphism backends: related but distinct stricter objective.
- `proofs/LozanoValiente2004-writeup-v1.md`: working paper transcription/explanation, useful as an index, not an authoritative substitute for the paper.
- `proofs/SubtreeProofs/Attempts/`: historical AI proof attempts, some with explicitly assumed statements.
- `rust/crates/common_subtree_algorithms/`: independent unordered-tree Droschinsky research crate, **not** an implementation of Lozano-Valiente.
- `networkx_algo_common_subtree/common_subtree_reference.py`: brute-force oracle for the unordered weighted family, **not** yet an independent paper-specific LCBS oracle.

Do not force the unordered weighted solver through the ordered LCBS specification. Keep its correctness, optimization, and future formalization as an independent workstream.

## 3. Scope and mathematical contracts

### 3.1 Paper-exact initial core

Work initially with finite, rooted, ordered, unlabeled trees and edge counts. Preserve left-to-right child order. Define exactly which contraction operations are allowed and how contraction splices an ordered child's children into the parent. Define the empty sequence / single-rooted-node case explicitly.

Formalize the balanced-sequence grammar `nil | cons head tail`, corresponding to `lambda | 0 head 1 tail`, its length as **number of edge pairs**, and its interpretation as a forest under one root. Distinguish:

- the empty balanced sequence (zero edges, one represented rooted node in the tree model);
- the empty forest (zero components);
- tree leaves vs. forest leaves for an empty tail;
- edge-score `m` vs. nonempty subtree node count `m + 1`;
- the paper's `|x|` (edge-pair count) vs. the Python API's node/affinity score.

Prefer a small exact data model with stable node/edge IDs so a returned witness can be related back to input trees. Define tie-breaking deterministically for execution and testing, but do not make arbitrary tie-breaking a premise of optimality.

### 3.2 Paper theorem and runtime claim

Target the 2004 paper's ordered-tree runtime expression:

`O(n1 * n2 * min(d1, leaves1) * min(d2, leaves2))`.

Separate the **combinatorial bound on decomposed states** from the **cost of constructing canonical state IDs** and the **dynamic-programming accesses**. The paper's constant-time dictionary steps rely on expected-time hashing; a fully deterministic worst-case bound requires another data-structure argument. State the exact assumptions of each runtime theorem and whether the result is expected or worst-case. The complexity theorem must describe the executable algorithm actually analyzed, not an invented unit-cost stand-in unrelated to the Rust implementation.

### 3.3 Later extensions, each with its own contract

1. Exact labels and compatibility constraints (paper's labeled extension).
2. Nonnegative integral weights, with a stated objective and witness scoring; show equivalence to the unlabeled case under unit weights.
3. Checked integer widths and range/overflow preconditions; avoid making a floating-point algorithm the initial formal target.
4. Public `node_affinity` callable behavior and float/fractional weights. Address NaN, infinity, negative values, Python exceptions, and tie-breaking explicitly instead of assuming arithmetic over real numbers matches `f64`.
5. Ordered subtree **isomorphism**, forests, flexible roots, and any current API-specific behavior: independent refinement obligations, not silent consequences of the embedding theorem.
6. Unordered weighted Droschinsky algorithms: later separate formalization with different data models and matching lemmas.

## 4. Proposed implementation and proof layout

The exact names can be adjusted during integration, but preserve the separation of responsibilities:

```text
proofs/
  lakefile.toml, lean-toolchain, lake-manifest.json
  SubtreeProofs/
    Paper2004/
      BalancedSequence.lean       # grammar, append, head/tail, tree encoding
      Contraction.lean            # ordered embedded-subtree semantics
      Decomposition.lean          # D, R, S and Lemmas 1-5
      Cardinality.lean            # Facts, Lemmas 6-7, Corollary 2, Theorem 1
      Optimality.lean             # Theorem 2 and Lemma 8
      Complexity.lean             # Theorem 3 with explicit cost hypotheses
    Algorithm/
      Specification.lean         # independent executable recurrence and witnesses
      StateIndex.lean            # canonical states and indexing invariant
      Correctness.lean           # executable mathematical algorithm vs. spec
    Rust/
      Generated/                 # reproducible Charon/Aeneas output
      Refinement.lean            # generated definitions vs. independent spec
      Safety.lean                # valid input implies success / no panics
      Cost.lean                  # explicit step model where feasible
    Lib/                          # existing generic lemmas, retained
    Attempts/                     # historical attempts, never a trusted import root
rust/
  crates/
    lozano_valiente_core/         # extraction-friendly safe Rust core
    common_subtree_algorithms/    # existing separate Droschinsky family
  src/lib.rs                      # existing PyO3 backend; adapter/migration path
networkx_algo_common_subtree/
  ...                             # existing public API and Python references
```

Avoid creating multiple permanent generic utility modules with ambiguous, duplicate function names. Prefer distinctive, domain-specific names so symbols remain easy to grep. Avoid speculative abstractions, compatibility layers, and process-only tests. Refactor shared code only when there is a real, tested ownership boundary.

The verified core should use safe, sequential, extraction-supported Rust constructs, small transparent data types, explicit indices, and error-bearing operations. Keep PyO3, arbitrary Python objects, callbacks, thread scheduling, and external fast hash maps outside the first extraction target. Those boundaries must eventually be accounted for in a verified adapter/refinement argument if end-to-end correctness is claimed.

## 5. Work packages and completion gates

Work packages below are ordered by dependency, not by estimated calendar time. Close each with a concrete commit, passing checks, and an updated proof/assumption ledger.

### W0 - Reconcile source, history, and toolchains (blocking)

- [ ] Preserve the present branch and its history; record HEAD, refs, working tree status, and any unpublished files.
- [ ] Compare the local `proofs/` tree with `origin/proofs` (including v3-v6), companion modules, Lake config, Mathlib pins, and copied May work; treat the existing local files as input, not lost artifacts.
- [ ] Selectively integrate the best Lean modules without overwriting unrelated Rust/Python developments or keeping obsolete modules in the default build.
- [ ] Make `proofs/` a clean, reproducible Lake workspace; repair `proofs/Main.lean` or remove it from build if it is a stale scaffold.
- [ ] Run the historical v6 target and full Lake build; capture exact results, theorem statements, direct hypotheses, `#print axioms` closures, and mismatches with independent paper specifications.
- [ ] Record rustc/Cargo, Charon, Aeneas, Lean, and Mathlib versions by actual commit or toolchain pin; keep compatible Aeneas Lean libraries on the same revision as the translator.
- [ ] Run Python tests with configured dependencies, Rust crate tests, PyO3 backend tests, `cargo fmt`, and `cargo clippy`; record failures and the initially skipped tests.
- [ ] Remove the generated tracked `cmake_install.cmake` in a targeted follow-up cleanup.

**Gate W0:** current sources have a reproducing baseline and the local and remote proof trees are reconciled or explicitly indexed; no performance or formal claim relies on a historical build log.

### W1 - Create an independent, executable mathematical specification

- [ ] Define the ordered-tree and balanced-sequence objects, contraction relation, containment, common-embedding witness and optimum without referring to a production implementation.
- [ ] Prove round-trip and structural correspondence between ordered trees and balanced sequences, including child order, contractions at any depth, and lengths; specifically bridge `ContainedDef2` to `ContainedRTC` and encoding containment to contraction RTC.
- [ ] Implement a slow, independently structured exhaustive oracle for small ordered trees (actual contraction/embedding enumeration, not a copy of Lemma 8).
- [ ] Make edge/node scoring, root retention, empty inputs, labels, and repeated identities explicit; create focused counterexample fixtures for each ambiguity, including the single-edge `paperLeaves=2` vs. `actualLeaves=1` discrepancy.
- [ ] Establish an independently checkable witness verifier and score calculator.

**Gate W1:** representative hand-checked and exhaustively generated small cases have one unambiguous expected objective, and the mathematical model is stable.

### W2 - Finish the *whole paper* Lean formalization

Paper coverage checklist:

- [ ] Definition 1, Fact 1: balanced sequence / tree encoding and linear construction.
- [ ] Definition 2: balanced-sequence containment and its contraction interpretation.
- [ ] Definition 3: head and tail decomposition.
- [ ] Definition 4, Lemmas 1-5, Corollary 1: `D`, `R`, `S`, append/decomposition closure.
- [ ] Fact 2: `|R[x]| = |x| + 1`.
- [ ] Lemmas 6 and 7: separate the printed (degenerate) `ell` recurrence from the actual leaf-count bound; prove corrected, tree-leaf Lemma 7, including exact empty-tail cases.
- [ ] Corollary 2 and Theorem 1: `|D[x]|` bound using `min(depth, leaves)`.
- [ ] Definition 5 and Theorem 2: contraction-based embedding at any position (independent of encoding) equivalent to sequence containment/LCBS in both directions.
- [ ] Lemma 8: sound, complete, optimal dynamic-programming recurrence, with an explicit theorem relating the recursive `lcsLen` result to the independently chosen `LCBS` optimum.
- [ ] Theorem 3: concrete runtime/cost relation and asymptotic statement with documented dictionary assumptions, over an executable algorithm instead of the noncomputable `mcesAlgPaper`.
- [ ] Labeled-tree extension: formal theorem for the scope actually stated; account for the paper's informal prose separately.

**Known immediate subgoal:** the existing v6 scaffold reduces the unconditional tree-leaf result to the nil-tail obligation:

```text
forall x, |S(cons x nil)| <= semilen(cons x nil) * treeLeaves(cons x nil) + 1
```

Use `S_cons_nil_eq_D` and the existing nonempty-tail lemma, but first establish the corrected tree/forest leaf conventions and search for a smallest counterexample to every proposed strengthening. Do not force an invalid exact constant. If a corrected/slack statement is needed, state and prove it transparently, then derive the required asymptotic result. A theorem with an explicit `h7tree`, `hnil`, or cardinality hypothesis is valuable intermediate work but is **not** the unconditional paper theorem.

**Gate W2:** the paper-facing theorem graph builds from checked definitions, repaired real-leaf bounds, and proofs; no `sorry`, `admit`, arbitrary axiom, or undeclared assumption occurs in the accepted dependency closure. Assumptions modeling dictionary runtime are explicitly named, not hidden inside a theorem claiming unconditional worst-case execution.

### W3 - Verify the paper-level executable recurrence

- [ ] Define a finite DP state space for pairs of balanced-sequence decompositions, with an explicit structural ranking to justify termination.
- [ ] Prove `head`, `tail`, `head ++ tail` dependencies are smaller or already available in a valid evaluation order.
- [ ] Prove dynamic programming returns the value of the LCBS specification on all valid inputs.
- [ ] Add a witness reconstruction algorithm; prove it produces a feasible embedded common tree with optimal value (including equal-score ties and empty matches).
- [ ] Establish normalization/canonicalization of states and identify which equality notion permits safe memoization.
- [ ] Isolate a formal cost counter for recurrence steps/state accesses.

**Gate W3:** executable Lean specification has optimality proved *against contraction/containment rather than an unfold-equivalence*, witness validity, termination, and an explicit dependency/cost model; no external Rust code is needed to state these theorems.

### W4 - Rust proof-friendly core and first Aeneas extraction

- [ ] Choose whether to extract a carefully factored version of existing `rust/src/lib.rs` or create the small `lozano_valiente_core` crate. Prefer reuse of proven recurrence/state designs while avoiding PyO3-specific machinery in the verified part.
- [ ] Make input validation, balanced-token parsing, state construction, memo indexing, DP update, and witness reconstruction explicit and testable.
- [ ] Use checked indexing and arithmetic or prove their preconditions. Define behavior for memory/index limits and invalid encodings as `Result`/typed error values.
- [ ] Choose Aeneas-supported Rust collections/algorithms empirically with a minimal extraction spike; do not redesign the entire solver around a guessed tool limitation.
- [ ] Run the exact pipeline: `charon cargo --preset=aeneas ...` then `aeneas -backend lean ...` with pinned versions.
- [ ] Compile the generated Lean definitions against the pinned Aeneas Lean library; commit generated sources or an equivalent reproducible, immutable output snapshot as the proof dependency.
- [ ] Add an extraction/regeneration check that fails when translated source and reviewed generated definitions diverge.

**Gate W4:** the actual Rust core extracts and the generated Lean builds in CI; a trivial representative Rust function already has a real correspondence theorem to an independent specification.

### W5 - Rust-to-spec correctness proof, function by function

- [ ] Prove parsing/validation yields an ordered-tree/sequence satisfying all representation invariants.
- [ ] Prove state-ID equality and canonicalization are collision-safe and cannot conflate distinct subproblems; distinguish correct hash-table equality from uniqueness of hashes.
- [ ] Prove memo-table invariants and the DP transition specification, including the exact meaning of cached values and evaluation order.
- [ ] Prove witness reconstruction uses legal matched edges/contractions and preserves order.
- [ ] Prove extracted Rust's final value equals the independent Lean optimum, and its witness passes the independent verifier.
- [ ] Prove valid-input execution succeeds under stated representability/resource preconditions (bounds, overflow, indexing, handled errors).
- [ ] Identify and eliminate opaque operations or trusted stubs in the accepted correctness path, or explicitly narrow the theorem until their specifications are justified.

**Gate W5:** a theorem about the **generated Rust entry point** implies correct optimum and valid witness for the specified domain. The proof can be regenerated against a fresh extraction and checked without importing historical attempt files.

### W6 - Complexity and representation refinement

- [ ] Derive the number of distinct decomposition states using proved Theorem 1; connect actual internal state IDs to these mathematical states.
- [ ] Count DP iterations, state transitions, table accesses, reconstruction, and encoding costs in the same model as the verified implementation.
- [ ] Account for state-key construction, hashing/equality, allocations, resizing, and score/callback evaluation rather than silently treating all as unit cost.
- [ ] Prove the paper's `O(n1*n2*min(d1,l1)*min(d2,l2))` under its appropriate expected-time dictionary operations, or document a different bound for the implemented deterministic index structure.
- [ ] State memory complexity separately; measure peak allocations and state counts as a check against the model.
- [ ] If a fast unverified hash map is retained behind a specified boundary, keep its performance claim conditional and its safety/correctness obligation explicit.

**Gate W6:** the reported complexity theorem applies to a named implementation model with a checked bridge to its states and an honest dictionary cost assumption; its supporting code can report work counters that agree with the proof model.

### W7 - Python/NetworkX API refinement

- [ ] Preserve public APIs `maximum_common_ordered_subtree_embedding` and related isomorphism methods; document semantic differences instead of guessing equivalence.
- [ ] Verify conversion from `OrderedDiGraph` to the core's ordered tree, unique IDs, and inverse mapping of result witnesses.
- [ ] Keep Python-specific affinity callbacks and float weights outside the exact initial theorem. Add a separately specified weighted adapter once numerical semantics are fixed.
- [ ] Compare `impl=iter`, recursive, Cython, existing Rust, and verified Rust for result values and independently verified witnesses; allow different optimal witness choices where ties permit them.
- [ ] Explicitly check invalid forests, empty graphs, inconsistent mappings, duplicate labels, deep/pathological trees, and exceptions.
- [ ] Route production traffic only after parity and benchmarks justify the change; retain a reasonable rollback/diagnostic path during migration.

**Gate W7:** the verified core is available through the intended real API, with a typed and tested boundary and no unreviewed semantic drift.

### W8 - Independent, high-value correctness testing

- [ ] Exhaustive small rooted ordered trees and all small pairs; independently enumerate contraction minors or embeddings and compare optimal values.
- [ ] Verify returned witnesses independently, not just solver-vs-solver score agreement.
- [ ] Property-based tests: symmetry of optimal value, identity, relabeling invariance under compatible affinities, monotonicity under allowed contractions, child-order sensitivity, and extension monotonicity where premises justify it.
- [ ] Differential tests across Python, Cython, old Rust, and verified Rust with fixed seeds and minimized counterexamples.
- [ ] Test degeneracies behind Lemma 7: `nil`, singleton child, empty tail, long paths, stars, brooms, deep chains, wide shallow branching.
- [ ] Test overflow/error paths, adversarial/equal-hash keys where applicable, repeated affinities, and large but valid state-ID tables.
- [ ] Mutation/negative tests should target real invariant failures, not tests of source-text style or tests-of-tests.
- [ ] Record every found counterexample as a concise minimized fixture plus root-cause explanation.

**Gate W8:** all backends agree with an independent oracle on the tractable exhaustive domain, and the Rust proof is complemented by boundary and integration tests.

### W9 - Performance engineering and benchmark discipline

- [ ] Establish baseline times and peak memory for every available backend, on known hardware/toolchains, before optimizing or retiring any backend.
- [ ] Profile (rather than assume) costs of string-token conversion, Python callbacks, state interning, memoization, allocation, hashing, witness copies, recursion, and table layout.
- [ ] Include structured tree families: chains, stars, combs, broom shapes, balanced trees, random trees, similar vs dissimilar, worst-shape candidates for `min(depth, leaves)`.
- [ ] Retain seven deterministic PyTorch-like module-tree cases as a separate applied benchmark suite; they are representative module *hierarchies*, not computation DAGs or theorem oracles.
- [ ] Measure cold/warm runs, compiler flags, backend selection, score/witness sizes, state counts, allocated bytes, peak memory, and runtime distributions; avoid drawing asymptotic conclusions from one machine/size.
- [ ] Fit scaling against `|D(s)| * |D(t)|` and node/depth/leaf characteristics; inspect outliers and explain regressions.
- [ ] Optimize one measured hotspot at a time, with formal refinement/update obligations and preserved independent-oracle agreement. Compare with existing optimized PyO3 implementation before replacing it.
- [ ] Set performance regression gates only after baseline data exist; distinguish required release gates from exploratory benchmark reports.

**Gate W9:** demonstrable performance and memory tradeoffs for realistic and adversarial inputs, with no loss of correctness or extraction fidelity.

### W10 - CI, reproducibility, and proof hygiene

- [ ] Add distinct CI jobs for Python, old/new Rust, formatting/lint, Charon+Aeneas regeneration, generated Lean build, paper proofs, and refinement proofs.
- [ ] Fail the proof jobs on `sorryAx`, `admit`, unjustified `axiom`, or trusted declarations in the critical theorem closure; keep an explicit allowlist for foundational libraries and externally specified operations.
- [ ] Run `#print axioms` (or an equivalent dependency audit) on the public optimality, safety, witness, and runtime theorems.
- [ ] Pin Rust nightly used by Charon, Charon commit, Aeneas commit, Lean version, Mathlib revision, and generation flags; enforce a clean regeneration diff.
- [ ] Keep executable correctness/performance reports reproducible; exclude build objects, `.lake`, CMake outputs, large caches, and machine-specific paths from source control.
- [ ] Make default test targets practical for normal development and keep exhaustive/large benchmark suites selectable.

**Gate W10:** fresh checkout passes the full assurance chain without using local unstaged proofs or unexplained generated code.

### W11 - Publication and maintenance

- [ ] Replace stale proof README claims with an accurate theorem inventory and build instructions.
- [ ] Provide a short mathematical exposition mapping the exact 2004 paper statements to Lean theorem names, including any corrected formulation and rationale.
- [ ] Publish API contract and verified scope (ordered/unordered, roots, labels, weights, empty inputs, score units, witnesses).
- [ ] Publish reproducible benchmark tables, hardware metadata, complexity assumptions, and comparison against pre-verification implementations.
- [ ] Document remaining trusted boundaries and extension obligations; provide stable names and minimal examples for consumers.

**Gate W11:** a new contributor can identify what has been proved, reproduce it, run the solver, and assess performance without reading the conversation history.

### W12 - Parallel but separate later research: unordered weighted algorithms

The `common_subtree_algorithms` crate implements Droschinsky/Kriege/Mutzel-style unordered, weighted problems with bipartite matching and a prototype distance-penalized embedding recurrence. Continue its independent reference fixtures and applied benchmarks. Formalizing that family requires its own graph matching and path-penalty specifications; do it only after the Lozano-Valiente verification track is stable, unless a concrete application changes priorities. No theorem from the 2004 ordered-tree paper alone verifies this code.

## 6. Assurance ledger (keep updated as code changes)

Track these claims with exact source location, theorem name, supporting command, and status. Suggested status vocabulary: `not_started`, `specified`, `tested`, `proved`, `conditional`, `blocked`.

| Claim | Initial status | Required evidence |
| --- | --- | --- |
| Paper's Definition 1-5 accurately modeled | partial | checked Lean definitions and equivalence lemmas |
| Lemmas 1-6 and structural decomposition | partial | recovered branch build and theorem inventory |
| Lemma 7 for actual tree leaves; empty-tail case | blocked | unconditional checked lemma with corrected tree/forest leaves; distinguish paper algebraic measure |
| Corollary 2 / Theorem 1 for actual leaves | conditional | no remaining `h7tree`/`hnil` hypothesis; derive bound from actual leaf counts, not `semilen+1` |
| Definition 2 vs. operational containment | unproved bridge | both directions between `ContainedDef2` and `ContainedRTC` |
| Theorem 2 LCBS vs. real edge contractions | unproved bridge | contraction relation at arbitrary depth; two-way equivalence with encoding containment |
| Lemma 8 recurrence / independent optimum | unproved bridge | `lcsLen` equal to the LCBS optimum, plus independent contraction oracle |
| Theorem 3 runtime bound for executable solver | conditional/model-only | explicit actual-leaf state bound and a cost semantics for an executable DP; dictionary assumptions |
| Rust core translation via Charon/Aeneas | not_started | pinned extraction/regeneration CI |
| Rust optimum and witness refinement | not_started | theorem about actual generated entry point |
| Rust no-failure property on valid inputs | not_started | checked safety proof and preconditions |
| Python/NetworkX adapter parity | partial | cross-backend/differential and boundary tests |
| Performance target | unmeasured | recorded baselines and regression evidence |

Mark individual lemmas proved only after `lake build` has checked the relevant declarations and the theorem's dependency assumptions have been examined. Do not inflate the ledger from comments, theorem names, historical successful build reports, or file presence.

## 7. Commit / branch policy

**Recommendation: keep the existing commits for now.** The May correctness and experimental algorithm work and the November benchmark additions represent different useful stages. Cleaning up the *working tree and sources* has immediate value; rewriting Git history does not advance the proof. Especially avoid squashing away the Rust performance experiment followed by its revert before recording what was learned.

For the November partial-work commit:

1. Preserve `54a5ceb` and the 19-file change as a recoverable checkpoint.
2. Run Rust tests/benchmarks when the native toolchain is available, then record which benchmark paths work.
3. Follow up with a focused cleanup that removes the accidentally tracked CMake install file and addresses real failures.
4. Improve logical organization with subsequent commits. Consider history surgery only much later, with a reviewed target branch and a concrete maintainability need; do not do it merely because the commit message says "partial".
5. Integrate the `proofs` branch by reviewing its specific files and provenance, not by overwriting the whole tree or discarding its history.

For future work, use reviewable commits at working boundaries: recovery, paper theorem, LCBS spec, Rust extraction, implementation refinement, adapter, benchmarks. Generated Lean output should be paired with a recorded extraction source hash, flags, and toolchain pins.

## 8. Immediate next sequence

1. **Reconcile and build `Lozano-v6.lean`** with the existing local `proofs/` tree. Preserve all source history; record theorem statements, dependencies, and build results.
2. **Fix the mathematical specification first.** Separate the paper's printed `ell(x)=|x|+1` measure from actual leaf count; prove/refute the corrected cardinality bound (especially `cons x nil`) with independent exhaustive regressions.
3. **Prove the missing semantic equivalences.** Connect `ContainedDef2`, deletion RTC, encoding, and ordered-tree contractions at arbitrary depth. Prove `lcsLen` equals the independently specified LCBS optimum, and Theorem 2 with actual contractions.
4. **Formalize executable DP semantics and its runtime.** Derive a decomposition-index/step bound for the actual implementation model; only then publish a corrected Theorem 3 with exactly stated hashing assumptions.
5. **Prototype Aeneas extraction on a real LCBS state transition** before restructuring the optimized PyO3 backend; prove the generated Rust semantics refine the independent Lean specification.
6. **Measure and refine performance**, retaining Python/Cython/PyO3 as reference baselines until verified Rust parity and benchmarks justify adoption.

## 9. Primary sources and tooling

- Lozano and Valiente (2004), original accessible paper: https://www.cs.upc.edu/~antoni/subtree.pdf
- Gabriel Valiente publication listing (bibliographic details): https://www.cs.upc.edu/~valiente/
- Aeneas/Charon official overview: https://aeneasverif.github.io/projects/
- Aeneas Rust-to-Lean getting started: https://github.com/AeneasVerif/aeneas/blob/main/documentation/getting-started.md
- Aeneas main source and compatibility notes: https://github.com/AeneasVerif/aeneas
- Droschinsky, Kriege, and Mutzel (2016), unordered MCSI: https://arxiv.org/abs/1602.07210
- Droschinsky et al. (2018), distance-penalized embeddings: https://arxiv.org/abs/1805.00821
- Existing advanced Lean source: https://github.com/Erotemic/networkx_algo_common_subtree/blob/proofs/proofs/SubtreeProofs/Lozano-v6.lean
- Original paper PDF p. 7 (PDF page index 6), printed `ell` recurrence and Lemma 7: https://www.cs.upc.edu/~antoni/subtree.pdf

This plan is an inventory and execution roadmap, not a claim that unrun Lean/Rust checks already pass. Update the source audit and ledger as soon as the recovery and toolchain baseline are reproduced.
