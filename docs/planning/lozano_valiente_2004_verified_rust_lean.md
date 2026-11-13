# Lozano-Valiente (2004): fresh Lean formalization and verified Rust implementation

Status: approved direction -- clean restart of the proof code; implementation work not started
Last revised: 2026-11-13
Paper: Antoni Lozano and Gabriel Valiente, *On the Maximum Common Embedded Subtree Problem for Ordered Trees* (2004)
Repository: `networkx_algo_common_subtree`

## 1. Decision and desired outcome

**Start the Lean proof code from scratch.** Retire the older `proofs/` definitions, v3-v6 experiments, local utility lemmas, Aristotle attempts, partial runtime arguments, and related handoff notes. Do not port or selectively reuse their declarations, proofs, file layout, or theorem statements. Do not merge the historical `proofs` branch. The existing Git history and remote branches are sufficient to preserve that work if historical comparison is ever useful. No new in-tree `legacy/` or `Attempts/` directory is needed.

This reset applies to **formal proofs**, not to the existing Python/Cython/Rust implementations, tests, benchmarks, or their history. Those are useful independent baselines. The new mathematical statements must be derived from the 2004 paper and checked against an independently specified problem, with proof architecture selected for the new Rust/Aeneas effort.

Deliver:

1. A Lean formalization of the paper's ordered-tree problem, principal definitions and lemmas, correctness theorem, and meaningful complexity theorem.
2. An executable, deterministic Rust solution for the specified problem, with generated Lean semantics from that exact Rust source through Charon/Aeneas.
3. Machine-checked theorems connecting the translated Rust entry point to an independently defined optimum and a valid output witness, including explicit safety/precondition claims.
4. A computational cost theorem for the algorithm actually implemented, identifying any dictionary, allocation, arithmetic, or probabilistic assumptions rather than claiming unconditional real-world runtime.
5. Reproducible, competitive performance and sound integration with the existing Python/NetworkX interface.

Do not count a proof of a recurrence defined to equal itself as algorithm optimality. Do not define the paper's embedding relation in terms of the algorithm's balanced-sequence encoding. Do not treat a manually written Lean counterpart as verified Rust code. Scope every accepted theorem to its actual hypotheses.

## 2. Reset the active proof tree

From the supplied `f829c7a` snapshot, retire the following tracked paths in a single reviewable cleanup:

- `proofs/SubtreeProofs/` (all old theorem and helper code, including `Attempts`)
- `proofs/Main.lean` (stale placeholder importing missing modules)
- `proofs/LozanoValiente2004-writeup-v1.md` (old proof-adjacent write-up)
- `proofs/lake-manifest.json` (old dependency resolution, with no corresponding active `lakefile`)
- `next_steps.md` (obsolete handoff that assumes continuing `Lozano-v6`)

Replace `proofs/README.md` with the concise fresh-start policy in this overlay. Keep `proofs/.gitignore`. Keep `proofs/lean-toolchain` temporarily as an *existing pin to review*, not as an accepted toolchain decision. Add a new Lake configuration and fresh lock/manifest once the chosen Lean/Mathlib versions are tested together. Keep the proofs directory intentionally free of new `.lean` files until W1 defines the contract; avoid adding placeholders that look like working proofs.

Leave all Git history untouched. In particular, keep the current application/benchmark commits, and leave `origin/proofs` as an archived branch without importing it. **No squash, force push, or history rewrite is required.** If a local worktree contains uncommitted changes to the paths above, inspect or save those separately before removing them; do not use a forced deletion to overwrite someone's uncommitted work.

The old development exposed useful *failure modes*, which can inform review checklists without contributing proof dependencies:

- The paper's printed sequence recurrence for `ell` yields `semilen + 1`; verify whether it counts actual tree leaves before using it in a tree-leaf bound.
- A tree-contraction theorem must account for contractions at arbitrary depths, not just a root operation or containment defined by encoding.
- A DP recurrence must be proved equivalent to an independent maximum, not merely unfolded.
- A complexity theorem needs an executable costed algorithm, not a symbolic formula assigned to a noncomputable choice of optimum.

These are **requirements for fresh specifications**, not a mandate to repair or recover a particular old theorem.

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

### C. Optimality of the dynamic program

1. Define LCBS/MCES optima independently (maximum over feasible witnesses or a proved equivalent finite characterization).
2. Define the paper's numeric recurrence as a *separate* executable function; prove the recurrence returns that independent optimum by soundness, completeness, and well-founded induction.
3. Give an explicit witness-producing algorithm and prove its returned witness is feasible and has the optimal score, including base cases and tie choices.
4. Prove the resulting tree witness solves the contraction-based MCES problem using Gate A, without defining `MCES` via the DP result.

**Gate C:** a checked theorem says the executable Lean algorithm returns an optimal, independently valid tree witness. Unfolding a recurrence is insufficient.

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
| W0 | Clean proof-tree reset; baseline/test and toolchain inventory | none | legacy proof files removed from active tree, history intact; Rust/Python baseline recorded |
| W1 | Independent tree and contraction-based specification plus exhaustive oracle | W0 | precise semantics and examples checked |
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

Initial status after reset:

| Target | Status |
| --- | --- |
| Independent tree/embedded-subtree specification | open |
| Tree-to-sequence correspondence and containment/contraction equivalence | open |
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

## 9. First execution cycle

1. Commit the proof reset and the new README/plan without modifying existing algorithm source.
2. Establish a valid new Lean/Mathlib workspace with a working trivial proof; record toolchain pins. Separately record current Rust/Python test and benchmark outcomes. No legacy imports.
3. Write the new `OrderedTree` specification and contraction-based exhaustive oracle, with discriminating examples.
4. Prove actual tree statistics and encoding round-trips, then the two-way containment/contraction bridge.
5. Prototype one Rust function through Charon/Aeneas in parallel. Confirm Lean generation, imports and a small refinement theorem before committing to a full verified Rust design.
6. Continue the paper's combinatorial theorems and LCBS recurrence from independent definitions; establish a real-leaf cardinality theorem before relying on the paper's complexity claim.

The first substantive checkpoint is **a small, independently specified theorem that compiles**, together with a translated Rust example whose equivalence can be proved. Do not jump straight to the paper's final theorem or port the old 2,500-line file.

## 10. Sources

- Lozano & Valiente (2004): https://www.cs.upc.edu/~antoni/subtree.pdf
- Aeneas / Charon project: https://github.com/AeneasVerif/aeneas and https://github.com/AeneasVerif/charon
- Aeneas getting started (verify commands against pinned revision): https://github.com/AeneasVerif/aeneas/blob/main/documentation/getting-started.md
- Existing application code, tests and benchmark suite in this repository (not a source of mathematical truth)

The historical `proofs` branch remains accessible through Git, but it is intentionally excluded from the new work plan and formal dependency graph.
