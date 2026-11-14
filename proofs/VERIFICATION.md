# Reproducing verification

The maintained project uses Lean 4.35.0, Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, and Aeneas commit
`5a392f4b80a4d0d05abc240eb2a7fa70622a9a35`. Lake fetches both Git
dependencies; no sibling repository, submodule, or local path is required.

Run from this repository:

```bash
(cd proofs && lake exe cache get && lake build)
dev/regenerate_rust_lean.sh --check
cargo test --locked --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
cargo test --locked --manifest-path rust/crates/verified_assignment_core/Cargo.toml
(cd proofs && lake env lean Tests/RootedDynamicProgram.lean)
python -m pytest tests
```

A source-only `git archive 6dbf81e` was unpacked at
`/tmp/common-subtree-clean`, with no copied `.lake` or project build artifacts.
`lake exe cache get && lake build` fetched its pinned dependencies and succeeded
(3,473 jobs). The Mathlib download cache was reused; project modules rebuilt.

The GitHub workflow `.github/workflows/verification.yml` builds the library,
checks regeneration, executes all three standalone Rust crates, and runs the
independent finite oracles. Its first remote execution is still pending.

## VM caches

This checkout is on virtiofs. Its **nested** Lake workspace is `proofs/`, so
mount the cache at `proofs/.lake`, rather than the repository root's `.lake`.
The existing sibling cache script resolves Git roots and would choose the
wrong directory for this layout. Before building on a VM, seed and mount:

```bash
sudo mkdir -p /var/cache/lake/networkx_algo_common_subtree-proofs/.lake
sudo chown "$(id -u):$(id -g)" /var/cache/lake/networkx_algo_common_subtree-proofs/.lake
cp -a proofs/.lake/. /var/cache/lake/networkx_algo_common_subtree-proofs/.lake/
sudo mount --bind /var/cache/lake/networkx_algo_common_subtree-proofs/.lake proofs/.lake
findmnt -T proofs/.lake
```

Apply the copy only when initializing a new cache; on later boots remount
without copying. The verification run on 2026-11-14 used an ext4 cache at that
path. A bind mount leaves the host's original directory untouched and is
VM-local. Do not replace `.lake` with a symlink. Ordinary Linux CI runners
already use local disk and need no bind mount.

## Rust extraction boundary

`dev/regenerate_rust_lean.sh` downloads the x86-64 Linux release
`nightly-2026.11.09-5a392f4`, verifies archive SHA-256
`54982f0f6bb8ec7080ef9d2a23932aebe6e3c032f32015963bbccc43103f723a`,
and invokes its bundled Charon and Aeneas. The compatible Charon revision is
`454586e9b770231e66d2062993e632dfc06463e2`; extraction uses Rust
`nightly-2026-09-17` with `rustc-dev`, `rust-src`, and `miri`. Set `AENEAS_BIN_DIR`
to an existing copy of this exact release to reuse an installation. The
release archive includes its Lean backend sources, but Lake fetches those
sources independently at the pinned revision.

The script regenerates both `verified_ordered_core` and
`verified_assignment_core`; `--check` compares fresh outputs with their
maintained generated modules.
Intermediate LLBC files are generated locally and ignored. Generated Lean
must never be edited to make a proof pass.

`Rust.contractionBudget_refines_tree` proves that a genuine tree edge
contraction agrees with the generated `remaining_edges_after_contraction`
operation whenever a `u32` represents the input edge count. The positive
case cannot underflow, and zero returns `None`. This establishes the W6
feasibility spike. The later `Rust/OrderedSolver.lean` module verifies the
actual structural-witness solver: `largest_common_embedding_of_trees`
proves successful execution, an independent maximum tree, and the exact
edge score whenever both input trees have fewer than 2^32 edges. Rust
representation/Dyck-word round trips are proved. Its reference recursion
is exponential. `Rust/MemoizedOrderedSolver.lean` additionally verifies the
actual owned-memo entry point and the exact returned-cache correspondence,
including uniqueness and state bounds. Its association-list scans and payload
copies remain representation costs to refine; index witnesses, adapter
verification and efficient dictionary performance are open. The Aeneas model abstracts
allocation and recursive stack resources, so the theorem is a functional
correctness result rather than a platform memory-budget guarantee.
Rust compilation, Charon/Aeneas translation, and the models of supported Rust
operations are explicit translation trust boundaries. Lean checks the resulting
refinement proof. The mathematical tree relation remains independent of them.

The ordered crate's root-preserving and arbitrary-root isomorphism reference
APIs are also verified in `Rust/OrderedRootedIsomorphism.lean` and
`Rust/OrderedArbitraryIsomorphism.lean`. For inputs below the u32 edge-count
limit they return independently maximum adjacency-preserving ordered subtrees
with exact scores. Structural forest interpretation agrees with the existing
two-sided Dyck/tree bridge. These exponential reference functions make no
memoization or running-time claim; original index maps and vertex-pair Python
conversion remain open.

The exact assignment core has reproducible generated semantics and complete
public entry-point total correctness in `Rust/AssignmentEntrypoint.lean`.
`min_cost_assignment_total_spec` verifies every represented input, returning
an independent optimum with exact feasible/tight exported potentials on
admitted square i64 matrices, or the specified size/shape rejection. Numeric
ranges, search/augmentation termination and all driver invariants are derived
inside the proof. `Rust/MatchingEntrypoint.lean` proves the actual rectangular
optional signed-i64 partial-matching public API total contract, including exact
input-index pair membership, list uniqueness, independent global optimality,
exact weight and prescribed shape/size rejection. Actual construction,
assignment, decoding and checked weight conversion are verified. Graph/Python
integration and implementation costs remain open. The actual deletion-family
reference API is verified by
`Rust/MatchingDeletionEntrypoint.max_weight_matching_deletions_total_spec`,
including the original optimum, all deleted optima, exact original indices,
weights and unmatched-result reuse. It fully recomputes matched deletions;
paper one-augmentation repair and optimized costs remain separate obligations. The same supported-operation
and allocation-model boundaries apply. The pinned release
emits a generic unknown-externals warning in single-file mode for this crate;
a split-file diagnostic emitted only `Types.lean` and `Funs.lean`, and the
maintained module compiles against the supplied Aeneas models without a custom
external-model file. This diagnostic is not a substitute for final endpoint
dependency review.

`Rust/AssignmentArithmetic.lean` locally imports the bodies of the pinned signed
checked-addition/subtraction aliases with `import all` for their respective
`Aeneas.Std.Scalar.CheckedOps` modules. Their published specifications name the
underlying generic operations rather than the machine aliases. These scoped
imports permit ordinary definitional bridges; the dependency pin and generated
Rust module are unchanged by those proofs.

## Endpoint dependency audit

An opt-in audit module is `BaselineAudit.lean`. Run it at a milestone and
capture output, rather than putting declaration inventories in normal builds:

```bash
(cd proofs && lake env lean BaselineAudit.lean) > /tmp/subtree-axioms.log
```

The initial reviewed baseline permits `propext`, `Classical.choice`, and
`Quot.sound`. Later dependency audits compare against that set and report
only differences. This audit is separate from routine compilation.
