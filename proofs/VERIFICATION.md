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
(cd proofs && lake env lean Tests/OrderedIsomorphism.lean)
(cd proofs && lake env lean Tests/LookupEvents.lean)
(cd proofs && lake env lean Tests/LookupSource.lean)
python3 proofs/checks/test_lookup_source_reifier.py
python -m pytest tests
# Build the opt-in proved-core extension through the actual package build:
python -m pip wheel . --no-deps --wheel-dir /tmp/common-subtree-wheels \
  --config-settings=cmake.define.BUILD_CYTHON_EXTENSIONS=OFF \
  --config-settings=cmake.define.REQUIRE_RUST_EXTENSIONS=ON
```

A source-only `git archive 6dbf81e` was unpacked at
`/tmp/common-subtree-clean`, with no copied `.lake` or project build artifacts.
`lake exe cache get && lake build` fetched its pinned dependencies and succeeded
(3,473 jobs). The Mathlib download cache was reused; project modules rebuilt.

The GitHub workflow `.github/workflows/verification.yml` builds the library,
checks regeneration, executes all three standalone Rust crates, and runs the
independent finite oracles. Its Python extension job installs a built package
and exercises the backend tests outside the checkout. Its first remote execution
is still pending.

Local extension evidence: the CMake/scikit-build wheel with Rust required and
Cython disabled builds under Python 3.13.2. It was installed using `pip --target`
into `/tmp/common-subtree-verified-wheel-install`; from `/tmp`, both
`test_verified_rust_backend.py` and `test_rust_backend.py` pass (23 tests) with
that installation on `PYTHONPATH`. With the locally built source-tree extension,
the full Python suite passes (86 tests). Python/PyO3 token conversion is tested
integration, while the source-refinement theorem covers the Rust Boolean core.

## VM caches

On virtiofs VMs, put build outputs on VM-local disk before running Lean,
Cargo, Charon, or extension builds. From the repository root:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
```

The helper mounts the **nested** `proofs/.lake`, experiment Lake caches,
`rust/target`, and every standalone crate's `target`. It uses local storage
under `/var/cache/common-subtree/<device:inode>/`, so separate checkouts have
separate caches. Override with an absolute `SUBTREE_BUILD_CACHE_ROOT` on local
disk if necessary; use the same override when checking or unmounting.
Every mounted path must report `bind-mounted` and a local filesystem such as
ext4. Existing unrelated mounts and symlinks are refused. Local-disk hosts and
CI are left alone. The helper does not copy host caches: first builds populate
independent guest caches. It does not require the tools submodule.

Mounts disappear on reboot. Rerun setup before resuming; use
`dev/setup-build-caches.sh --unmount` after stopping builds to reveal the
untouched host directories.
Do not replace cache directories with symlinks into the VM. The shared tools'
`setup-lake-cache.sh` resolves Git roots and would mount the wrong `.lake`
for this repository's nested project.

`CARGO_TARGET_DIR` or `--target-dir` can redirect Cargo away from the mounted
paths; verify the actual output directory if either is set. CMake supplies an
explicit `<build-dir>/cargo-target`, so `CARGO_TARGET_DIR` alone does not relocate
wheel builds. Use a local build directory, for example:

```bash
local_build=$(mktemp -d /var/tmp/subtree-wheel.XXXXXX)
findmnt -T "$local_build"  # must be local disk, e.g. ext4
python3 -m pip wheel . --no-deps --wheel-dir /tmp/common-subtree-wheels \
  --config-settings=build-dir="$local_build" \
  --config-settings=cmake.define.BUILD_CYTHON_EXTENSIONS=OFF \
  --config-settings=cmake.define.REQUIRE_RUST_EXTENSIONS=ON
```

Keep Cargo/Rustup homes and any additional custom output directories on local
disk as well. Confirm with `findmnt -T <path>`.

## Optional formalization tools

The pinned `submodules/aiq-lean-formalization-tools` checkout provides `leanq`,
`aiq-lean`, `lake-build-report`, and `lean-warning-fix`. It is development
tooling; ordinary builds still fetch only their pinned Lake dependencies.

```bash
git submodule update --init submodules/aiq-lean-formalization-tools
python3 -m pip install -e ./submodules/aiq-lean-formalization-tools
leanq --project proofs libs
leanq --project proofs --lib SubtreeProofs index
leanq --project proofs --lib SubtreeProofs query --name maximum_common
```

Use `leanq axioms`, `deps`, `rdeps`, and `statement` for elaborated evidence;
see the submodule's `docs/leanq.md`. Indexes under `.leanq/` are ignored.

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
It also regenerates the four-function normal-path operational lookup model
and a real temporary Rust extra-comparison mutation using the same pinned
Charon/Rust toolchain. The reification adapter and immutable-reference model
are explicit trusted boundaries; its cost theorems concern the reified model,
not heapful Rust/Aeneas runtime semantics. Exact scope is in the
[lookup pilot report](../docs/planning/lean-complexity-campaign/evidence/lookup-source-pilot.md).
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

The original-index LCBE wrapper is verified in `Rust/IndexedOrderedEntrypoint.lean`.
`maximum_common_embedding_indexed_of_trees` composes the actual memoized optimum,
checked canonical preorder numbering and total indexed reconstruction. It returns
an independently maximum tree, exact score and actual deletions from both canonical
originals. Original edge/pair indices are unique and in bounds, with exactly one
per scored edge. The input bound is fewer than 2^32 edges per tree. These are pair
positions, with token/vertex conversion separate. Backtracking reconstruction has
no optimized cost theorem; the shape memo operation bound does not bound this
complete wrapper's runtime.

`Rust/TokenParserEntrypoint.parse_balanced_tokens_total_spec` verifies the
actual flat Boolean parser on every represented input: exact independent
acceptance/rejection, complete original shape and original opening/closing
coordinate table. The admitted domain is the independent Dyck encoding with
fewer than 2^32 pairs. Universal source safety/termination and accepted-input
coordinate contents are proved separately and composed. Token emission and
Python/NetworkX conversion remain open; the same operation/allocation model
boundary applies.

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
