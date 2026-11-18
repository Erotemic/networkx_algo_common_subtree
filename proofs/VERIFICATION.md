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
(cd proofs && lake env lean Tests/LookupSourceFrontend.lean)
(cd proofs && lake env lean Tests/LookupSourceTypes.lean)
(cd proofs && lake env lean Tests/LookupTypePreservation.lean)
(cd proofs && lake env lean Tests/LookupSpatial.lean)
(cd proofs && lake env lean Tests/LookupStack.lean)
(cd proofs && lake env lean Tests/LookupBorrow.lean)
(cd proofs && lake env lean Tests/LookupRegions.lean)
(cd proofs && lake env lean Tests/MemoSource.lean)
(cd proofs && lake env lean Tests/MemoHeap.lean)
(cd proofs && lake env lean Tests/MemoTypes.lean)
(cd proofs && lake env lean Tests/MemoSpatial.lean)
(cd proofs && lake env lean Tests/MemoStack.lean)
(cd proofs && lake env lean Tests/MemoBorrow.lean)
(cd proofs && lake env lean Tests/MemoRegions.lean)
(cd proofs && lake env lean Tests/SourcePartial.lean)
(cd proofs && lake env lean Tests/SourceEval.lean)
(cd proofs && lake env lean Tests/SourceEvalHelpers.lean)
(cd proofs && lake env lean Tests/SourceEvalChoice.lean)
(cd proofs && lake env lean Tests/SourceEvalBase.lean)
(cd proofs && lake env lean Tests/SourceEvalRecursion.lean)
(cd proofs && lake env lean Tests/SourceEvalTypes.lean)
(cd proofs && lake env lean Tests/SourceEvalTypeExecution.lean)
(cd proofs && lake env lean Tests/SourceEvalRegions.lean)
(cd proofs && lake env lean Tests/SourcePartialHeap.lean)
(cd proofs && lake env lean Tests/SourceLocalBorrow.lean)
(cd proofs && lake env lean Tests/SourceFrameUpdates.lean)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceFrameInventory.lean)
(cd proofs && lake env lean Tests/SourceStorageLifecycle.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceCallingProgram.lean)
(cd proofs && lake env lean Tests/LookupHeap.lean)
(cd proofs && lake env lean Tests/LookupFrame.lean)
(cd proofs && lake env lean Tests/Memo.lean)
(cd proofs && lake env lean Tests/EditDistance.lean)
(cd proofs && lake env lean Tests/MemoWork.lean)
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

The scoped region increment adds `Rust/LookupRegion*.lean` and
`Tests/LookupRegions.lean`. It checks actual free/body region scope and helper
call arities, retains regional local types and proves erasure equivalence under
an explicit immutable retained-world lifetime. Both actual source snapshots
pass kernel certificates; `lookup_source_total` composes source parsing,
recursive regional traces, native success, prior safety/readback and costs.
The main 3,823-job build, sixteen suites, native WP example, seven Python tests
and 414-endpoint audit pass. See the
[region report](../docs/planning/lean-complexity-campaign/evidence/lookup-region-erasure.md)
for exact assumptions and remaining compiler/runtime and memo-composition work.

The actual concatenation/insertion pilot adds `Rust/MemoSource*.lean`,
`Generated/MemoSource{Input,Program}.lean`, `dev/regenerate_memo_source.py` and
`Tests/MemoSource.lean`. The main regeneration command now also checks these
fresh pinned extractions. Shared primitive/control semantics and parsing are
polymorphic in callees; all prior lookup refinements still specialize to their
original targets. New kernel source certificates and native-input totality
retain complete costs and agree with independent append/prepend models and
translated Rust. The main 3,829-job build, seventeen suites, nine Python tests,
thirteen ordered Rust tests, full regeneration and 430-endpoint audit pass.
See the [memo primitive report](../docs/planning/lean-complexity-campaign/evidence/memo-source-primitives.md)
for exact event counts and remaining addressed safety/evaluator obligations.

The addressed memo increment adds `Rust/MemoHeap*.lean` and
`Tests/MemoHeap.lean`. Generic addressed instruction simulation preserves the
certified source's complete costs; exact output layouts establish fresh
concatenation ownership and transfer of insertion's original table. Native
success, independent typed readback, allocation growth and complete owner
ledgers/frame preservation compile. The 3,835-job build, eighteen suites, native
WP, nine Python tests and 461-endpoint audit pass. No source regeneration is
needed: Rust, generated artifacts and pins are unchanged. See the
[addressed memo report](../docs/planning/lean-complexity-campaign/evidence/memo-heap-ownership.md)
for exact assumptions and remaining intermediate invariants/evaluator work.

The memo typing/scope increment adds `MemoSourceTypes`, `MemoType*.lean`,
`MemoRegion*.lean` and `Tests/MemoTypes.lean`. Actual source type/region checks
are kernel-certified, generic preservation consumes checked static constraints,
and ordinary results contain no shared reference even inside owned payloads.
Insertion's owned argument and distinct value/region arities are explicit.
The 3,842-job build, nineteen suites, native WP, nine Python tests and
484-endpoint audit pass. Source/generated files and pins are unchanged; no
new regeneration is needed. See the
[memo typing/scope report](../docs/planning/lean-complexity-campaign/evidence/memo-source-typing.md)
for assumptions and remaining guard/storage/spatial/loan/lifetime work.

The memo guard/spatial increment adds `MemoFrame*.lean`, `MemoSpatial*.lean`
and `Tests/MemoSpatial.lean`. Generic checker/soundness interfaces retain old
lookup entry points and allow insertion's owned table role. Recursive concrete
traces preserve complete local/temporary/caller ownership lists and all costs;
native source/heap endpoints retain typed readback, events and old-table identity.
The 3,847-job build, twenty suites, native WP, nine Python tests and
516-endpoint audit pass. Rust/generated artifacts, readers, tools and pins are
unchanged. See the [memo spatial report](../docs/planning/lean-complexity-campaign/evidence/memo-spatial-ownership.md)
for explicit frame premises and remaining storage/loan/lifetime obligations.

The memo storage increment adds `MemoStack*.lean` and `Tests/MemoStack.lean`.
Generic retained-marker lowering and storage checker soundness preserve original
lookup entry points. Kernel actual-body/count checks and fuel induction produce
normal storage/initialization traces; native endpoints compose prior full-cost
source/heap, typed readback, guarded/spatial and owner-transfer results.
The 3,850-job build, 21 suites, native WP, nine Python tests and
531-endpoint axiom audit pass. Rust/generated artifacts, parser, tools and pins are
unchanged. See the [memo storage report](../docs/planning/lean-complexity-campaign/evidence/memo-stack-initialization.md)
for exact scope and remaining dynamic loans/lifetimes/evaluator work.

The memo loan/region increment adds `MemoBorrow*.lean`, `MemoRegionCalls.lean`,
`MemoRegionRefinement.lean`, `Tests/MemoBorrow.lean` and `Tests/MemoRegions.lean`.
Generic loan soundness retains original lookup APIs. Actual source checks now
compose routes with scoped declarations; recursive memo traces preserve typed
caller loans and interpret actual checked annotations in retained heap worlds.
Native endpoints retain all previous safety/readback/cost conclusions and
ordinary output closure. The 3,855-job build, 23 suites, native WP, nine Python tests and
552-endpoint axiom audit pass. Rust/generated artifacts,
source parser, tools and pins are unchanged. See the
[memo loan/region report](../docs/planning/lean-complexity-campaign/evidence/memo-loan-regions.md)
for exact lifetime scope and remaining actual evaluator/core work.

The evaluator partial-local increment adds `SourcePartial*.lean` and
`Tests/SourcePartial.lean`. It proves partial readback/moves, preserved siblings,
exact remaining declared destruction work, local frames and old whole-local
compatibility. These primitives are not yet composed into actual evaluator
source/heap execution. The 3,858-job build, 24 suites, native WP, nine Python tests and
572-endpoint axiom audit pass. Rust/generated artifacts,
parser/reifier and pins are unchanged. See the
[partial-local report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-partial-locals.md)
for the pinned extraction command and exact remaining obligations.

The actual evaluator profile adds six `SourceEval*.lean` modules and
`Generated/SourceEvalInput.lean`. The full regeneration command now runs
`dev/regenerate_eval_source.py`, reusing pinned extraction/data generation.
Actual source reading/covers/counts/execution binding and native checked-add
agreement are kernel certified; common control/frontend semantics are reused.
`Tests/SourceEval.lean` includes kernel primitive/rejection checks and native
behavioral guards on the actual decoded program. The 3,865-job build, 25 suites, native WP, nine Python tests, thirteen Rust
tests, full regeneration check and 592-endpoint axiom audit pass.
See the [evaluator profile report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-source-profile.md)
for exact reference/destruction scope and remaining universal refinement/safety.

The expanded helper bridge adds `SourcePartialReadback`, four
`SourceEvalLegacy*` and three `SourceEvalHelper*` modules, with
`Tests/SourceEvalHelpers.lean` in CI. Kernel identity of actual helper bodies,
recursive exact-work simulation and native/addressed safety compositions reuse
the completed earlier helper chains. The numeric domain and one-way success
scope have explicit regression cases. All 3,873 library jobs, 26 suites, native WP and nine Python tests pass; the
624-endpoint audit remains within `propext`, `Classical.choice`, `Quot.sound`.
Shared `leanq` inspected the recursive and insertion-totality statement closures
(1,239 records). Rust/generated data, interpreters and dependency pins are
unchanged; the preceding full regeneration and thirteen Rust tests remain the
provenance/behavior baseline. See the
[helper bridge report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-helper-bridge.md).

Four `SourceEvalChoice*` modules add the complete kernel-certified actual score
choice body, universal native/tie agreement and exact losing-witness destructor
currency. `Tests/SourceEvalChoice.lean` checks distinct-word ties, inconsistent
scores and exact work/Box counts. All 3,877 library jobs, 27 Lean suites, native WP, nine Python tests and the
634-endpoint axiom audit pass; shared statement inspection covers 706 records. No Rust,
generated data, parser/executor or pins change. See the
[owned-choice report](../docs/planning/lean-complexity-campaign/evidence/memo-owned-choice.md)
for scope and reproduction.

Four `SourceEval{Body,BodyCertificate,Base,BaseRefinement}` modules add the
complete kernel-identified evaluator control and universal cache-hit/empty-query
source/native base contracts. `Tests/SourceEvalBase.lean` includes a maximal-
score unsound duplicate-key cache, exact cold events and universal actual JSON
execution/native agreement. All 3,881 library jobs, 28 Lean suites, native WP,
nine Python tests and the 645-endpoint audit pass. Shared statement inspection
covers 838 unique declaration records. Source/profile interpreters, Rust/generated inputs and pins are unchanged.
See the [evaluator base report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-base-paths.md)
for exact remaining recursive and addressed safety obligations.

Nine new source-control/evaluator modules add full-cost fuel monotonicity,
all recursive success/failure/overflow composition and universal actual
source/native totality for arbitrary finite words/warm tables. Independent
consistency/memo results reuse their original assumptions. The new
`Tests/SourceEvalRecursion.lean` exercises both checked-add exits and recursive
failure propagation with exact tables, destruction and call counts. All 3,890
library jobs, 29 Lean suites, native WP, nine Python tests and the 675-endpoint
axiom audit pass. Shared statement inspection covers 837 unique declarations. Rust/generated data,
interpreters/frontends and pins are unchanged. See the
[universal evaluator report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-native-totality.md)
for reproduction and remaining typed addressed/global resource scope.


Eight `SourceEvalType*`/`SourcePartialTyp*` modules check all nine actual source
declaration/control profiles, both Option layouts and nested annotations,
then prove independent partial-local read/move/store/clear and expanded
operand/expression/action preservation. `Tests/SourceEvalTypes.lean` consumes
actual evaluator/public-entry constraints and checks scalar/option/shared-move
counterexamples plus typed partial tuple moves. Recursive typing and addressed
owner/storage/loan/region/destruction composition remain required. The 3,898-job
build, all 30 Lean suites, native WP, nine Python tests and 706-endpoint axiom
audit pass; statement inspection covers 752 unique declaration records. See the
[type evidence](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-source-typing.md).


Six modules now discharge actual recursive source typing and retain all nine
scoped signature/local profiles. New `SourceEvalTypeExecution` and
`SourceEvalRegions` suites consume actual JSON/native/type and binder endpoints,
including the polymorphic Box, fallthrough, call-region arity and dynamic-lifetime
false neighbors. The new type/region proofs preserve the original complete
costs; full addressed ownership/storage/local-loan/destructor interpretation
remains required. The 3,904-job build, 32 Lean suites, native WP, nine Python
tests and 734-endpoint audit pass; statement inspection exports 1,046 unique
declarations with no unknown references. See the [recursive typing evidence](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-recursive-typing.md).


Six addressed partial-value modules now connect stored cells, initialized masks,
complete owner lists, concrete move/readback, fresh Boxes and logical destruction
to existing source primitives. `Tests/SourcePartialHeap.lean` checks a nested
payload move retaining its Box shell, precise retirement/visit/work counts and
caller ownership, plus duplicate-owner, stale-data and shared-alias false
neighbors. Whole addressed execution and loan/storage/destructor interpretation
remain required. The 3,910-job build, 33 Lean suites, native WP, nine Python
tests and 780-endpoint audit pass; statement inspection exports 275 unique
declarations with no unknown references. See the [addressed partial evidence](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-addressed-partials.md).


The local-storage increment adds `SourceHeapReachability`, `SourceHeapPlaces`,
`SourceHeapStorage`, `SourceEvalLocalBorrow` and `Tests/SourceLocalBorrow.lean`.
Actual initialized partial place reads retain concrete pointers, transitive
shared reference graphs and live classified storage roots. Source address/Box/
drop primitives compose with retained caller frames. Mutation/initialization
conflicts, actual recursive frame traces and dynamic region/destructor
interpretation remain open. See the
[local storage report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-local-storage.md).
The 3,914-job build, all 34 Lean suites, native WP, nine Python tests and
830-endpoint audit pass; shared statement inspection exports 278 unique
records without unknown references. Rust/generated files and pins are unchanged.

Four modules add `SourceHeapTransport`, `SourceHeapWrites`, `SourceFrameUpdates`
and `SourceEvalFrameActions`, with `Tests/SourceFrameUpdates.lean`. Guarded read/
owner transport supports actual in-place local writes; source scalar assignment,
store continuations and storage-live/dead markers preserve retained frames.
Nonowning initialized references may end storage; Box shells may not silently
lose owners. Actual full RHS/move/frame/control/callee and region/destructor
composition remain open. See the
[frame write report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-frame-writes.md).
The 3,918-job build, all 35 Lean suites, native WP, nine Python tests and
867-endpoint axiom audit pass. Shared statement inspection covers 245 unique
declarations with no unknown references.

Seven modules add partial graph/frame moves, executable addressed operands/RHSs,
finite ghost graph tracing, guarded assignment and reverse simulation under
independent physical move-route permissions. `Tests/SourceAddressedExpressions.lean`
checks sequential moves/aggregates, concrete comparisons/reborrows, shape and
conflict rejection, complete assignment/cost correspondence and caller retention.
Actual frame/guard/ownership/control/callee and dynamic region/destructor traces
remain open. See the
[addressed RHS report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-addressed-rhs.md).
The 3,925-job build, all 36 Lean suites, native WP, nine Python tests and
888-endpoint axiom audit pass. Shared statement inspection covers 283 unique
declarations with no unknown references.

Four modules add `SourceHeapResources`, `SourceFrameInventory`,
`SourceActivationInventory` and `SourceEvalDerivedAssignments`, with
`Tests/SourceFrameInventory.lean`. They derive actual bounded active/caller
read/owner/loan inventories and remaining contexts. Assignment computes its
guards/context and preserves exact caller resources at unchanged source cost.
Actual initial/control/callee, exclusive owner/spatial and dynamic region/
destructor traces remain open. See the
[computed inventory report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-derived-inventories.md).
The 3,929-job build, all 37 Lean suites, native WP, nine Python tests and
929-endpoint axiom audit pass. Shared statement inspection covers 313 unique
declarations with no unknown references.

Four modules add `SourceActivationInitial`, `SourceEvalDerivedStorage`,
`SourceEvalDerivedDrop` and `SourceEvalDerivedActions`, with
`Tests/SourceStorageLifecycle.lean`. Initial frames use actual parsed local
counts. Computed storage/drop guards protect stack roots and classified unique
Box owners; non-call sequences retain original complete source execution/costs
and final activation/caller/world validity. Calls, switches/returns, all actual
branch check success, global exclusive transfer and region/destructor traces
remain open. See the
[storage/action report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-storage-actions.md).
The 3,933-job build, all 38 Lean suites, native WP, nine Python tests and
949-endpoint axiom audit pass. Shared statement inspection covers 456 unique
declarations with no unknown references.

Four modules add `SourceEvalAddressedScrutinees`, `SourceEvalAddressedReturn`,
`SourceEvalAddressedControl` and `SourceEvalAddressedChoice`, with
`Tests/SourceAddressedControl.lean`. Retained concrete tags support partial moves;
boolean routing and return packets reuse the shared control engine. Successful
addressed runs preserve source results/complete costs and frame/caller/packet
validity. The actual choice bridge reuses the checked native rule and source
body. Calls, all actual physical check success and complete exclusive/storage/
region/destructor composition remain open. See the
[addressed control report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-addressed-control.md).
The 3,937-job build, all 39 Lean suites, native WP, nine Python tests and
962-endpoint axiom audit pass. Shared statement inspection covers 920 unique
declarations with no unknown references.

Nine modules add `SourceHeapReadback`, `SourceHeapHelperWorld`,
`SourceHeapOutputReadback`, `SourceEvalHeapHelpers`, `SourceEvalHeapMemo`,
`SourceEvalHeapLookup`, `SourceEvalHeapIntrinsics`, `SourceEvalDerivedCalls` and
`SourceEvalHelperCalls`, with `Tests/SourceHelperCalls.lean`. They reuse existing
concrete helper execution over mixed prefixes, reconstruct actual live output
metadata, preserve ownership transfers/costs and compose one-pass argument/callee/
result-store execution. Native shapes/fuel discharge local callee contracts.
Control/recursive integration, choice/evaluator/maximum service and all actual
readiness/check/global ownership/storage/region obligations remain open. See the
[helper-call report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-helper-calls.md).
The 3,946-job build, all 40 Lean suites, native WP, nine Python tests and
1,007-endpoint axiom audit pass. Shared statement inspection covers 914 unique
declarations with no unknown references.

The latest calling-entry increment adds five maintained modules, actual
post-argument suspended-stack passing, call/control composition, parsed entry
and zero-owner return cleanup. The actual parsed choice consumer preserves its
native result/tie rule and complete cost while retiring remaining stack roots.
Recursive dispatch, whole-run protected caller preservation, all-path readiness/
physical success and global ownership/region/destructor obligations remain.
See the [calling-entry report](../docs/planning/lean-complexity-campaign/evidence/memo-evaluator-calling-entry.md).
The 3,951-job build, all 41 Lean suites, native WP, nine Python tests and
1,030-endpoint axiom audit pass. Shared statement inspection covers 1,124 unique
declarations from five seeds with no unknown references.

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
Charon/Rust toolchain. It also retains the entire JSON of both extractions,
normalizing only the two output-destination options. The Lean reader and
kernel-checked concrete certificates validate both control normalizations;
the Python control reifier is no longer trusted for those certificates.
The immutable-reference/primitive model, typed heap adequacy and Charon/Rust
extraction remain explicit boundaries. These are source-control cost results,
not heapful Rust/Aeneas runtime semantics. See the
[source certificates](../docs/planning/lean-complexity-campaign/evidence/lookup-source-certificates.md)
and historical [lookup pilot report](../docs/planning/lean-complexity-campaign/evidence/lookup-source-pilot.md).
Intermediate LLBC files are generated locally and ignored. Generated Lean
must never be edited to make a proof pass.

`Rust/LookupHeap{Memory,Typing,Primitives,Execution,Inputs,Refinement}.lean`
adds addressed execution and typed readback for represented immutable heap
inputs, with exact source currencies and fresh Box-cell growth. It proves
lookup success at sufficient fuel and constructs input layouts for every native
table/query. Unique ownership/destruction, stack references, checked JSON field
typing and official LLBC/Rust adequacy remain open. These are logical source
currencies, not constant-time list-store or physical memory/runtime guarantees.
See the [heap realization report](../docs/planning/lean-complexity-campaign/evidence/lookup-heap-realization.md).

`Rust/LookupHeap{Ownership,Layout,ReturnOwnership}.lean` now proves exclusive
returned ownership for the generated copy/result-copy/lookup bodies. Exact
cell/heap layout proofs connect actual addressed execution to fresh postorder
regions. The output ownership-occurrence list covers every new Box exactly
once and has length equal to the allocation counter; no input Box is reused as
owned output. Intermediate resets/destruction, stack lifetimes and official
source adequacy remain separate. The existing `Tests/LookupHeap.lean` command
also checks ownership countermodels. See the
[returned ownership report](../docs/planning/lean-complexity-campaign/evidence/lookup-return-ownership.md).

`Rust/LookupFrame*.lean` now kernel-checks both actual bodies' local ownership
transitions and proves soundness with concrete guarded execution traces.
Completed normal runs discard no owned Box at local reset/overwrite, consume
moved drops only when empty, satisfy callee ownership profiles and leave no
owned non-result locals on return. Recursive callee contracts are discharged
by fuel induction; source-certificate composition retains the complete cost.
`Tests/LookupFrame.lean` is in Lean CI. Spatial ownership, complete source
typing/lifetimes and failed/unwind paths remain open; see the
[frame-safety report](../docs/planning/lean-complexity-campaign/evidence/lookup-frame-safety.md).

`Rust/LookupSourceTypes.lean`, `LookupTypedCode.lean` and
`LookupType{Reader,Annotations,Certificate}.lean` now check lifetime-erased
field layouts, signatures, local/nested type annotations, generic instances
and static body constraints against independent `Heap.Shape`. Both concrete
retained extractions pass `decide +kernel`; coverage includes all four ordinary
helpers. `Tests/LookupSourceTypes.lean` rejects false annotations and type
errors missed by control/ownership-class checks and is in Lean CI.
These certificates do not prove operational type preservation or borrow/region
semantics. Intermediate spatial ownership, stack liveness/lifetimes and
official source adequacy remain open; see the
[source-type report](../docs/planning/lean-complexity-campaign/evidence/lookup-source-typing.md).

`Rust/LookupType{Primitives,Execution,Calls,Refinement}.lean` now proves actual
successful-run type preservation from those checked constraints. It preserves
reachable-cell/local typing through operations and control, discharges recursive
callee contracts including generic Box, and composes both retained source
programs with full cost/allocation correspondence. The source reader additionally
retains checked argument/return local-prefix proofs. Both concrete certificates
are kernel-checked with this stronger reader. `Tests/LookupTypePreservation.lean`
is in Lean CI. This does not establish initialization/progress, intermediate
spatial ownership, stack/borrow lifetimes or official typed LLBC/Rust adequacy.
See the [preservation report](../docs/planning/lean-complexity-campaign/evidence/lookup-type-preservation.md).

`Rust/LookupSpatial{Ownership,Locals,Primitives,Execution,Calls,Refinement}.lean`
proves duplicate-free complete Box footprints across all active owner roots:
live locals, operand temporaries and suspended caller frames. Recursive traces
erase to the actual completed normal execution and retain complete cost.
Both real programs are covered at all fuels; `lookup_spatial_total` composes
native-input success, spatial/frame safety, exclusive returned ownership,
independent typed readback and exact event/allocation bounds.
`Tests/LookupSpatial.lean` is in Lean CI. Stack allocation/liveness, borrow
lifetimes, official source adequacy, freeing/mutation and failure/unwind paths
remain open. Shared pointees do not become owners merely by representation.
See the [spatial report](../docs/planning/lean-complexity-campaign/evidence/lookup-spatial-ownership.md).

`Rust/LookupStack{Code,State,Primitives,Execution,Calls,Certificate,Refinement}.lean`
retains distinct allocation/deallocation markers and proves initialized reads,
allocated writes and exact local storage/value-state consistency through
completed normal recursive runs. Both retained source bodies and exact local
declaration counts pass kernel certificates. `lookup_stack_total` composes
storage/spatial/frame traces, native success, returned ownership, typed readback
and existing costs. `Tests/LookupStack.lean` is in Lean CI. The concrete
certificate module can take several minutes for full kernel reduction; keep
the same live build session until it finishes. Logical local-storage discipline
does not model physical stack addresses or borrow-region/lifetime semantics,
official source adequacy, freeing/mutation or failed/unwind paths. See the
[storage report](../docs/planning/lean-complexity-campaign/evidence/lookup-stack-storage.md).

`Rust/LookupBorrow{Loans,Places,Primitives,Certificate,Execution,Calls,Outputs,Refinement}.lean`
proves dynamic immutable shared loans backed by actual typed earlier-heap reads.
Both retained programs pass kernel-checked source route/type/body certificates.
Intermediate local/temporary loan traces, recursive calls and borrow-free
ordinary results compose with native lookup's storage/spatial/frame safety,
typed readback and exact existing currencies. `Tests/LookupBorrow.lean` is in
Lean CI. A fresh-root borrow can be well typed while outside this stronger
old-root profile; the tests do not claim such a borrow is Rust-invalid.
Source region binding/outlives and official interpretation adequacy remain
open, as do physical provenance, mutable/freeing and failed/unwind behavior.
See the [shared-loan report](../docs/planning/lean-complexity-campaign/evidence/lookup-shared-loans.md).

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
