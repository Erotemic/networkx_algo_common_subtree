# Resume on another machine

Branch: `Droschinsky-algos`. The latest increment proves
[addressed memo primitive ownership](lean-complexity-campaign/evidence/memo-heap-ownership.md).
Six `MemoHeap*.lean` modules reuse generic heap instruction simulation, produce
actual native-input addressed runs with exact source costs/allocation growth,
and prove independent typed readback. Concatenation's entire output is fresh.
Insertion copies keys/witness into a fresh entry, then puts the original table
cell under a fresh tail Box. Its complete occurrence ledger transfers all old
owners and each new Box exactly once, with multiplicity retained and arbitrary
external owner frames preserved. Shared arguments may alias into the owned
table being moved. Input layouts exist for every native value, including a
separated owned-table frame. Next intermediate source/type/storage/spatial/
loan/region invariants for these helpers, then actual evaluator/core and wrappers.

The preceding increment supplies
[actual concatenation/insertion source composition](lean-complexity-campaign/evidence/memo-source-primitives.md).
`MemoSource{,Frontend,Certificate,Refinement}` and two generated modules retain
actual pinned Charon JSON and kernel-check its normalization. Shared instruction/
control semantics and parsing now support arbitrary callee types; lookup is the
original specialization. Native-input execution constructs independent append/
prepend outputs with unchanged complete source costs, agrees with translated
Rust, and has explicit structural copy/Box counts. Arbitrary tables and witness
scores remain supported. Addressed heap/owner/storage/loan/region composition
for these new functions remains open. Next extend those invariants, then the
actual memo evaluator/core and wrappers.

The preceding increment proves
[scoped lookup region erasure](lean-complexity-campaign/evidence/lookup-region-erasure.md).
Eight `Rust/LookupRegion*.lean` modules check actual free/body region binders,
all nested reference/generic uses and helper call arities. Checked annotations
retain region-bearing types with independent scope proofs and exact erasure.
`scoped_erasure_iff` supplies an explicit immutable retained-world lifetime
interpretation; bounded signature substitution preserves scope and values.
Both actual source programs pass kernel certificates. Recursive `RunScoped`
traces use the parsed declarations and actual local annotations.
`lookup_source_total` composes native success, regional/loan/storage/spatial/
frame witnesses, borrow-free output, exclusive returned ownership, independent
first-hit readback and unchanged costs/allocation growth. This completes the
scoped immutable interpreted lookup pilot in the declared source-operation
model. Full W06-C3 remains open for the actual memo core and wrappers. Compiler/
machine/provenance and mutable/unwind semantics remain separate boundaries.

The preceding increment proves
[stable typed shared loans](lean-complexity-campaign/evidence/lookup-shared-loans.md).
Eight `Rust/LookupBorrow*.lean` modules back shared references with typed reads
in the retained caller heap, preserve loans through actual helper execution
and prove ordinary output borrow-free, including owned payloads. The new region
increment consumes these results; do not duplicate them.

The preceding increment proves
[normal local-storage lifetimes](lean-complexity-campaign/evidence/lookup-stack-storage.md).
Seven `Rust/LookupStack*.lean` modules retain distinct source allocation and
deallocation and check initialized reads/allocated writes, with exact state
consistency against actual value environments. Moves preserve allocated empty
storage; reallocation/repeated deallocation follow pinned Charon conventions.
Actual recursive traces retain the unchanged heap execution and full cost.
Both real source bodies and exact declaration counts pass kernel certificates:
10/15/6/20 locals, with 23 for mutant lookup. `lookup_stack_total` composes
native success, stack/spatial/frame certificates, final ownership, typed
first-hit readback and existing costs/allocation growth. This establishes
logical normal-path local storage discipline. The subsequent loan increment
establishes dynamic shared-loan validity. Source regions, physical stack
addressing and official source adequacy remain open.

The preceding increment proves
[intermediate framed lookup ownership](lean-complexity-campaign/evidence/lookup-spatial-ownership.md).
Six `Rust/LookupSpatial*.lean` modules track duplicate-free complete Box
occurrence lists across every live local, temporary bundle and suspended caller
frame. Concrete traces preserve the actual completed normal execution and full
cost. Recursive spatial contracts are discharged by fuel induction for both
real programs, including generic Box. `lookup_spatial_total` composes successful
native-input execution, recursive spatial/frame safety, final exclusive owned
output, independent typed first-hit readback and existing event/allocation
bounds. Shared aliases remain supported. The theorem concerns active owner
roots; it does not infer ownership of borrowed storage from representation.
The subsequent storage increment proves normal local allocation/liveness.
Dynamic immutable loans are now proved; source regions and official adequacy
remain open.

The preceding increment proves
[operational lookup type preservation](lean-complexity-campaign/evidence/lookup-type-preservation.md).
Four `Rust/LookupType{Primitives,Execution,Calls,Refinement}.lean` modules consume
the checked static constraints to preserve independent reachable-cell/local
typing through actual addressed reads, borrows, moves, construction and control.
The reader retains checked argument/return prefixes; both concrete certificates
are kernel-checked with the stronger reader. Recursive typed callee contracts
are discharged by fuel induction, including generic fresh Box allocation.
Both actual programs preserve output types and old memory for every successful
run at every fuel. Source composition retains complete costs and allocation
growth. The subsequent spatial increment handles intermediate owner separation.
Normal local initialization/storage checks now have their own soundness proof.
Dynamic immutable loan preservation is also proved. Progress, source regions
and official source adequacy remain open.

The preceding increment supplies
[kernel-checked lifetime-erased source types](lean-complexity-campaign/evidence/lookup-source-typing.md).
Five `Rust/LookupSourceTypes.lean`, `LookupTypedCode.lean` and
`LookupType{Reader,Annotations,Certificate}.lean` modules check actual retained
field layouts against independent `Heap.Shape`, helper signatures, local and
nested annotations, generic instances and every helper body's static type
constraints. Both original and actual cost-mutant source inputs pass
`decide +kernel`. All four ordinary helpers are covered; the checker rejects
false annotations and constructor errors accepted by control/frame checks.
This closes supported lifetime-erased declaration/annotation checking.
The subsequent increments establish operational preservation, intermediate
spatial ownership, local storage discipline and dynamic loan validity. Source
region/interpretation adequacy remains open. Regions are deliberately erased.

The preceding increment proves
[checked intermediate lookup frame safety](lean-complexity-campaign/evidence/lookup-frame-safety.md).
Six `Rust/LookupFrame*.lean` modules analyze empty/non-owning/potentially-owned
locals and prove the analysis sound against concrete execution. Every completed
normal run of both generated programs has safe reset/overwrite destinations,
empty moved drops, tracked moves, callee ownership profiles and return cleanup.
Recursive contracts are discharged by fuel induction. `certified_run_safe`
preserves the retained source execution's complete cost; `lookup_guarded`
includes native-input success, typed first-hit readback and final exclusive
ownership. This is not a full type checker or spatial/lifetime proof.

The preceding increment proves
[exclusive returned lookup ownership](lean-complexity-campaign/evidence/lookup-return-ownership.md).
`Rust/LookupHeap{Ownership,Layout,ReturnOwnership}.lean` defines ownership
intervals and occurrence lists, proves exact generated copy/result-copy/lookup
output cell/heap layouts, and shows that each new Box is owned exactly once by
the returned result. The occurrence count equals actual Box allocations and
excludes old input Boxes. Shared input aliases, duplicate keys and unsound
cached witnesses remain supported. The new frame analysis separately supplies
local guard/cleanup evidence; final reachability alone does not prove it.
Intermediate spatial ownership and lifetime-erased operational typing are now
proved; normal storage and dynamic loans are checked as well. Source region
and official interpretation adequacy remain open.

The preceding increment proves an
[addressed lookup memory realization](lean-complexity-campaign/evidence/lookup-heap-realization.md).
Six `Rust/LookupHeap*.lean` modules implement addressed shared reads, invalidating
local moves, guarded field paths, independently typed represented values and
fresh Box cells. Primitive/control/call simulation preserves complete costs and
proves heap growth equals Box allocations. Actual lookup succeeds with independent
first-hit readback at the established sufficient fuel; comparison preserves the
entire heap and permits aliased inputs. Input layouts exist for every native
table/query. Both original and mutant connect through their source certificates.
This is immutable logical memory. Returned exclusive ownership, normal local
frame safety and lifetime-erased JSON field/static typing are now checked.
Operational type preservation and intermediate spatial ownership are now
proved, with normal storage and dynamic loans now checked. Source region and
official LLBC/Rust interpretation adequacy remain open.

The earlier source-control increment supplies
[kernel-checked lookup source-control certificates](lean-complexity-campaign/evidence/lookup-source-certificates.md).
Both original and actual Rust extra-comparison mutant retain complete pinned
Charon JSON (only output-destination options normalized). A Lean reader checks
supported source forms; a separate source-index interpreter and proved lowering
preserve complete outcomes/costs for every fuel/function/argument list.
Concrete reads/normalizations are kernel-checked, without native proof oracles.
The mutant cannot pass the original normal-form certificate and still violates
the old comparison allowance. The Python control reifier is no longer trusted
for those snapshots. Charon/data import and declared snapshot primitives remain
boundaries. Subsequent addressed, ownership, frame and static typing results
and operational/spatial/storage/loan preservation advance those obligations;
source region and official interpretation gaps stay explicit.

The earlier generic increment proves
[whole-run memo work envelopes](lean-complexity-campaign/evidence/memo-work-envelopes.md)
from actual primitive contracts, rather than assumed final-trace caps.
The generic native theorem includes nonuniform body/request budgets, arbitrary
sound warm storage, finite closure and multiple roots. It also exports a
Std.WP contract. List/direct/encoded-pair work models and LV/edit-distance
consumers compile; both cold clients include cache setup. Edit distance uses
its exact `n*m` interior-state count for sharper weighted bounds.

The [LV bridge](lean-complexity-campaign/evidence/memo-lv-correspondence.md)
preserves unchanged `memoLcs` values, complete table order, calls, misses and
comparisons. The [independent edit-distance client](lean-complexity-campaign/evidence/memo-edit-distance.md)
proves attained/minimum edit cost and fits the same generic memo theorem with
list/dense implementations. Generic and edit-distance modules import no tree
or Rust module. See the [reuse audit](lean-complexity-campaign/evidence/memo-statement-audit.md)
and [native core](lean-complexity-campaign/evidence/memo-interpreter.md).

This is **C1 declared-event work**, not complete Lean/Rust runtime. The gap from
supplied trace caps to actual run-level primitive bounds is closed. Remaining
MEM-03/W05 work concerns unpriced input access, structural equality/copy,
body/key construction, materialization/finalization and source realization.
W04's other result-size/substitution interfaces and W06-C3's remaining
ownership/lifetime/source adequacy remain open. Checked reification covers the
supported lookup control fragment; the addressed model realizes its immutable
primitive interpretation. The
[G1 decision](lean-complexity-campaign/evidence/g1-backend-decision.md) and optional
arlib/Lax pilots are unchanged. Production refinement, paper time/space,
release and application-study work remain open in the full planning program.

The main 3,835-job build, all eighteen Lean suites, native WP example, nine Python
reifier tests and 461-endpoint axiom audit pass. The preceding `63f929f` full
regeneration and thirteen ordered Rust tests remain the unchanged provenance/
behavior baseline. New modules have no warnings;
new axioms stay within
`propext`, `Classical.choice`, `Quot.sound`. Shared `leanq` inspected the native
weighted WP's elaborated statement closure (108 records).
`lookup_spatial_total`'s statement closure also has a shared-tool inspection
(202 records). The new `lookup_source_total` statement closure was inspected
(623 records), retaining represented native inputs, actual source/run witnesses
and prior safety/readback/cost conclusions. The new memo heap totality and
ledger endpoints have a 597-record statement-closure inspection, retaining
actual source/heap runs and conditional owner-frame/occurrence guarantees. Main pins and
production Rust/existing Aeneas semantics are unchanged. New generated JSON
snapshots reproduce exactly. CLRS compatibility and source-only
AFP inspection remain recorded in the earlier reuse audit.

Follow [proofs/VERIFICATION.md](../../proofs/VERIFICATION.md) for bootstrap
and pinned extraction details. From the repository root:

```bash
dev/setup-build-caches.sh  # virtiofs VMs; skips local-disk hosts
dev/setup-build-caches.sh --status
(cd proofs && lake exe cache get && lake build)
dev/regenerate_rust_lean.sh --check
python3 proofs/checks/test_lookup_source_reifier.py
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
(cd proofs && lake env lean Tests/LookupHeap.lean)
(cd proofs && lake env lean Tests/LookupFrame.lean)
(cd proofs && lake env lean Tests/LookupEvents.lean)
(cd proofs && lake env lean Tests/Memo.lean)
(cd proofs && lake env lean Tests/EditDistance.lean)
(cd proofs && lake env lean Tests/MemoWork.lean)
(cd proofs && lake env lean experiments/resource_cost_audit/LookupSourceWP.lean)
(cd proofs && lake env lean Tests/RootedDynamicProgram.lean)
(cd proofs && lake env lean Tests/OrderedIsomorphism.lean)
(cd proofs && lake env lean BaselineAudit.lean)
# Optional competing backends; keep their dependencies outside the main manifest.
(cd proofs/experiments/arlib_cost && lake build)
(cd proofs/experiments/lax62_cost && lake build)
```

Extraction auto-bootstrap supports Linux x86_64; other platforms require the
exact compatible tools through `AENEAS_BIN_DIR`. Preserve toolchain/dependency
pins and generated files when moving machines. Caches can be regenerated.

Next is **intermediate insertion/concatenation invariants and actual memo
evaluator/core composition (W06-C3), then remaining local/source costs
(MEM-03/W05)**. Generic declared-currency work and the scoped interpreted
lookup pilot are implemented. Reuse the checked source/type constraints,
addressed execution, ownership, storage, loan and region traces. The explicit
region valuation uses immutable retained-world extension; it is not a full Rust
borrow checker or compiler/machine simulation. D12 permits this honest
source-operation endpoint; do not invent a whole-compiler gate before the
actual memo pilot.

The actual insertion/concatenation source control and native functional/event
bridge now exists; do not repeat that extraction or write a duplicate control
interpreter. Addressed simulation, exact output layouts, returned ownership,
old-table transfer and native input inhabitation now exist too. Next generalize
the checked static signatures/constraints and source region reader to the memo
function set, then operational typing and local guard/storage/spatial/loan
traces. Insertion's initial profile includes an owned table. Preserve its old
occurrence ledger instead of using lookup's fresh-only output interval.
Concatenation reuses shared input borrows. Next inspect and model
actual evaluator arithmetic, owned-local borrows, losing-candidate destruction
and overflow/table returns. Legitimate borrows of caller-owned locals cannot
all satisfy lookup's old-heap-only borrow profile. Preserve scope and ownership
facts when extending it. Then compose one public core entry point.
Then handle indexed/token/reconstruction wrappers, normal work, input/error
policy and the required G3 adversaries. Preserve independent specs and the exact
existing evaluator bridge. `eval_spec` already supplies valid storage and the
actual `ops.read` counter to lookup invariants. Keep W04 size/substitution,
MEM-03 unpriced work, SRC-01/C3, MEM-04 and APP-01 obligations explicit; generic
C1/C2 or the lookup pilot alone cannot close them.

Use [capabilities.md](capabilities.md), [PROOF_STATUS.md](../../proofs/PROOF_STATUS.md)
and the paper plans for the full mathematical, software and release scope.
IEEE-754 correctness remains excluded from the initial proof scope. All four presentation decks were rendered and reviewed; their sources and render
evidence are committed. Ignored media must be regenerated using
[presentations/README.md](../../presentations/README.md). The controlled
application pilot and publication claim remain prospective.
