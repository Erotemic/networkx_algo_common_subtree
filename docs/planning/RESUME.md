# Resume on another machine

Branch: `Droschinsky-algos`. The latest increment proves
[exclusive returned lookup ownership](lean-complexity-campaign/evidence/lookup-return-ownership.md).
`Rust/LookupHeap{Ownership,Layout,ReturnOwnership}.lean` defines ownership
intervals and occurrence lists, proves exact generated copy/result-copy/lookup
output cell/heap layouts, and shows that each new Box is owned exactly once by
the returned result. The occurrence count equals actual Box allocations and
excludes old input Boxes. Shared input aliases, duplicate keys and unsound
cached witnesses remain supported. Intermediate frame/reset/move/destruction
safety is still required; final reachability alone does not prove it.

The preceding increment proves an
[addressed lookup memory realization](lean-complexity-campaign/evidence/lookup-heap-realization.md).
Six `Rust/LookupHeap*.lean` modules implement addressed shared reads, invalidating
local moves, guarded field paths, independently typed represented values and
fresh Box cells. Primitive/control/call simulation preserves complete costs and
proves heap growth equals Box allocations. Actual lookup succeeds with independent
first-hit readback at the established sufficient fuel; comparison preserves the
entire heap and permits aliased inputs. Input layouts exist for every native
table/query. Both original and mutant connect through their source certificates.
This is immutable logical memory. Returned exclusive ownership is now proved;
intermediate ownership/destruction, stack lifetimes, checked JSON field typing
and official LLBC/Rust adequacy remain open.

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
boundaries. The new addressed model advances the heap obligation; its remaining
ownership, lifetime, declaration-typing and source-adequacy gaps stay explicit.

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

The main 3,779-job build, all nine Lean suites, native WP example, seven Python
reifier tests and 190-endpoint axiom audit pass. New modules have no warnings;
new axioms stay within
`propext`, `Classical.choice`, `Quot.sound`. Shared `leanq` inspected the native
weighted WP's elaborated statement closure (108 records). Main pins and
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
(cd proofs && lake env lean Tests/LookupHeap.lean)
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

Next is **ownership/frame and typed source adequacy (W06-C3), then remaining
local/source costs (MEM-03/W05)**. Generic declared-currency work, lookup control
normalization, immutable addressed execution and exclusive returned ownership
are implemented; do not duplicate them. Prove safe intermediate local resets/
overwrites, moves, callee argument ownership and conditional destruction for the
actual generated bodies. The current heap model does not free cells; its bare
representation relation permits duplicate Box aliases. New `Owns`/`Footprint`
proofs rule these out in returned values and account for all new allocations,
but do not supply the intermediate frame invariant. Check retained JSON field declarations against the independent
signatures, then connect the official typed source semantics. Extend stack
borrows/mutation as needed for insertion, concatenation and the memo evaluator/
public core. Preserve
the exact existing evaluator bridge and independently optimal clients.
`eval_spec` now supplies valid storage and the actual `ops.read` counter to
lookup invariants, so the former cost-invariant API blocker is resolved.
Keep W04's size/substitution and G1's remaining typed-reference/source-adequacy
obligations visible; generic C1/C2 results cannot close them or APP-01.

Use [capabilities.md](capabilities.md), [PROOF_STATUS.md](../../proofs/PROOF_STATUS.md)
and the paper plans for the full mathematical, software and release scope.
IEEE-754 correctness remains excluded from the initial proof scope. All four presentation decks were rendered and reviewed; their sources and render
evidence are committed. Ignored media must be regenerated using
[presentations/README.md](../../presentations/README.md). The controlled
application pilot and publication claim remain prospective.
