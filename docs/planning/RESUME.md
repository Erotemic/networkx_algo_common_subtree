# Resume on another machine

Branch: `Droschinsky-algos`. The latest increment proves
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
W04's other result-size/substitution interfaces and W06-C3's checked reification
and typed heap/reference simulation remain open. The
[G1 decision](lean-complexity-campaign/evidence/g1-backend-decision.md) and optional
arlib/Lax pilots are unchanged. Production refinement, paper time/space,
release and application-study work remain open in the full planning program.

The main 3,765-job build, all seven Lean suites and 140-endpoint axiom audit
pass. New modules have no warnings; new axioms stay within
`propext`, `Classical.choice`, `Quot.sound`. Shared `leanq` inspected the native
weighted WP's elaborated statement closure (108 records). Main pins and
production/generated sources are unchanged. CLRS compatibility and source-only
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

Next is **remaining local/source cost realization (MEM-03/W05 and W06-C3)**.
The generic declared-currency work theorem is now implemented; do not duplicate
it. Inspect the actual pinned Rust memo evaluator/LLBC operations and connect
remaining input/key/body/materialization work to the source/heap model. Preserve
the exact existing evaluator bridge and independently optimal clients.
`eval_spec` now supplies valid storage and the actual `ops.read` counter to
lookup invariants, so the former cost-invariant API blocker is resolved.
Keep W04's size/substitution and G1's named checked-reification/typed-reference
obligations visible; generic C1/C2 results cannot close them or APP-01.

Use [capabilities.md](capabilities.md), [PROOF_STATUS.md](../../proofs/PROOF_STATUS.md)
and the paper plans for the full mathematical, software and release scope.
IEEE-754 correctness remains excluded from the initial proof scope. All four presentation decks were rendered and reviewed; their sources and render
evidence are committed. Ignored media must be regenerated using
[presentations/README.md](../../presentations/README.md). The controlled
application pilot and publication claim remain prospective.
