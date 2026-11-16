# Resume on another machine

Branch: `Droschinsky-algos`. The latest increment adds a checked
[native memo interpreter](lean-complexity-campaign/evidence/memo-interpreter.md)
and [statement/reuse audit](lean-complexity-campaign/evidence/memo-statement-audit.md).
Generic modules prove independent values, cache preservation, once-only
expansion, exact root-plus-body request accounting and closed finite warm-cache
envelopes. List/direct-address caches satisfy the same functional contract;
actual primitive counters and initialization costs differ. The existing
`paperLcs` recurrence fits the body/descent interface without tree imports in
the generic modules. No assumed total runtime bound is a field.

This is C1 progress, not correspondence with existing `memoLcs` or Rust.
W04 and W05 are partial: the remaining substitution/size interfaces, LV
counter/cache bridge, unrelated client and complete representation work
envelopes remain open. W06-C3's checked reification and typed heap/reference
simulation remain separate obligations. The selected native Std.WP C2 route
and optional arlib/Lax source pilots from the
[G1 decision](lean-complexity-campaign/evidence/g1-backend-decision.md) are unchanged.
Production refinement, paper time/space results, release and application-study
obligations remain open across the full planning program.

The main 3,756-job build, five Lean suites (including the new memo
adversaries), and 111-endpoint dependency audit pass. New modules have no
linter warnings and new endpoints stay within the accepted
`propext`, `Classical.choice`, `Quot.sound` axiom set. Production Rust/generated
sources and main dependency pins are unchanged; no regeneration was needed.
Selected unmodified CLRS statement/execution sources compile under the main
pins. AFP memo sources were inspected only; Isabelle is unavailable.

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

Next is **W05: correspondence with the existing LV evaluator**, preserving
actual table contents, call/miss/comparison counters and the `4*misses+1`
constant. Then complete the unrelated independent edit-distance client and
run-level priced envelopes for both representations. The toy memo tests are
only discriminators, not the unrelated client. See the
[remaining-work list](lean-complexity-campaign/evidence/memo-interpreter.md#remaining-work).
Continue the named **W06-C3** source/reification and heap/reference work;
generic C1/C2 results cannot close that source work or APP-01.

Use [capabilities.md](capabilities.md), [PROOF_STATUS.md](../../proofs/PROOF_STATUS.md)
and the paper plans for the full mathematical, software and release scope.
IEEE-754 correctness remains excluded from the initial proof scope. All four presentation decks were rendered and reviewed; their sources and render
evidence are committed. Ignored media must be regenerated using
[presentations/README.md](../../presentations/README.md). The controlled
application pilot and publication claim remain prospective.
