# Resume on another machine

Branch: `Droschinsky-algos`. The latest increment delivers the
[G1 backend decision at the operational C2 boundary](lean-complexity-campaign/evidence/g1-backend-decision.md).
The native WP, charged arlib and Lax62 timed pilots now use the same four
actual generated lookup bodies, independent values and six work currencies.
They preserve complete successful-run costs and reject the actual compiled
extra-comparison mutation's old comparison budget. Native Std.WP over the
existing operational interpreter is selected for the next C2 work.

This is not SRC-01/C3, Rust runtime, RAM/IR realization, failure-cost or heap
completion. The Python reifier and immutable-reference interpretation remain
trusted. G0's remaining reconnaissance and the wider program's production
refinement, time/space, release and application-study obligations remain open.
The [source pilot](lean-complexity-campaign/evidence/lookup-source-pilot.md),
[native WP](lean-complexity-campaign/evidence/lookup-native-wp.md),
[arlib pilot](lean-complexity-campaign/evidence/lookup-arlib-source-pilot.md), and
[Lax experiment](../../proofs/experiments/lax62_cost/README.md) give exact scopes.

The unchanged main library passed a fresh 3,751-job build, four Lean example
suites, 95-endpoint dependency audit, seven frontend regressions and 13 ordered
Rust tests. Both optional projects pass (3,781 arlib / 3,490 Lax jobs); the latter
compiles its required source dependency chain, not every unrelated main target.
The final signatures and permitted axiom closures are printed by the pilots.
All thirteen original source-pilot hashes still match; no Rust/generated source
or main dependency pin changed in the backend comparison.

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

Next is **W04: checked finite memo request/cache interfaces**, followed by W05's
LV and unrelated clients and two representations. First finish the relevant
upstream memoization statement/reuse audit; keep generic modules independent
of tree/Rust imports. Preserve warm caches, multiple roots, repeated requests,
exact small-input constants and the independent recurrence specifications.
The [G1 report](lean-complexity-campaign/evidence/g1-backend-decision.md) names
**W06-C3** separately: checkable reification/source semantics, typed heap/reference
simulation, then the actual memo evaluator and one public core. Generic C1/C2
results cannot close that source work or APP-01.

Use [capabilities.md](capabilities.md), [PROOF_STATUS.md](../../proofs/PROOF_STATUS.md)
and the paper plans for the full mathematical, software and release scope.
IEEE-754 correctness remains excluded from the initial proof scope. All four presentation decks were rendered and reviewed; their sources and render
evidence are committed. Ignored media must be regenerated using
[presentations/README.md](../../presentations/README.md). The controlled
application pilot and publication claim remain prospective.
