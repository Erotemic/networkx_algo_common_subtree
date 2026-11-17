# Resume on another machine

Branch: `Droschinsky-algos`. The latest increment adds the
[independent edit-distance client](lean-complexity-campaign/evidence/memo-edit-distance.md):
valid edit sequences, an attained minimum-cost recurrence, a bounded-index
request body, and list/dense implementations of the same problem. The generic
interpreter supplies correctness, once-only expansion and warm/multi-root
request envelopes. Dense operations charge their actual two-step index
encoding, and dense cache setup explicitly initializes the entire rectangle.

The [LV bridge](lean-complexity-campaign/evidence/memo-lv-correspondence.md)
already proves exact agreement with unchanged existing `memoLcs` on values,
complete table order, calls, misses and comparisons for arbitrary warm tables.
Generic trace/envelope results recover its `4*misses+1` constant and warm
D-product miss bound. Both clients consume the
[native memo core](lean-complexity-campaign/evidence/memo-interpreter.md), with
no tree/Rust imports in generic or edit-distance modules. The
[reuse audit](lean-complexity-campaign/evidence/memo-statement-audit.md) records
inspected declarations and selected compatibility checks.

This is **C1**, not a Rust/source runtime theorem. W04/W05 remain partial:
complete run-level work envelopes, retained input/body/key costs and the other
size/substitution interfaces remain open. W06-C3's checked reification and
typed heap/reference simulation remain separate. The selected native Std.WP
C2 route and optional arlib/Lax pilots from the
[G1 decision](lean-complexity-campaign/evidence/g1-backend-decision.md) are unchanged.
Production refinement, paper time/space, release and application-study work
remain open across the full planning program.

The main 3,761-job build, new edit-distance suite and 125-endpoint axiom audit
pass. The five unchanged Lean suites passed at the preceding milestones.
New modules have no warnings; endpoint axioms stay within
`propext`, `Classical.choice`, `Quot.sound`. Main pins and production/generated
sources are unchanged. Selected original CLRS sources compile under main pins;
AFP sources were inspected only, without Isabelle.

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

Next is **MEM-03/W05: run-level representation budgets and complete priced
envelopes**. Both independent correctness/request clients now compile. Include
setup, input access/body construction, key operations/conversion and
finalization; do not identify narrow word tests/cell counters with total source
runtime. `eval_spec` currently requires lookup invariant preservation for every
work value; cost invariants may need that premise specialized to the actual
`ops.read` counter, while preserving the actual evaluator and existing proofs.
Retain W04's other interfaces and the named **W06-C3** source/reification and
heap/reference work; generic C1/C2 results cannot close that work or APP-01.

Use [capabilities.md](capabilities.md), [PROOF_STATUS.md](../../proofs/PROOF_STATUS.md)
and the paper plans for the full mathematical, software and release scope.
IEEE-754 correctness remains excluded from the initial proof scope. All four presentation decks were rendered and reviewed; their sources and render
evidence are committed. Ignored media must be regenerated using
[presentations/README.md](../../presentations/README.md). The controlled
application pilot and publication claim remain prospective.
