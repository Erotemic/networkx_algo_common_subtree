# Resume on another machine

Branch: `Droschinsky-algos`. The latest increment proves
[exact correspondence with existing `memoLcs`](lean-complexity-campaign/evidence/memo-lv-correspondence.md):
values, complete table order, calls, misses and comparisons for arbitrary warm
tables. Under sound valid storage, the generic interpreter recovers
`4 * misses + 1` and the initially-absent D-product miss bound. Multiple roots
in the D-product also consume the generic warm-cache envelope theorem.
The original evaluator and its unconditional counter theorem are unchanged.

This builds on the [native memo core](lean-complexity-campaign/evidence/memo-interpreter.md)
and [statement/reuse audit](lean-complexity-campaign/evidence/memo-statement-audit.md).
Generic modules prove independent values, cache preservation, once-only
expansion, exact root-plus-body requests and finite warm-cache envelopes.
List/direct-address implementations share the functional contract and have
separate actual primitive/initialization counters. Generic modules have no
paper or Rust imports.

This is **C1**, not a Rust/source runtime theorem. W04/W05 are partial: remaining
substitution/size interfaces, the unrelated full client and complete
representation work envelopes remain open. W06-C3's checked reification and
typed heap/reference simulation remain separate obligations. The selected
native Std.WP C2 route and optional arlib/Lax pilots from the
[G1 decision](lean-complexity-campaign/evidence/g1-backend-decision.md) are unchanged.
Production refinement, paper time/space, release and application-study work
remain open across the full planning program.

The main 3,757-job build, updated memo suite and 115-endpoint axiom audit pass.
The four unchanged Lean suites passed with the preceding generic-core build.
New modules have no warnings; endpoint axioms remain within
`propext`, `Classical.choice`, `Quot.sound`. Main dependency pins and production
Rust/generated sources are unchanged. Selected original CLRS sources compile
under the main pins; AFP sources were inspected only, without Isabelle.

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

Next is **W05: the unrelated independent edit-distance client and complete
run-level priced envelopes for both cache representations**. Include setup,
key conversion and finalization; do not identify word tests/cell operations
with total source runtime. The toy memo tests are only discriminators, not the
unrelated client. See the [remaining-work list](lean-complexity-campaign/evidence/memo-lv-correspondence.md#validation-and-remaining-work).
Retain W04's other interfaces and the named **W06-C3** source/reification and
heap/reference work; generic C1/C2 results cannot close that work or APP-01.

Use [capabilities.md](capabilities.md), [PROOF_STATUS.md](../../proofs/PROOF_STATUS.md)
and the paper plans for the full mathematical, software and release scope.
IEEE-754 correctness remains excluded from the initial proof scope. All four presentation decks were rendered and reviewed; their sources and render
evidence are committed. Ignored media must be regenerated using
[presentations/README.md](../../presentations/README.md). The controlled
application pilot and publication claim remain prospective.
