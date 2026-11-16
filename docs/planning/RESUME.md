# Resume on another machine

Branch: `Droschinsky-algos`. The latest completed increment is the
[reified lookup operational pilot](lean-complexity-campaign/evidence/lookup-source-pilot.md).
Its source, generated programs, tests, exact pins and validation evidence are
committed together. No local build cache or generated media is needed to
reproduce the source work.

The accepted stopping point has a **3,750-job Lean build**, four passing Lean
example suites, seven passing frontend regressions, a checked endpoint axiom
inventory and passing pinned regeneration. The pilot is operational C2 work:
its reifier and immutable-reference interpretation remain trusted. It does
not establish a Rust runtime theorem or complete G1/SRC-01/C3.

After checking out this branch, follow [proofs/VERIFICATION.md](../../proofs/VERIFICATION.md)
for toolchain/bootstrap details. From the repository root:

```bash
(cd proofs && lake exe cache get && lake build)
dev/regenerate_rust_lean.sh --check
python3 proofs/checks/test_lookup_source_reifier.py
(cd proofs && lake env lean Tests/LookupSource.lean)
(cd proofs && lake env lean Tests/LookupEvents.lean)
(cd proofs && lake env lean Tests/RootedDynamicProgram.lean)
(cd proofs && lake env lean Tests/OrderedIsomorphism.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Extraction auto-bootstrap supports Linux x86_64; other platforms require the
exact compatible tools via `AENEAS_BIN_DIR`, as described in the verification
instructions. Keep dependency pins and generated files unchanged when moving
machines. Fresh dependency/build caches can be regenerated.

The next bounded complexity work is **G1/W03**: compare the candidate routes
on the same four-function fragment and make an explicit backend/semantic-boundary
decision. Preserve the trusted reification/heap boundary; do not treat the
checked operational model as completed source-cost refinement. Complete memo
evaluation and wrapper costs remain separate work.

The wider program still has optimized production refinement, applicable
time/space proofs, distribution/release gates and the controlled application
pilot open. Use [capabilities.md](capabilities.md),
[PROOF_STATUS.md](../../proofs/PROOF_STATUS.md) and the paper plans for exact
scope. IEEE-754 correctness remains deliberately excluded from the initial
proof scope.

The presentation sources are committed and all four decks were rendered and
reviewed. Their Git-ignored HTML/PDF/video outputs must be regenerated on the
new machine; [presentations/README.md](../../presentations/README.md) and
[the render report](../../presentations/RENDER_STATUS.md) give the commands and
scope. The application study and publication claim are still prospective.
