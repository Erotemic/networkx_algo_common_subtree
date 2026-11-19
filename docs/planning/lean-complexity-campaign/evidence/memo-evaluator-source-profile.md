# Actual memo evaluator source profile and execution: 2026-11-17

Baseline: `23b5043`. Six maintained `SourceEval{Scalar,Operands,Machine,Frontend,
Program,Certificate}` modules and the new generated `SourceEvalInput` consume
the real evaluator/public-core extraction. The shared control executor and
frontend now support this profile and the original lookup/memo-helper profiles.
The original source normalization and safety chains remain checked.

This supplies a kernel-checked executable source profile for the complete
primitive core, including partial moves, live drops and overflow/table returns.
Universal source/native functional/resource refinement and typed addressed
safety for this expanded profile are still open; this does not close W06-C3.

## Actual retained input and kernel certificates

`dev/regenerate_eval_source.py` reuses the existing pinned extraction helper and
JSON-to-Lean data renderer. Its root is
`verified_ordered_core::maximum_common_embedding`; the entire serialized AST,
including annotations and unwind metadata, is retained. Only output destinations
are normalized, as before. There is no external Python code normalizer for this
profile: the maintained Lean reader decodes the source-control program directly.
The normalized source JSON SHA-256 is
`4a9c4cae17fe1955aabc0a9d8285185294d661ed7b4db7387502712f965fc854`.

`ProgramReader` checks the pinned version/preset/crate/error flags, unique
identities, all ordinary helper names/signatures, safe nonvariadic Rust ABI,
canonical local indices, input arities and complete helper coverage. Box uses
the existing generic method checker. The opaque checked-add method must have
the exact `core::num` inherent `u32` identity and signature. Normal conditional
drops must name recognized builtin drop glue for the supported data types,
Box, option or returned tuple. Calls use the checked identity map and arities.

`Certificate.original_read` kernel-checks the successful actual read;
`original_covers` retains all nine ordinary helpers. `original_counts` checks:

| Function | Local slots |
| --- | --- |
| copy word | 10 |
| word comparison | 15 |
| copy result | 6 |
| lookup | 20 |
| concatenate | 13 |
| insert | 15 |
| choose longer | 6 |
| memo evaluator | 113 |
| public maximum entry point | 7 |

`original_execute` binds source reading to the actual decoded program at every
fuel, function and argument list, preserving the whole optional value/cost pair.
It is a source-profile execution theorem, not yet an equivalence with Aeneas or
a physical Rust runtime. Its returned cost measures the decoded program;
offline decoding/generation itself is not included in program work.

## Shared control and expanded primitives

`Control.Tree` factors the source tree over an action type. The original
`Control.Block` is its original action specialization. `Control.execWith`
implements routing and early return once, accepting primitive state/outcome/work
handlers. Original snapshot execution specializes it, and `exec_lower` still
proves the original complete outcome/cost correspondence. The new profile uses
the same executor with partial locals, not a copied controller.

The shared frontend exposes operand, expression, call, sequence and terminal
hooks. Original lookup/helper entry points retain their earlier profile. The
new profile recognizes projected moves, bounded `u32` literals, scalar less-than,
whole-local live conditional drops, fake-read annotations and the actual
undefined-behavior leaf. Shared thin-reference, routing, bounds, safety and
arity checks are reused. The selected unwind profile recognizes cleanup and
termination markers; unwind execution remains outside this normal-run model.

A small shared strict-decimal decoder handles Charon's unsigned spellings with
a structural character-list fold. This is needed for kernel reduction: the
pinned standard string parser evaluates through an opaque iterator loop in this
certificate setting. It accepts decimal digits only, rejects empty/negative/
nondecimal spellings, and the evaluator reader additionally checks `u32` range.
The supported numeric domain was not restricted to the observed zero/one values.

`checkedAdd32_native` proves agreement with pinned `U32.checked_add` for all
native scalar inputs, including overflow. `run_checkedAdd` consumes that theorem
in the primitive driver. Overflow yields a source option `None`, distinct from
interpreter failure. Copies exclude owned values; `copy_nonowning` and
`address_nonowning` prove zero owned-Box currency and unchanged local state.
`move_transfer` consumes the preceding partial-field transfer theorem.
Discriminants inspect retained tags even after payload movement.

`Cost` retains complete source steps/events, declared destructor visits/Box
tokens, and memo-evaluator invocation count. Each drop charges its statement
plus remaining visits; Box-shell tokens are retained after a payload move.
`action_drop_other` proves exact cost and preservation of other locals. All
callee work composes at the actual call occurrence. Recognized fake reads are
explicit ghost no-ops with a statement charge; they do not establish dynamic
borrow validity. Undefined behavior has no successful normal execution; its
unreachability for supported inputs is still a proof obligation.

## Validation and precise remaining scope

The full 3,865-job build passes. All 25 maintained Lean suites, native WP and
nine Python reifier tests pass (27 command checks), including all earlier safety
and source-mutation rejection cases. The thirteen ordered Rust integration tests
pass: five independent contraction-oracle tests, three isomorphism-choice tests
and five token-parser tests. Full pinned regeneration and its check mode pass.
Rust and existing generated artifacts are unchanged; only the new evaluator JSON
input is added. Cache status was checked as VM-local ext4 before builds.

The opt-in axiom audit reports 592 distinct endpoints. All 20 new closures stay
within `propext`, `Classical.choice` and `Quot.sound`; new modules/tests have no
warnings. Shared `leanq statement` inspection of `original_execute` and
`run_checkedAdd` produced 760 elaborated statement records, retaining the actual
source input, full result/cost and pinned native scalar semantics. This is
supplementary to the kernel and axiom checks.

Local logs are `/var/tmp/subtree-source-eval-{full-build,regression,axioms}.log`,
`/var/tmp/subtree-source-eval-rust{,-adapters}.log`,
`/var/tmp/subtree-source-eval-regeneration-check.log` and
`/var/tmp/subtree-source-eval-statements.{json,txt}`.

```bash
dev/setup-build-caches.sh --status
dev/regenerate_rust_lean.sh --check
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceEval.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
leanq --project proofs statement \
  SubtreeProofs.Rust.SourceEval.Certificate.original_execute \
  SubtreeProofs.Rust.SourceEval.run_checkedAdd \
  --root-module SubtreeProofs.Rust.SourceEvalCertificate
```

The new suite kernel-checks scalar boundaries, partial/drop behavior, retained
tags, unsupported operations/literals/destructor identities and terminal/unwind
profiles. Three native behavioral guards run the actual decoded program: empty
inputs return score zero with the temporary cache's two Boxes destroyed; a
one-edge match leaves exactly two more allocated than destroyed Boxes in the
returned witness; and an intentionally unsound warm cache exercises checked-add
overflow, returning `None` and its table after three evaluator invocations.
These guards are executable regressions, not universal refinement theorems and
do not add a native-decision axiom to library proofs.

The new execution layer currently uses full-value snapshots for references.
Logical destructor tokens are not a proof of native drop-glue instruction cost,
physical deallocation, or pointer/lifetime safety. Whole-program local/field
static typing, source-region interpretation, operational typing, allocation/
owner/storage invariants and addressed local-borrow/destruction simulation must
now be composed. Reuse the existing helper proofs through a profile bridge;
do not independently repeat them. Then prove the actual evaluator/core's
functional, overflow/table and resource correspondence, followed by separate
wrappers, input/error policy and G3 adversaries. Preserve independent specs and
D12's named source-operation boundary; no whole-compiler gate is introduced.
