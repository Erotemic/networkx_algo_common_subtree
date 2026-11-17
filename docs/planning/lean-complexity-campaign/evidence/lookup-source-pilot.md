# Reified lookup operational pilot: 2026-11-16

Historical milestone. The subsequent
[kernel-checked source-control certificates](lookup-source-certificates.md)
remove Python control-reifier trust for both retained snapshots, while
preserving the explicit snapshot-primitive/typed-heap boundary below.

Baseline: `7785776`. This implements the bounded source-model part of W06 over
the same four W02 functions. It is **operational C2 progress with reproducible
source provenance**, not completed SRC-01/C3 or full G1. The reifier and its
reference interpretation remain trusted. No production Rust, existing Aeneas
semantics, main dependency pin or backend default changed.

## Computation and contracts

[`LookupSource.lean`](../../../../proofs/SubtreeProofs/Rust/LookupSource.lean)
defines a small deterministic operational model for this fragment: local
lifetimes, assignment, moves, scalar/reference copies, shared-reference reads,
field projections, constructor assembly, binary switches, function calls,
returns and already-moved conditional drops. `Code.done` is empty-block
fallthrough, not a free source instruction. Each actual represented instruction
has a positive charge, operand/read-expression work is included, and complete
callee costs compose at each call. Box creation is a charged primitive.

`run_bound` proves the instruction envelope for every completed run from local
syntax budgets and callee composition, **without using any value specification
or the earlier packet theorem**. The checked `program_budget` bounds each of
the four generated bodies plus its entry by 256. Fuel bounds call nesting;
work is counted additively and is not inferred from fuel.

[`LookupSourceDeterminism.lean`](../../../../proofs/SubtreeProofs/Rust/LookupSourceDeterminism.lean)
proves that more fuel preserves the exact value **and cost** of any completed
run. `run_unique` therefore identifies all completed runs, even those below a
convenient sufficient-fuel threshold.

[`LookupSourceRefinement.lean`](../../../../proofs/SubtreeProofs/Rust/LookupSourceRefinement.lean)
proves, for every represented native word/table input:

- `copy_source`: successful complete owned copying, with exactly the earlier
  word-visit and Box-creation counts.
- `compare_source`: successful head-before-tail, short-circuit comparison,
  with exactly the structural comparison packet count.
- `copyResult_source`: complete word and scalar-result copying.
- `lookup_source`: nonvacuous first-hit lookup success with exactly the earlier
  event vector, including both short-circuit levels and complete witness copy.
- `lookup_source_all_runs`: every completed run has the independent first-hit
  result and the same event vector, for arbitrary fuel.
- `lookup_aeneas_value_agreement`: the operational result and the existing
  Aeneas theorem agree on the independent `findResult`. This is a **value**
  agreement theorem, not a cost refinement of Aeneas semantics.
- `lookup_source_spec` and `lookup_all_runs_bound`: with the existing
  `TableSound` predicate, every completed operational lookup pays at most

  ```text
  256 * (t * (2*L + 2*R + 3) + 4*min(L,R) + 3)
  ```

  modeled instruction/access units. Here t is actual table length and L/R
  are actual query pair counts. No duplicate-free premise is needed.

Without cache soundness, the independent first-hit result and exact event
counts still hold, but an arbitrarily large stored witness must remain in the
copy budget. The sufficient `lookupDepth` includes such witnesses. It is a
mathematical termination certificate, not an executed input prepass or a
claimed runtime bound.

## Source provenance and actual mutation

[`dev/reify_lookup_llbc.py`](../../../../dev/reify_lookup_llbc.py) consumes
Charon 0.1.315's non-deduplicated Aeneas-preset JSON. It preserves all normal-path
statements in these functions and rejects unsupported operations. Exact helper
paths, duplicate declarations, both signature/body arities, thin shared
references, Box constructor identity and extraction profile are checked. No
function is recognized merely by basename. Source locations and serialization
IDs are absent from the normalized program digest, making regeneration stable
across temporary checkout paths.

[`dev/regenerate_lookup_source.py`](../../../../dev/regenerate_lookup_source.py)
uses the existing pinned Charon/Rust toolchain. It extracts the unchanged
crate, then copies the crate to a temporary directory and inserts

```rust
let _ = words_equal(left, left);
```

at the start of the real `memo_lookup`. Both crates are compiled and both
operational programs are generated from their actual LLBC. No production
source or maintained generated module is hand-edited.

`LookupSourceMutation.extra_compare_violates_old_bound` proves that the compiled
mutant returns the same `None` on the empty-table/empty-query example while
executing one comparison. The old empty-table comparison bound permits zero.
This refutes that **component** of the old contract; it does not refute the
slack aggregate 256-times work envelope. Unlike `LookupEvents.lookupTwice`,
this experiment starts with a real Rust edit rather than a handwritten charged
twin. It still relies on the declared reification/interpretation boundary.

The existing `dev/regenerate_rust_lean.sh --check` now checks both operational
programs as well as both original Aeneas modules.

## Executed checks and review

The full library builds **3,750 jobs**. All four Lean example suites pass,
including eleven new source-execution/unsupported-operation examples. Seven
frontend regressions pass. The nine new audited endpoints use only the
accepted `propext`, `Classical.choice`, `Quot.sound` baseline; no new axiom or
proof placeholder was introduced. Full pinned extraction `--check` passes.
Exact source hashes and commands are in [lookup-source-pilot.json](lookup-source-pilot.json).

Two independent agent reviews checked the semantics and regeneration/CI route.
They found a helper-basename alias bug and an unused-argument boundary gap.
Both were fixed before this milestone: exact root identities and duplicate
rejection prevent helper substitution; signature and body arities are checked
independently. The new regressions cover both failures. Review also confirmed
that the mutation invalidates the comparison component, not necessarily the
loose aggregate bound. No remaining concrete issue was reported in this scope.

From the repository root:

```bash
dev/regenerate_rust_lean.sh --check
python3 proofs/checks/test_lookup_source_reifier.py
cd proofs
lake build
lake env lean Tests/LookupSource.lean
lake env lean Tests/LookupEvents.lean
lake env lean Tests/RootedDynamicProgram.lean
lake env lean Tests/OrderedIsomorphism.lean
lake env lean BaselineAudit.lean
```

## Remaining boundary and next gate

The Python LLBC→Code adapter is trusted, not proved correct. `Value.reference`
is an immutable value snapshot, not a heap address. The model does not verify
LLBC/Rust field typing, aliasing/lifetimes, physical layout, allocator work,
unwinding, allocation failure or stack exhaustion. Normal-path shared reads
and Box creation are the declared operation model; native CPU time, allocator
steps/bytes and memory residency are not conclusions of these theorems.
The existing Charon/Rust compiler trust also remains.

Consequently this is not a Rust runtime theorem or full source-cost adequacy
certificate. SRC-01/C3 remains open. Full G1 also requires the competing-route
comparison and an explicit backend/semantic-boundary decision. W03 must now
compare candidates against this same source-linked fragment and preserve these
limitations. Do not begin a broad generic memo library solely because the
instruction theorem compiles. Complete memo evaluation, insertion, concatenation,
the public core/wrappers and the other source-algorithm applications remain
separate W06/MEM-04/APP obligations.
