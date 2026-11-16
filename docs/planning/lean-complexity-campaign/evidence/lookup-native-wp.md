# Native Std.WP lookup adapter: 2026-11-16

Baseline: `895de31`, following the `a6927b0` source-operation pilot. This is
the native-Std.WP leg of W03, at the existing operational **C2** boundary.
G1 route selection and SRC-01/C3 remain open. Main dependency pins, source
programs, generated files, and existing mathematical specifications are unchanged.

## Checked contracts

[`LookupSourceWP.lean`](../../../../proofs/experiments/resource_cost_audit/LookupSourceWP.lean)
uses Lean 4.35.0's installed `EStateM` WP instance. Its `call` executes the
existing `LookupSource.run`, then adds that run's full cost to the input state.
It does not replace the source computation by `findResult` or a charged twin.
All declaration names below have prefix `ResourceCostAudit.LookupSourceWP`.

- `call_wp_iff`: a successful WP contract holds exactly when the operational
  run succeeds and its value and accumulated cost satisfy the postcondition.
  A stuck or insufficient-fuel run cannot satisfy a successful contract.
- `lookup_wp`: successful independent first-hit lookup, exact packet vector,
  and at most `256 * events.units` additional modeled instruction/access units.
  Structural comparison, short-circuiting, owned witness copy and allocation
  packets are retained. Duplicate keys are allowed; `TableSound` is unnecessary
  because the envelope keeps the actual copied witness size.
- `compare_wp`: the actual recursive comparison scan, preserving the exact
  comparison count and its instruction envelope.
- `copy_wp` and `copyResult_wp`: complete copying with its actual constructor,
  allocation, and result-copy packet counts, plus the instruction envelope.
- `bind_run`: two source calls compose through the actual `EStateM.bind`,
  preserving both costs and allowing the second call's arguments to depend
  on the first result. Every contract accepts an arbitrary prior cost state.
- `extra_compare_rejects_old_wp`: the existing compiled source mutant still
  returns `None` on empty input but cannot meet the old zero-comparison WP
  postcondition. This rejects that component contract, not the loose aggregate
  instruction bound.

## Execution and boundaries

From `proofs/`, after the maintained library build:

```bash
lake env lean experiments/resource_cost_audit/LookupSourceWP.lean
```

This command passes and prints the seven endpoint axiom closures. Each is
within `propext`, `Classical.choice`, `Quot.sound`; `bind_run` needs only
`propext`. CI now executes this worksheet after the source-model examples.

The fresh VM baseline also passes `lake build` (3,751 jobs), the four maintained
Lean example suites, `BaselineAudit.lean`, seven frontend regressions, and all
13 ordered-core Rust integration tests. Build outputs reside on the verified
ext4 bind mounts. Logs for this run are local under
`/var/tmp/subtree-baseline-{build,axioms}.log`; source and commands suffice to
reproduce them. No new extraction is needed: source/generated modules did not
change in this increment.

The adapter imports the established operational semantics and the existing
mutation theorem. Its cost is that semantics' instruction/access count, not
Lean interpreter execution time, RAM-word operations or hardware instructions.
The interpreter/reifier boundary, immutable reference snapshots, Box-allocation
model, and unsupported Rust features retain exactly the limitations in
[the source pilot](lookup-source-pilot.md). No ownership, layout, stack-budget,
physical-memory, allocator-time or full Rust runtime result follows.

The four function contracts prove success for all represented inputs given
their explicit sufficient-fuel inequalities. Fuel bounds nesting and is not
charged as a runtime prepass. Errors preserve the accumulator in this adapter;
their work is deliberately unspecified, so no failure-cost theorem is claimed.

## Remaining W03 comparison

This establishes a usable native WP contract over the same source fragment,
independent result, and operational cost model as the original pilot. It does
not select a backend by itself. The pinned arlib RAM realization and Lax62 IR
realization need their own representation/primitive adapters; transporting an
already computed result into a zero-cost `pure` or arbitrarily charging it
would not discharge those obligations. Preserve this semantic distinction in
the competing-route report. Do not start a broad generic memo library before
the G1 decision and explicit source-boundary disposition.
