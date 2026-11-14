# Isolated arlib cost-model experiment

This standalone Lake project implements the experiment recommended in the
[supplied audit](../../../docs/planning/lean_complexity_library_reuse_audit_2026_11_14.md).
It leaves the main proof project's Lake dependencies unchanged. Production
algorithm sources are the committed software baseline; this experiment changes
no algorithm or backend selection.

Pins: Lean 4.35.0; arlib `8d08f89a6d05c5e8368e91659bd6e117fbb74c4e`;
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; existing pinned Aeneas
`5a392f4b80a4d0d05abc240eb2a7fa70622a9a35`. The experimental manifest resolves
the same revisions of **every** main-project dependency. A standalone Lake
project supplies dependency isolation without switching the active work branch.

## What is actually proved

`ArlibSpike/MemoLookup.lean` contains a computable lookup over arlib's sealed
queue storage, using charged dequeue and key comparison operations. It reads no
raw table list, specification view, or cost inside the program. Fuel is supplied
at the input boundary; `length + 1` covers the terminal empty pop.

For every existing `MemoTable`, including duplicate keys, theorems prove:

- the returned value equals `(memoFind key table).1` exactly;
- recorded key comparisons equal `(memoFind key table).2` exactly;
- comparisons are at most the original table length;
- dequeue operations are at most length plus one;
- no enqueue/isEmpty operations occur;
- the complete recorded operation count is at most `2 * length + 1`;
- a first-entry hit returns immediately with one comparison and one pop,
  regardless of the unused suffix length.

These theorems bridge to the **existing computation**, not a new optimum or an
unrelated charged example. They do not reimplement the tree DP. The input
queue is a noncomputable encoding boundary; runtime construction costs are
excluded explicitly, not hidden inside the program.

`ArlibSpike.lean` also reproduces the upstream sealed-vector example returning
7 with 23 recorded operations, while importing the whole main proof library.
The small example is adapted under Apache-2.0; see its attribution and
`LICENSE.arlib`. Arlib is fetched as a pinned dependency, not vendored.

`ArlibSpike/Exchange.lean` proves a dictionary lookup has one abstract dictionary
operation and demonstrates the library's exchanges at the dictionary's actual
cardinality:

- `StdImpl.listBacked setup`: at most `3 * card + setup + 1` modeled word steps;
- `StdImpl.constantTime setup`: at most `setup + 1` modeled word steps.

The latter is an **explicit implementation-cost assumption**, not an expected
hashing result. These are model exchanges for arlib's dictionary operation;
they do not establish a Rust dictionary implementation or replace the proved
comparison count of the queue scan.

## Cost and trust boundaries

The lookup currency counts a sealed table pop and a **whole Dyck-key equality
comparison**. A structural comparison is not established to cost one RAM
instruction. Loop/control, representation access, key comparison internals,
allocations/copies and Rust-to-resource correspondence need separate bounds
before any full running-time claim. IEEE-754 correctness remains outside the
initial proof scope.

`Program.find` is the entire small operation-bearing program. Its body and the
single `Interface.equalKey` primitive were inspected: no `noncomputable`
program, raw table view, cost introspection or expensive function inside `pure`.
The compiler rejects all three declarations in `ForbiddenAccess.lean`: a free
queue view, free dictionary lookup, and erasing charges through `Charged.val`.
This is a bounded manual program audit and negative compilation check, not a
claim that Lean automatically prevents every possible cost-laundering program.
The library documents additional recursor/sharing holes. No space claim or
`ExactNet` obligation is asserted here.

## Reproduce

On the agent workspace, `.lake` is an ext4 bind mount, never a symlink. The
experiment reused exact-pinned dependency caches through bind mounts after
checking revisions; ordinary installations can fetch their own caches.
When a reused cache contains nested bind mounts, use a recursive bind or
mount those dependencies individually: a plain bind hides nested mounts. Keep
cache storage outside the mounted source filesystem as required by the local
formalization workflow.

```bash
cd proofs/experiments/arlib_cost
lake update
lake exe cache get
lake build
# This command must fail with three dependsOnNoncomputable errors:
lake env lean ForbiddenAccess.lean
```

The negative file is deliberately outside the library namespace and is not an
import or default build target. `results.json` records the executed checks and
source pins. The joint **3,744-job build passes**, including the complete main
proof library, and all three intended negative compilation checks pass. Upstream legacy-module/deprecation warnings are retained; no
upstream source was patched to suppress them.

## Adoption decision

The pinned APIs support a genuine, small bridge to the current memo lookup.
However, the main development already proves `memoFind_value`,
`memoFind_comparisons`, whole-DP call/miss bounds and the association-list
comparison bound in `MemoizedDynamicProgram.lean`. The experimental program
and proofs add about 170 lines plus a smoke example; the existing lookup value
and length proofs occupy about 20 lines. The gain is sealed operation-bearing
storage and reusable exchange infrastructure, not a new asymptotic theorem.

**Keep this as an optional experiment; do not add arlib to the main manifest
now.** Extend the current exact counters for immediate 2004 obligations. Revisit
arlib when a production operation/resource bridge or the optimized matching
schedule can reuse its sealed storage, heap or RAM realization theorems without
rewriting the independent specification. Functional correctness alone does not
establish similar runtime. Matching-family amortization, the optimized 2018
schedule/dichotomy, expected hashing and production Rust complexity remain open.
