# Executable addressed operands, RHSs and assignment: 2026-11-17

Baseline: `bf8ff6a`. Seven maintained modules add syntax-directed addressed
operand/RHS execution, graph-preserving partial moves, reverse simulation under
physical move permissions, and one-pass destination initialization. Every current
RHS constructor is covered: use, address, aggregate and less-than. This advances
SRC-01/W06-C3; full addressed control/callee execution and the full planning goal
remain open.

## Actual cells and initialization metadata

`SourceEvalAddressedOperands.ValueCell` pairs the existing `Heap.Cell` with a
snapshot used for initialization metadata. The executor's cells/pointers come
from actual memory and field/dereference projection. Metadata is assembled by
the same operand/RHS steps so subsequent stores can initialize their masks.
The definitions do not call `SourceEval.operand`, `SourceEval.operands` or
`SourceEval.expression` to obtain a parent answer. They reuse existing
`Partial.Locals.read/move` primitives for initialization and mask updates, with
separately proved concrete graph correspondence.

`Addressed.read`, `copyCell`, `operand` and `operands` implement the current
syntax. Copies allow booleans, bounded numbers and shared pointers; owned
values cannot be copied. Moves update the actual source mask, retain stored data
and reject a final physical place root in the supplied protected list. Constants
retain the original scalar bounds. Operand lists execute in order, so a later
move observes holes introduced by earlier moves.

`operand_spec` and `operands_spec` prove actual successful source execution at
the same final mask, concrete full graph readback and a represented remaining
frame. `operand_move_iff` exposes the exact source-mask/projection/conflict
conditions; `operand_move_complete` recovers concrete success from a successful
source move under its physical route condition.

## Graph partition and remaining frames

`SourceHeapGraphMoves.PartialGraph.take` partitions complete finite read graphs
between the moved complete value and remaining partial parent, retaining
multiplicity for shared aliases. The existing `Rep.take` ownership partition
is unchanged and reusable. Moving a Box payload retains the containing Box root.
`PartialGraphFields.focus` preserves the unaffected field frame.

`SourceFrameMoves.Frame.locate` connects a successful initialized source read to
an actual cell/pointer and selected graph, whose addresses/root are covered by
the source frame. `Frame.move` derives the remaining partial frame from the
actual source move. It retains a conservative superset of live resources; it is
a data/initialization-view theorem, not permission to invalidate a live loan or
discard exclusive ownership. The executable move policy separately checks the
supplied protected roots, and complete traces still have to prove their coverage.

## Every RHS form and reverse simulation

`SourceEvalAddressedExpressions.expression` evaluates all four current forms:

- use delegates to the addressed operand;
- address reads the initialized source place and obtains an actual pointer from
  `Storage.borrow`;
- aggregate evaluates operands in order and assembles concrete fields and value
  metadata from their packets;
- less-than evaluates both operands, inspects concrete numeric cells and uses
  the existing checked `less32` primitive.

`expression_spec` proves source result/final-mask agreement, complete concrete
graph readback, graph coverage and the remaining frame. `expression_readable`
adds liveness-backed readback using the input frame's live resources. No new
cell/type universe, source parser or full-value decoder is introduced.

`SourceEvalAddressedCompleteness.Allowed` describes independent physical move
routes. `AllowedExpr` composes those conditions through RHS syntax. Memory and
root bindings remain fixed during RHS evaluation, so these permissions do not
assume an addressed parent result or depend on an unknown final answer.
`operand_complete`, `operands_complete` and `expression_complete` prove the
reverse direction for every successful source operand/RHS under these route
conditions. Actual program traces must still discharge the conditions from
active/suspended loan resources; an empty or incomplete protected list does not
become a safety certificate merely because execution succeeds.

## Executable guarded assignment

`SourceHeapGraphTrace.traceGraph` traverses concrete shared/owned pointers under
finite result metadata and validates scalar/constructor shape. `Graph.trace`
proves the computed list is the complete read graph; `guards_unique` derives
uniqueness of that list. This is executable ghost resource bookkeeping in the
source interpretation, not additional work performed by production Rust. Its
meta-interpreter traversal is not a machine/allocator-time claim.

`SourceEvalAddressedAssignments.assign` evaluates its RHS once, requires an
empty destination mask, finds its existing stack binding, computes the RHS read
guard and calls the existing classified/live/bounded guarded `writeStack`.
It initializes the new mask from the same result packet's metadata. Move
protection and retained store contexts are separate lists: protecting every
active local root during operand evaluation would incorrectly prevent ownership
transfer. The destination must avoid both retained resources and the computed
RHS graph, including newly created shared references.

`assign_run` records the concrete composition. `assign_complete` establishes
success from a completed addressed RHS and local destination/guard conditions.
`assign_spec` independently recovers the actual source action and its original
complete `Cost.local Action.weight`, the same storage identity, resulting frame,
RHS graph after the write, retained world and well-formedness. It consumes an
explicit context for the other locals/callers at the actual intermediate mask;
it no longer assumes that arbitrary addressed RHS simulation has been done by
an unspecified parent. Full execution must still construct those contexts and
carry complete exclusive ownership/spatial resources alongside read graphs.

## Consumers and validation

`Tests/SourceAddressedExpressions.lean` constructs an owned payload, an inline
shared alias, an empty destination and a caller retaining a different live local.
It checks concrete payload transfer with a retained Box shell, repeated-move
rejection, protected-root rejection, forbidden owned copying, oversized scalar rejection,
concrete less-than, sequential aggregate assembly, reborrowing, metadata mismatch
rejection, graph tracing, reverse simulation, complete addressed assignment and
caller preservation. Both aggregate metadata and concrete field order are checked.

Reproduce:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Validation passes:

- Full maintained library: 3,925 jobs; all seven new modules have no warnings.
- All 36 maintained Lean suites, native WP and nine Python reifier tests.
- 888 distinct audited endpoints, including 21 new endpoints, with only the
  unchanged `propext`, `Classical.choice`, `Quot.sound` axiom baseline.
- Shared `leanq` inspection of `expression_spec`, `expression_complete`,
  `assign_spec` and `PartialGraph.take`: 283 unique declarations, no unknown
  references; elaborated seed signatures reviewed.
- `git diff --check`; production Rust, generated files, existing model/reader/
  type/control/region definitions and pins unchanged.

Local logs: `/var/tmp/subtree-addressed-rhs-full-build.log`,
`/var/tmp/subtree-addressed-rhs-regression.log`,
`/var/tmp/subtree-addressed-rhs-axioms.log`, and
`/var/tmp/subtree-addressed-rhs-statements.{json,log}`. The focused suite is also
recorded in `/var/tmp/subtree-addressed-expressions-tests.log`. The unchanged
production source retains the `6137120` regeneration/thirteen ordered Rust
checks; no Rust or generated file changed in this increment.

## Remaining work

Construct actual initial/intermediate active and suspended frames along the
113-local evaluator and all callees. Derive complete protected-root coverage,
precise remaining store contexts and exclusive owner/spatial transfer through
these executable RHS steps. A graph/frame view alone does not validate a move
against every live loan. Current protected guards operate on entire roots; no
arbitrary overlapping field-write theorem is claimed.

Compose actions for storage, drop, calls, switches, returns and shared control,
including Box/checked-add intrinsics and the completed ordinary helper safety
chains. Reuse their actual source/cost/type/native certificates. Then discharge
dynamic parsed-region and destructor-instance interpretation, public maximum,
separate wrappers/input policy/global resources/G3, and the remaining
mathematical/software/release/application program. No full C3, compiler,
allocator or runtime closure follows from this RHS/assignment milestone.
Production Rust, generated source, existing source/type/region/control models,
readers and pins are unchanged.
