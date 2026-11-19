# Complete head failure and constructed tail recursion

Date: 2026-11-18. Baseline: `4611592` on `Droschinsky-algos`.
Fifteen new modules provide 24 public checked theorems. This increment constructs
the complete actual head-failure invocation and the successful-head path through
the actual tail recursive call. Both use explicit universal native contracts
for strictly smaller requests. Full pair/pair induction remains open.

The main endpoints are `SubtreeProofs.Rust.SourceEval.Evaluator.head_failure_total`
in [`SourceHeadFailureTotality.lean`](../../../../proofs/SubtreeProofs/Rust/SourceHeadFailureTotality.lean)
and `SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_tail_prefix_complete` in
[`SourcePairTailEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairTailEntry.lean).
The preceding complete cache-hit and empty-query miss endpoints remain checked.

## Complete selected head-failure path

`head_failure_total` takes independently readable native inputs and complete
input/caller/external ownership, a native parent cache miss, the universal
contract `NativeTotal lh rh` for the smaller head pair, and independent native
head failure `memoized_common_embedding lh rh table = .ok (none, output)`.
The recursive premise is explicit and remains to be discharged by the full
pair/pair induction. No successful physical parent run or post-callee frame is
supplied. Cache soundness and global owner/loan disjointness are not required.

The theorem constructs parsed entry, common lookup, miss setup, all twenty-six
head instructions, native head-failure selection, output packing, input cleanup,
all retained word/lookup joins, parameter cleanup, guarded return and checked
stack closure. It returns native `None` with the head request's actual updated
table, a readable output packet, well-formedness, protected caller bytes,
complete output/caller/external Box ownership and coverage of every live Box.
One fixed final world, packet and complete cost persists at every larger fuel/
readback pair. `Evaluation minimumFuel ... none output cost` retains exact
source/native value/table/full-cost agreement.

`failure_pack_complete` constructs the shared nine-instruction failure output
pattern at explicit distinct local slots. It opens an actual nullary `None`,
moves the updated table, assembles output zero, drops the moved-out temporaries
and retires their storage. `headsFailure_actions` identifies the pinned head
instance `(source, optional, table) = (32, 39, 40)`. The statement retains all
selected slot, initialization and native type requirements rather than assuming
successful assignment. This reusable pattern also fits later failure exits.

`head_failure_cleanup_complete` constructs all ten actual `cleanupInputs`
actions. On this path payload 37 is empty, table 32 has moved into output,
result 31 is `None`, and original query views/tuple contain zero Box owners.
`original_return_complete` handles the real outer parameter cleanup/return
for an arbitrary original-loan family once only output/parameter roots remain.

`head_failure_continuation_complete`, `pair_cases_next` and
`entry_head_failure_body_complete` compose actual native inspection, word cases,
linear prefixes and their real joins into the returned parent body.
`evaluator_body_close_total` factors checked closure and recursive-dispatch
lifting for constructed native bodies. It derives source/native `Evaluation`,
complete owner resources and stable exact costs from actual entry/body/return
proofs; its body-success premise is discharged by the head-failure construction.

## Successful head payload and actual tail call

`recurseTails_actions` checks the unchanged 24-instruction tail prefix and its
actual tail-result switch. The current endpoint constructs instructions 0–13:

- `tail_head_payload_complete` executes the first six instructions. It moves
  the head embedding out of optional 31 through temporary 38 into the existing
  fresh payload root 37, drops/retires moved-out 38 and retains its partial
  optional mask. Complete head ownership and original query loans are preserved.
- `pair_tail_arguments_complete` constructs instructions 6–12: fresh result
  root 43, native tail reborrows 44/45 from Box-field views 28/30, and updated
  table transfer from 32 to argument 46.
- `pair_tail_call_complete` constructs instruction 13 through actual recursive
  dispatch. Its premise is `NativeTotal lt rt`; no completed physical call or
  supplied result store is assumed. The head embedding remains owned in 37,
  optional 31 retains its moved payload hole, table 32 is empty, and native
  tail output resides in 43. All argument masks clear.

`original_evaluator_call_complete` supplies the same actual call construction
at arbitrary explicit local slots. Original shared-loan bounds derive selected
argument moves, while the existing smaller native contract, suspended-context
transport and checked store supply fixed sufficient bounds and exact stable
whole-call world/activation/full cost. Canonical original-loan families persist.

`pair_tail_prefix_complete` composes all fourteen instructions. It retains the
native input queries, tuple and four Box-field views, owned head embedding,
native tail output, empty return storage and precise root support. Native
`tail_request_smaller` proves strict decrease in the sum of Dyck semilengths.
`entry_pair_tail_prefix_complete` connects parsed entry/common/miss/head setup
and the tail call at shared sufficient bounds, using independent native head
success to select the path. It retains separate actual prefix derivations with
their true continuations. Tail-result extraction, its switch, later branches
and the successful parent return are not yet constructed.

## Consumers and validation

The extended `Tests/SourceCacheMissSetup.lean` starts with both parent queries
selecting the same nonempty word inside a Box owned by the input table. The head
empty/empty request misses and inserts its result; the actual empty/empty tail
request then hits that updated table. Both smaller native contracts are proved
base instances, so the consumer supplies no successful physical execution or
pair/pair-totality premise. It derives parsed entry and all four common/miss/head/tail
prefix boundaries, the exact updated tail table, complete original-loan machine,
owned head embedding, partial head optional and cleared table source.

The existing eight-case runtime suite includes the full warm-table head-failure
case with 1,189 source steps and four solver calls. Its actual recursive run
checks complete source value/table/cost agreement, caller-root preservation,
unique/live Box ownership, coverage and final storage cleanup. This is concrete
execution evidence; it does not discharge universal pair/pair induction.

The 4,127-job root library build and all six affected Lean suites pass, including
the eight recursive runtime cases. The opt-in audit checks 1,710 endpoints,
including all 24 new public theorems, with only `propext`, `Classical.choice` and
`Quot.sound`. Ten elaborated statement seeds cover 1,321 unique declarations
with no unknown references. Thirteen ordered Rust tests and nine standalone
Python frontend regressions freshly pass. The full 47-suite/native-WP evidence
at `d49f638` is inherited, not rerun. No Rust source, generated extraction,
interpreter semantics, parser, tooling or dependency pin changes are included.

Reproduction commands, from the repository root unless shown:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-head-failure-tail-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.head_failure_total \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_head_failure_body_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.evaluator_body_close_total \
  SubtreeProofs.Rust.SourceEval.Evaluator.failure_pack_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.head_failure_continuation_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_tail_prefix_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_tail_prefix_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.tail_head_payload_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.original_evaluator_call_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.tail_request_smaller
```

All seven caches are guest-ext4 bind mounts; all Lake/Lean commands run from
`proofs`. Cargo metadata selects the mounted standalone-crate target; Cargo and
Rustup homes are ext4. Machine-local logs are
`/var/tmp/subtree-head-failure-tail-{build,consumer,expressions,control,helpers,
lifecycle,runtime,axioms,statements,rust,python}.log`, with statement data at
`/var/tmp/subtree-head-failure-tail-statements.json`.

## Remaining work

Construct the last ten tail-prefix instructions: argument retirement, native
optional/table extraction, moved-out output cleanup and fresh payload storage.
Then select tail failure or score arithmetic, derive owned-witness destruction
permissions/provenance while preserving permitted query/table/caller aliases,
and complete overflow, both contraction requests, choice, final insertion and
parent cleanup/return. Discharge all smaller-request `NativeTotal` premises by
the complete pair/pair induction. Track fresh copied/concatenated witness loans
separately from original query origins; complete ownership alone is not a
substitute for selected destructor loan permission. Dynamic parsed regions/
destructors, public maximum/cold-table teardown, wrappers/input policy/resources/
G3 and every other planning target remain. Full SRC-01/C3 and the full goal stay
open; no production runtime/resource closure follows from this increment.
