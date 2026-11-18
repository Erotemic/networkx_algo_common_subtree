# Complete left-contraction failure dispatch

Baseline: `c669e99` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [root-overflow checkpoint](memo-evaluator-root-overflow.md) constructs both
checked-add failure returns. This follow-up constructs the entire left-
contraction None return, including destruction of the owned concatenated query
and matched candidate. Right-contraction failure and universal pair/pair
induction remain open.

## Shared outer return

`SourcePairFailureOuterReturn.lean` proves
`pair_failure_outer_return_complete`. Once the updated table is packed into
None output, it retires total scalar storage58, executes tail/head/input cleanup
joins, and constructs the guarded parameter return. Its independent inputs are
actual seventeen-root presence, older cleanup masks, empty moved table42, zero
owners in scalar58, both retained head/tail owner bounds and the initialized
output packet. Existing fresh retirement and exact drop-mask counts construct
every instruction. Old table/query/caller aliases remain permitted.
`SourceRootOverflowContinuation.lean` now reuses this suffix with its original
statement unchanged; root-overflow runtime/kernel consumers are rerun.

## Left storage, packing and owned cleanup

`SourceLeftFailureProgram.lean` identifies the actual nine packing instructions
at `(source, optional, table) = (75,83,84)` and all nine `cleanupLeft` actions.
`pair_left_root_presence` derives exactly twenty-two bound locals from real
root-score presence and the sixty-instruction matched/left prefix: the fifteen
tail roots plus51/58/64/71/74/75/81.

`SourceLeftFailureCleanup.lean` proves `left_failure_cleanup_complete`.
After table75 moves into output, empty payload81, moved table75 and scalar/None
option74 retire. The retained concatenated word71 and matched candidate64 are
both dropped using their independently derived owner bounds; actual drop-mask
counts justify their following storage-dead instructions. Seventeen older roots
remain. Output None/table, complete ownership/coverage and count survive.

`left_failure_continuation_complete` in `SourceLeftFailureContinuation.lean`
constructs the actual None74 selection, updated-table packing, owned cleanup,
all five cleanup joins and guarded return. Both witness words have already moved
into candidate64, so retained locals37/47 are result-word holes with zero owners.
Their zero counts and scalar58's zero count follow from the actual scope and
prefix preservation. Older masks persist. The shared outer return executes
from those checked facts; no parent run or successful close is supplied.

## Whole original body and checked dispatcher

`entry_left_failure_body_complete` in `SourceLeftFailureBody.lean` starts with
parsed readable pair/pair inputs and complete resources. Three explicit smaller
`NativeTotalFresh` contracts cover heads, tails and concatenated-left recursion.
Independent native equations establish head/tail success, subtotal/root success,
left None and the initial lookup miss. Actual prefix determinism aligns the
early miss setup; six prefixes plus the complete matched/left prefix derive
root presence, older masks, empty return storage and four prior optional tags.
The full sixty-instruction prefix, five cleanup joins, outer word/lookup routing
and guarded return compose to the original body. No parent native equation,
physical success, desired post-frame or close is assumed.

`SourceLeftFailureTotality.lean` separately derives the parent native None
equation and proves `left_failure_total_fresh`. Checked entry/closure supplies
readable None/actual updated-table output, well-formedness, protected caller
reads, complete output/caller/external ownership and live-Box coverage,
source/native agreement, result-field provenance and exact world/packet/full-
cost stability at all larger sufficient fuel/budget pairs. The three smaller
contracts remain explicit for general induction. Old table owners are allowed.
Earlier statements/contracts, independent specifications, source semantics,
generated artifacts, maintained Rust and pins are unchanged. Logical retirement
is distinct from physical allocator cost and peak-space bounds.

## Proved smaller instance and concrete consumers

`SourceMinimalPairTotality.lean` proves `empty_request_some` from the native
empty/cache-hit equations and `native_minimal_pair_total_fresh` for the one-edge
pair versus itself, universally over typed warm tables and legal native frames.
It splits the actual top lookup and checked-add results, reusing complete
cache-hit, subtotal/root-overflow and successful-parent constructors. All four
smaller requests have an empty side and use the proved empty fresh bases. Both
contraction results are independently Some by native empty semantics. This
specific universal instance supports a concrete larger failure consumer; it is
not universal totality for arbitrary pair/pair words.

`Tests/SourceLeftFailure.lean` discharges all three smaller contracts with proved
empty bases and the new minimal-pair instance. Two warm keys return nonempty
witnesses scoring 2^31 and zero. The parent subtotal and root score fit, but its
smaller left request doubles 2^31 and overflows. The actual None return drops the
six-owner matched candidate and two-owner concatenated query. Its right query
borrows inside the old table; five external left-query owners remain covered.
The kernel consumer constructs the entire dispatcher, readable None/table
output, ten output owners, complete output/external coverage, result provenance
and stable larger bounds. Ten output owners match the old table's size; count
alone is not an owner-address identity proof. No cache-soundness premise is
appropriate for this arbitrary typed warm-cache source case.

`Tests/SourceRecursiveExecution.lean` adds
`left-failure-owned-candidate-query`, with the same cached scores and nonempty
witnesses. It checks 3,130 source steps and six solver calls, complete source/
addressed value/table/cost equality, suspended caller guard bytes/liveness,
owner uniqueness/live-Box classification, complete output/caller coverage and
retirement of every other new storage cell. The runtime suite has twelve cases.

## Validation

The 4,335-job library build and all ten affected Lean suites pass, including
twelve runtime cases and all previous whole-parent/output/choice/cleanup
consumers. All 2,110 unique
audited endpoints, including eleven new theorems in seven new proof modules,
retain only `propext`, `Classical.choice` and `Quot.sound`. One existing root-
overflow module also reuses the new shared suffix. Eight elaborated statement
seeds export 1,313 unique records with zero unknown references. Source scans
identify candidates; accepted status comes from Lean and the axiom audit.
Thirteen ordered Rust tests and nine Python frontend checks freshly pass.
The new kernel consumer is in ordinary verification CI. CI lists fifty-four
suites; this checkpoint freshly ran the ten affected suites, not all fifty-four.
Full 47-suite/native-WP evidence at `d49f638` remains inherited.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceLeftFailure.lean)
(cd proofs && lake env lean Tests/SourceRootOverflow.lean)
(cd proofs && lake env lean Tests/SourceSubtotalOverflow.lean)
(cd proofs && lake env lean Tests/SourceNoneResultProvenance.lean)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceParentOutput.lean)
(cd proofs && lake env lean Tests/SourceParentChoices.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo metadata --locked --no-deps --format-version 1 \
  --manifest-path rust/crates/verified_ordered_core/Cargo.toml
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  aiq-lean source scan --root proofs --json > /var/tmp/subtree-left-failure-source.json
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-left-failure-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.left_failure_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_left_failure_body_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.left_failure_continuation_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.left_failure_cleanup_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_left_root_presence \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_failure_outer_return_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.native_minimal_pair_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.empty_request_some
```

Logs use `/var/tmp/subtree-left-failure-{outer,cleanup,continuation,body,totality,
minimal,root-reuse,build,consumer,parent,root,subtotal,none,output,choices,control,
lifecycle,runtime,axioms,statements,rust,python}.log`, plus source/statement JSON.
Accepted program/cleanup rebuilds are retained in the continuation log; earlier
failed drafts are superseded by those accepted builds. All ten regression
commands start after their required compiled artifacts are available; parent
and runtime suites start after the complete library rebuild. All seven caches
are checked ext4 bind mounts; Cargo metadata selects the mounted standalone
target and Cargo/Rustup homes are local ext4.

## Remaining work

Construct right-contraction failure, then universal pair/pair `NativeTotalFresh`
induction. Dynamic regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and every other planning requirement remain
open. No full SRC-01/C3 or production resource closure is claimed; the full goal
stays active.
