# Complete actual evaluator cache-hit execution

Date: 2026-11-18. Baseline: `e5e229d` on `Droschinsky-algos`.
Nineteen new proof modules and one added theorem in an existing module provide
79 new public checked theorems. Existing native-entry/common-prefix endpoints
also derive and retain query-loan origins. The maintained library now constructs
the whole actual parsed evaluator on cache hits, through return and checked
stack closure, from independently readable native inputs and complete ownership.

The central endpoint is
`SubtreeProofs.Rust.SourceEval.Evaluator.cache_hit_total` in
[`SourceCacheHitTotality.lean`](../../../../proofs/SubtreeProofs/Rust/SourceCacheHitTotality.lean).
This closes the cache-hit physical-totality obligation at the existing addressed
operational boundary. Empty-query misses, pair/pair recursion, overflow/failure
paths, public maximum and full SRC-01/C3 remain open.

## Exact inputs and result

The theorem takes a well-formed world, independently valid actual suspended
callers with their resource scan, readable native left/right shared query packets
and an owned native table packet. `FieldsFootprint`, `OwnerFrame` and
`BoxCoverage` give complete input/caller/external ownership. Protected addresses
are a subset of the actual caller reads. The branch condition is the independent
native `MemoizedOrderedSolver.findResult table left right = some result`.

It requires no cache-soundness, maximum-result, global work bound, expected
physical callee result, successful parent execution, selected move/drop permission,
or separation of all table owners from query/caller loans. Warm tables and cached
witnesses are arbitrary. A cache hit returns the cached result; optimality does
not follow without the separate mathematical hypotheses.

The conclusion constructs fixed sufficient call-fuel and ghost-readback bounds,
one final world, one readable native output packet, and the complete output/
actual-caller/external owner frame and live-Box coverage. The returned value is
`encodeOutput (some result) table`, and the actual native evaluator returns that
same result/table. Every larger pair of bounds runs the original recursive
parsed evaluator to exactly the same world, packet and full cost.

The cost is the existing `hitRunCost lookupCost`: `67 + lookupCost.steps`
operational work steps, the independent lookup event vector, one destructor
visit, zero destroyed Boxes, and one evaluator call. `lookupCost.events` equals
`(LookupEvents.lookup table left right).2`. These are declared operational
currencies, not allocator timings, hardware instructions or a production Rust
runtime bound.

## Query origins and selected root permissions

`SourceNativeQueryEntry.initial_shared_loan_origin` derives that each query's
loans address the pre-entry world, below its memory length. Fresh parameter roots
contribute local reads but do not become shared loans. `SourceQueryLoanOrigins`
transports this fact through actual reference preparation, allocation, guarded
writes, zero-owner retirement and clearing. Full local-resource uniqueness and
the actual read/owner/loan partition justify the transport.

The common prefix now derives and retains these origins from entry through
all fourteen instructions. `SourceQueryCallPreservation` reconstructs actual
post-argument masks and retained-context guards to preserve an untouched query's
read graph through a real helper call. The prefix hypotheses are unchanged;
the query-origin conclusions are stronger.

`SourceEvaluatorClosedLocals` derives that only the original query locals 1/2
can still hold references at the lookup switch. `SourceInlineMovePermissions`
then discharges the actual move guard at a selected fresh stack root. Moving
table local 3 does not require separation of every table-owned descendant from
every query loan. `SourceQueryMachine` combines these facts with the existing
native machine, complete owner invariant and preserved older caller reads.
It constructs the existing assignment, drop and storage-dead operations.

`SourceLocalPreservation` and `SourcePrefixLocals` transport untouched closed
local masks through actual non-call prefixes. `SourceQueryRetirement` constructs
finite sequences of existing zero-owner drops and storage retirement. It keeps
the actual destructor visits, reference-ending scan, root guards and costs;
it is not a replacement executor or parser.

## All twenty hit actions and the return join

`SourceCacheHitProgram.cacheHit_actions` identifies the unchanged pinned branch
with its twenty actual instructions. `SourceCacheHitPrelude.hit_prelude_complete`
constructs payload extraction, movement through temporary 11, optional-result
assembly in 10, retirement of 11 and opening of table-transfer local 12.
`SourceCacheHitTransfer.hit_transfer_complete` moves the table through local 12
and assembles the native output tuple in fresh return storage 0.

`SourceCacheHitCleanup.hit_cleanup_complete` constructs every remaining drop and
retirement, including the retained optional tag's nonzero destructor visit.
`SourceCacheHitBranch.hit_branch_complete` composes all twenty actions and proves
that only return/parameter roots remain. `SourceCacheHitReturn.hit_return_complete`
constructs the real return continuation, retires parameters 3/2/1, derives all
remaining masks are empty, and constructs guarded native return extraction.

`SourceCacheHitContinuation.hit_continuation_complete` constructs actual switch
selection, whole hit branch and return join. `SourceCacheHitBody.entry_hit_body_complete`
composes parsed entry, the common helper call/retirements, branch and return.
`cache_hit_total` uses the existing typed recursive call contracts and complete
owner transfer to construct checked closure, dispatch through the actual parsed
evaluator declaration, and preserve protected caller bytes. Source determinism
identifies its full cost with the existing independent cache-hit source theorem;
actual recursive budget enlargement establishes the stable conclusion.

No generated extraction, Rust/Python implementation, dependency pin, source
semantics, move/drop guard or reference-ending algorithm changed.

## Validation and adversarial consumer

All checks below terminate successfully:

- Full maintained library: 4,061 jobs; replayed warnings are in older modules.
- Five affected suites: `SourceAddressedExpressions`, `SourceAddressedControl`,
  `SourceHelperCalls`, `SourceOwnerLifecycle`, `SourceRecursiveExecution`.
- All eight recursive cold/nonempty/warm-hit/overflow/failure runtime cases retain
  complete values/full costs, caller bytes, live Box ownership/coverage and cleanup.
- The new whole-invocation consumer in `Tests/SourceAddressedControl.lean` has
  both queries selecting inline words inside the same Box owned by the table.
  It obtains actual complete cache-hit execution, native output, full output
  ownership/coverage and stability at every larger fuel/readback pair. An
  all-owner/query-loan separation rule would reject these inputs. Existing warm
  common-prefix and cold actual-suspended-caller consumers also pass.
- `BaselineAudit.lean`: 1,559 distinct endpoints, including all 79 new public
  theorems; only `propext`, `Classical.choice`, `Quot.sound`.
- Ten selected `leanq statement` seeds: 1,326 unique elaborated declarations,
  zero unknown references. Its raw stream reports 1,327 records including metadata.
- Thirteen ordered Rust tests pass, including independent contraction/isomorphism
  oracles, choice materialization and token/index input behavior.
- Nine Python frontend/reifier regressions pass using the documented standalone
  runner. Repository-wide pytest options require an unavailable xdoctest plugin
  in the default interpreter; the standalone suite runs without that plugin.

Broader 47-suite/native-WP evidence remains at `d49f638`, not a fresh full-suite
run of this increment. Rust source remains unchanged.

Reproduction from the repository root:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-cache-hit-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.cache_hit_total \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_hit_body_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.hit_branch_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.hit_return_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_common_prefix_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.initial_shared_loan_origin \
  SubtreeProofs.Rust.SourceEval.Addressed.allowed_inline_from_query_origins \
  SubtreeProofs.Rust.SourceEval.Addressed.QueryMachine.assign_empty \
  SubtreeProofs.Rust.SourceEval.Addressed.RetirementPlan.complete \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.call_preserves_other_local
```

All seven caches are guest-ext4 bind mounts. All Lake/Lean commands run from
`proofs`; actual Cargo metadata selects the mounted standalone crate target.
Cargo/Rustup homes are on ext4. Machine-local evidence:
`/var/tmp/subtree-cache-hit-{build,control,expressions,helpers,lifecycle,runtime,
axioms,statements,python,rust}.log` and `subtree-cache-hit-statements.json`.

## Remaining work

Construct empty-query miss insertion/return from the common native scope, then
all pair/pair recursion and overflow/failure paths with finite stable sufficient
budgets. Derive remaining source-point scope, masks and selected physical/owner-
transfer permissions while preserving allowed query/table/caller aliases.
Interpret dynamic parsed regions/destructor instances and complete public
maximum/cold-table teardown, wrappers/input policy, resource envelopes/G3, and
all other targets in `docs/planning`. The full goal remains active. Checked
physical closure here is symbolic storage retirement at the existing operational
boundary; compiler/reifier/runtime/allocator adequacy obligations remain explicit.
