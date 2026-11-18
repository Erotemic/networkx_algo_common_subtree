# Complete actual evaluator empty-query miss execution

Date: 2026-11-18. Baseline: `45b9f6c` on `Droschinsky-algos`.
Twenty-one new proof modules provide 53 public checked theorems and construct the entire pinned empty-query cache-miss
path, including actual insertion and checked return closure. The public endpoint
is `SubtreeProofs.Rust.SourceEval.Evaluator.empty_miss_total` in
[`SourceEmptyTotality.lean`](../../../../proofs/SubtreeProofs/Rust/SourceEmptyTotality.lean).
The preceding complete cache-hit endpoint remains checked.

This delivers one further actual evaluator path. Pair/pair recursion, overflow
and failure, dynamic parsed regions/destructors, public maximum/cold-table
teardown, wrappers/input policy/resources/G3 and all other planning obligations
remain open. Full SRC-01/C3 and production runtime/resource closure do not follow.

## Independent premises and complete conclusion

Inputs are an existing well-formed world, valid actual suspended callers and
their resource scan, independently readable native shared query packets and an
owned native table packet. `FieldsFootprint`, `OwnerFrame` and `BoxCoverage`
cover the input/caller/external owners. At least one native query is empty and
independent `MemoizedOrderedSolver.findResult table left right = none` selects
the miss. Protected reads are a subset of the original caller reads.

The theorem assumes no cache soundness, successful physical parent execution,
expected physical output or global owner/loan disjointness. It constructs fixed
sufficient fuel and readback thresholds, one final world and readable output
packet, and exact native output
`encodeOutput (some emptyWitness) (.Entry ⟨left, right, emptyWitness⟩ table)`.
It retains well-formedness, protected caller bytes, complete unique/live output,
caller and external Box ownership, and coverage of every live Box. The native
Rust/Aeneas evaluator returns the same result/table.

At every larger fuel/readback pair, actual `Recursive.original` returns that
same world and packet with full cost `emptyRunCost left lookupCost insertCost`.
Lookup and insertion event components equal their independent native event
models. Actual source execution and the existing independent base-source
contract identify the complete cost by determinism. This is the established
operational source currency, with its existing extraction/interpretation
boundaries; it is not a hardware runtime assertion.

## Original query loans and temporary embedding views

`SourceOriginalLoanMachine` generalizes the existing query machine to a finite
family of nonowning locals whose actual loans originate below the pre-entry
memory length. The active family `[1, 2, 13]` includes the copied query tuple.
Closed owned locals remain unrestricted. Its move, assignment, allocation,
zero-owner drop and storage-retirement theorems derive selected permissions
from canonical inventories, fresh stack roots and preserved old caller reads.
`SourceOriginalRetirement` executes existing finite retirement plans while
retaining this invariant and exact memory preservation.

`SourceEmbeddingLoanCells` extends the structural word-loan argument to native
embedding referents. Their reads select the inline embedding/word/scalar or
word-owned descendants; they cannot select a word-opaque table root.
`SourceEmbeddingLoanPermissions.allowed_table_local` consequently derives the
actual table move permission while embedding views remain live. Query references
may still select words inside table-owned entry Boxes.

The strengthened existing `query_view_complete` additionally transports an
untouched zero-owner local's original loan origin. Existing query-origin
conclusions remain. This carries tuple 13 through both query views.
`Prefix.unshared_local_same`, `Prefix.observed_local_same`,
`Prefix.closed_outside` and `Prefix.open_view_closed` reuse actual non-call
semantics to retain masks and scope through the new temporaries.

## Actual instructions, routing, return and closure

`SourceEmptyMissProgram.emptyLeft_actions` checks the exact pinned 47-action
empty branch, with its actual return. The prior `emptyRight_eq_emptyLeft`
identifies the other empty branch. The construction proceeds through:

- `empty_witness_complete`: actions 0–6 construct the native empty witness in
  local 16 and drop/retire its moved word temporary 17.
- `empty_table_transfer_complete`: actions 7–9 open result/table temporaries
  and move the owned table from local 3 to 19.
- `empty_query_views_complete`: actions 10–13 construct the two actual query
  reference views, retaining tuple 13's original loan bound.
- `empty_embedding_views_complete`: actions 14–17 construct witness views
  23 and 22. The temporary embedding loan into fresh witness 16 is tracked
  separately from the original query tuple loans.
- `empty_insert_call_complete`: action 18 constructs actual argument scanning,
  selected table/reference moves, native helper totality and result storage in
  18. Reference 23 ends at its actual last use; moved argument masks clear.
  The original-loan family is restored immediately after insertion.
- `empty_insert_retire_complete`: actions 19–24 retire every insertion
  argument/view root while retaining witness, inserted table and return storage.
- `empty_return_packing_complete`: actions 25–33 move witness and inserted table
  through the actual optional/table temporaries and assemble output tuple 0.
- `empty_cleanup_return_complete`: actions 34–46 drop moved-out temporaries,
  retire all remaining nonreturn roots, and perform actual guarded return
  extraction. All masks are empty after extraction.

`empty_insertion_prefix_complete` composes stable sufficient helper bounds.
`empty_branch_complete` composes all 47 actions and return.
`empty_cases_complete` executes the native left-empty route or both word
switches on the nonempty-left/empty-right route; actual early returns bypass
the retained joins. `entry_empty_body_complete` composes parsed native entry,
all fourteen common lookup actions, all eleven miss-setup actions, lookup
routing and the complete selected body at shared sufficient bounds.

`empty_miss_total` uses the existing typed source agreement and global ownership
results, constructs checked stack closure, and lifts the invocation into the
actual recursive dispatcher. Existing `Recursive.original_enlarge` preserves
its fixed world/packet/full cost at every larger pair of bounds.

## Consumers and validation

The extended `Tests/SourceCacheMissSetup.lean` retains the prior miss-scope test
and adds two whole-invocation consumers. In the first, both empty query pointers
select the same inline word in a Box owned by the input table. In the second,
the left query selects a nonempty word and the right query an empty word in that
same table-owned entry, exercising both word switches. The old table's key is
`(Empty, Pair Empty Empty)`, so both native queries independently miss. Each
consumer derives readable native output, well-formedness, complete ownership/
coverage and stable actual world/packet/full cost from the new theorem.

The 4,093-job root library build and all six affected Lean suites pass, including
the eight recursive runtime cases. The opt-in audit checks 1,652 endpoints,
including all 53 new public theorems, with only `propext`, `Classical.choice` and
`Quot.sound`. Ten elaborated statement seeds cover 1,314 unique declarations
with no unknown references. Thirteen ordered Rust tests and nine standalone
Python frontend regressions freshly pass. The full 47-suite/native-WP evidence
at `d49f638` is inherited, not rerun. No Rust source, generated extraction,
interpreter semantics, parser, tool or dependency pin changes are included.

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
  --out /var/tmp/subtree-empty-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.empty_miss_total \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_empty_body_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.empty_branch_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.empty_insert_call_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.empty_embedding_views_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.empty_return_packing_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.empty_cleanup_return_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.OriginalLoanMachine.rootLoans \
  SubtreeProofs.Rust.SourceEval.Addressed.allowed_table_local \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Graph.shared_result_reads
```

All seven caches are guest-ext4 bind mounts; all Lake/Lean commands run from
`proofs`. Cargo metadata selects the mounted standalone-crate target, and Cargo/
Rustup homes are ext4. Machine-local logs are
`/var/tmp/subtree-empty-{build,consumer,expressions,control,helpers,lifecycle,
runtime,axioms,statements,rust,python}.log`, with elaborated statement JSON at
`/var/tmp/subtree-empty-statements.json`.

## Next work

Construct the pair/pair recursive source scopes, query field views and selected
recursive call transfers from the accepted `MissScope`. Use smaller native word
requests to obtain finite stable sufficient budgets for each recursive call,
then compose success/overflow/failure/choice/insertion/cleanup paths. Preserve
legal query/table/caller aliases and account for fresh copied/concatenated
witness loans separately from original query origins. Finish dynamic parsed
regions/destructors, public maximum/cold-table teardown, wrappers/input policy/
resources/G3 and every other planning target. The full goal remains active.
