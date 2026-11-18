# Both actual parent choices through the insertion continuation

Baseline: `ebae9c9` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [generic original-loan choice constructor](memo-evaluator-choice-owner-constructor.md)
now constructs both real parent choice calls, their temporary setup, retirement
and final observation. Successful-right payload extraction plus the two choices
execute the first twenty-one actual finish instructions and reach `finishCode 21`.
Insertion and the remaining finish continuation are not yet executed.

## First actual choice

`SourcePairFirstChoice.lean` proves `pair_first_choice_complete`. It constructs
all nine instructions at finish indices 6--14: open outer slot 99, open first
result 100, move matched candidate 64 through 101, move left witness 81 through
102, execute the real recursive chooseLonger from 101/102 into 100, then retire
102 and 101 physically. Exact transfer plans derive both actual argument owner
bounds; the existing forward constructor derives transfer permission and full
callee execution without a desired run/post-frame premise.

The result is the independent native `OrderedSolver.selectResult candidate left`
with its exact complete call cost and derived owner bound at 100. The right
witness 95 and owned queries 71/85 retain their bounds. Source locals 64/81 are
empty; outer 99 remains empty with its actual bound root and original empty raw
cell for the second result. Count/frame, other roots and all older root bytes
remain checked. The same constructed worlds/activations work at every positive
recursive fuel and any helper budget.

## Second actual choice

`SourcePairSecondChoice.lean` proves `pair_second_choice_complete`. All six
instructions at indices 15--20 move right witness 95 through new temporary 103,
execute chooseLonger from 100/103 into 99, retire 103 and 100 physically, and
perform the actual fake read of 99. The selected native output and exact call
cost are constructed; the output bound at 99 and both owned-query bounds survive
all cleanup. Source 95 is empty. Closed untouched masks, original query snapshots,
other roots and all older root bytes except the written destination remain
checked. Stable execution again needs only positive fuel, at any helper budget.

`SourcePairChoices.lean` defines `selectedWitness` as the two independent native
selections and proves `pair_choices_complete` for all fifteen real instructions.
It exposes both actual recursive call worlds, prepared arguments and exact costs,
first-nine and second-six prefixes, and their composed full prefix. All seven
moved/retired local masks 64/81/95/100/101/102/103 are empty; argument roots
100--103 are unbound. A generic unchanged-unshared-mask guarantee also preserves
the original mixed query tuple without treating it as a closed owned value.

## Successful-right payload to insertion

`SourcePairFinishChoices.lean` proves `pair_finish_choices_complete`. It starts
with the earlier actual right-result scope, right optional witness bound at 88
and held bounds for 64/71/81/85. It constructs the six successful-right payload
instructions, derives witness 95, then constructs both choice regions. The
actual first twenty-one finish instructions reach `finishCode 21`, whose first
instruction opens insertion output 104.

`FinishChoicesScope` records selected 99, original query references 1/2 and tuple
13, ended child views 27--30, head/tail scalar holes, total, both owned queries,
option holes, table 89, emptied old table/witness masks and physical retirement.
All three former candidate masks are empty while their physical roots await
later source cleanup. Complete ownership/coverage, count/frame, unchanged other
roots and appropriate older root bytes remain checked. Selected witness 99 and
owned queries 71/85 have bounds relative to the original parent heap.

All preceding endpoint statements, explicit smaller `NativeTotalFresh` contracts,
independent native success/checked-add hypotheses, generated files, maintained
Rust, source semantics and dependency pins are unchanged. The finite finish
program remains definitionally tied to the real pinned source by `finish_actions`.
These constructors assume neither a successful whole-parent invocation nor a
universal stronger recursive contract or cache soundness.

## Consumers and adversarial paths

The added parsed-entry consumer in `Tests/SourceCacheMissSetup.lean` uses twenty
old table Box owners and original queries borrowing a nonempty table-owned word.
All four smaller requests hit nonempty cached Pair witnesses of score seven.
Proved empty-query fresh contracts discharge all smaller obligations. Parsed
entry, both contractions, their cleanup, successful-right payload extraction and
both actual choices reach the insertion continuation. The matched score-fifteen
witness beats both score-seven alternatives; actual local 99 has exactly six
bounded owners. Both owned-query bounds and all four retired argument roots are
checked, without a desired final frame or successful parent call as a premise.

`Tests/SourceParentChoices.lean` constructs an independent valid fixture for the
real fifteen-instruction two-choice region, including complete input resources
and actual temporary setup. Three candidates have distinct native word shapes
with two, four and six Box owners. All three scores are arbitrary U32 values.
Transferred owners lie beyond a two-cell original heap, while two older external
Boxes remain live and excluded from every selected inventory.

Four kernel consumers expose the native branch choice through owner counts:
first wins (two owners), middle wins (four), last wins (six), and equal scores
retain the first (two). The underlying construction quantifies all score triples.
No successful choice run, callee output or expected post-frame is supplied.

## Validation and reproduction

The 4,274-job root library build and five affected Lean suites pass: complete
parsed-parent consumers, distinct-shape parent choices, addressed control, owner
lifecycle and all eight recursive runtime cases. All 1,993 unique audited
endpoints, including four new public theorems across four modules, retain only
`propext`, `Classical.choice` and `Quot.sound`. Eight elaborated statement seeds
resolve 1,319 unique declarations with zero unknown references. Thirteen ordered
Rust tests and nine Python frontend checks freshly pass.

The full 47-suite/native-WP evidence at `d49f638` is inherited, not rerun. All
seven build caches are guest-ext4 bind mounts. Cargo metadata selects the mounted
standalone target; Cargo/Rustup homes are ext4. No generated or production source
is changed in this increment.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceParentChoices.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-parent-choices-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_finish_choices_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_choices_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_first_choice_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_second_choice_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.original_choice_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.choice_call_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_right_scope_complete_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.FinishChoicesScope
```

Machine-local evidence uses `/var/tmp/subtree-parent-choices-{first,second,
composed,finish,build,parsed-consumer,branches,control,lifecycle,runtime,axioms,
statements,rust,python}.log` and statement JSON. Shared source scanning supplies
candidates; kernel acceptance and elaborated statements/axiom closure establish
endpoints and assumptions.

## Remaining work

Construct actual insertion argument setup 104--109, including the original-query
reborrows and fresh selected-witness views, the actual insertion call and all
cleanup. Assemble the optional result/table output, execute the remaining owned
query/zero-temporary cleanup and checked return/closure. Retain legal original
query/table/caller aliases and the selected-witness owner bound.

Complete both optional joins, overflow/failure exits, remaining parent returns
and general pair/pair induction, including the universal `NativeTotalFresh`
contract. Dynamic regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and all other planning requirements remain
open. Both choices are constructed; this does not close SRC-01/C3, establish
production resource bounds or complete the full user goal.
