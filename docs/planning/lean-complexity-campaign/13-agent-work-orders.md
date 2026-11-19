# 13. Bounded work orders

## Shared handoff rules

These orders are implementation assignments for the campaign, not work already completed by this overlay. Every agent starts from a named Git/source baseline, reads the relevant existing declarations and reports exact changes. Preserve independent specifications and generated-code boundaries. Cython is evidence of intent, not a correctness oracle.

Use the current toolchain unless the assignment explicitly owns an isolated compatibility experiment. Do not modify unrelated manifests, rewrite retired Lozano code, invent hidden constant-time axioms or add process-only source-text tests. Report a missing source or theorem as a blocker rather than filling it with an assumption that contains the desired result.

The standard handoff contains: target IDs; baseline/pins; exact declarations and signatures; sources/locators; model level; proof/build commands and results; assumptions/axioms; consumer; counterexample or adversarial case; changed paths; and remaining obligations. A documentation claim that a theorem exists must point to its actual declaration.

## W01. Declaration-level reuse audit

**Own:** a new audit report and machine-readable updates under this campaign's evidence area. No production code changes.

**Read:** L02--L05, L14, R14; current local library audit and `proofs/VERIFICATION.md`.

**Task:** inspect the actual definitions and exported statements for cost composition, totality, realization, primitive contracts, memo support and asymptotic envelopes. Trace each selected declaration to its imported premises. For Lax62, distinguish the general refinement stack from example functional-specification backlog. For arlib, inspect `ExactRealizes` and its RAM interpretation. For L14, inspect the cost-preserving translation and allocation model.

**Deliver:** a row per capability with exact source revision/declaration/type, claim level, reusable fragment, license, build status, compatibility issue and decision. Include negative findings scoped to searched modules. Add contemporary overlapping work found in maintainers' public channels.

**Acceptance:** each proposed implementation target is classified as direct reuse, adapter, genuine new statement, local algorithm work or unresolved. No global absence claim follows from a search miss.

## W02. Actual lookup operation inventory

**Own:** a source/model inventory and a narrowly scoped experimental module/package; no source rewrite.

**Read:** `verified_ordered_core/src/lib.rs`, generated extraction modules, `Rust/MemoizedOrderedSolver.lean`, `Paper2004/MemoizedDynamicProgram.lean` and their exact types.

**Task:** map each lookup/scan operation to the candidate resource model, including structural equality, loop control, early exit and returned representation. Identify translation primitives and the independent postcondition. State source size and failure premises.

**Deliver:** an exact proposed lookup bound, one actual loop bound, a source-event correspondence design and an extra-scan counterexample. Identify what is proved versus trusted at the source boundary.

**Acceptance:** the first pilot uses existing source rather than a surrogate algorithm and has no unknown operation priced at zero.

## W03. Competing backend pilots

The [executed G1 decision](evidence/g1-backend-decision.md) now compares all
three over the same generated source fragment and selects native Std.WP at C2.
The optional arlib/Lax interpreters have exact value/cost correspondence and
source-mutation rejection. Their RAM/IR realization obligations and W06-C3
remain open; no machine/source claim is inferred from the comparison.

**Own:** separate standalone/worktree experiments for the same W02 task. Each candidate has its own manifest and no main-repository dependency changes.

**Task:** instantiate the task in arlib, in the selected timed-refinement route, and through a thin `Std.WP`/cost adapter. Keep input domain, independent result specification and operation model comparable. Audit the new order-maintenance stack for a reusable translation component before writing one. Add Iris only for a demonstrated ownership need.

**Deliver:** buildable theorem/consumer artifacts, printed assumptions, omitted-operation failure, imports and compatibility report. Compare semantic coverage before proof-script size.

**Acceptance:** the integration owner can select a route using concrete evidence. Failed candidates report the exact blocker and retained reusable pieces. No framework-wide ranking is required.

## W04. Checked core statements

**Depends on:** selected semantic boundary from W01--W03.

**Own:** proposed generic statement file and statement review, isolated from completed production theorems while any proof placeholders remain.

**Task:** translate D1--D4 and D7--D8 into checked signatures using actual backend types and declarations. Include multi-root/warm-cache/repeated-request cases. Make totality and error semantics explicit. Produce a small typed client showing that a local recurrence and cache contract fit.

**Deliver:** checked signatures, theorem dependency graph, provenance classification and false-neighbor examples. Record any substantive change to the mathematical dossiers rather than weakening a statement.

**Acceptance:** no undefined placeholder interface conceals the main proof; every future premise is either upstream, an earlier target, or a concrete local obligation.

## W05. Generic memo theorem and two clients

**Executed partial delivery:** [native memo core and exact scope](evidence/memo-interpreter.md).
Interpreter correctness/once-only expansion/exact requests and finite envelopes
compile; list/array contracts and the LV body fit. The
[LV follow-up](evidence/memo-lv-correspondence.md) closes exact old-evaluator
value/table/counter correspondence and warm D-product bounds. The
[unrelated minimum-edit client](evidence/memo-edit-distance.md) now also
compiles with both representations. The [whole-run follow-up](evidence/memo-work-envelopes.md)
now derives primitive budgets and weighted/native-WP envelopes with cache setup.
Remaining work is local input/body/key/materialization cost and source realization,
including the named W06-C3 requirements.
W04's other interfaces and W06-C3 remain retained work.

**Depends on:** W04; source adapter work continues alongside.

**Own:** MEM-01/02/03 and generic tests/examples; local LV adapter in an agreed path.

**Task:** prove the interpreter's correctness, cache preservation, unique expansion, exact request accounting and priced resource bound. Recover the existing LV counters and prove edit-distance or another approved unrelated instance. Instantiate two representation contracts.

**Deliver:** public API, exact and envelope corollaries, two clients and a comparison of removed versus retained client proof work.

**Acceptance:** no tree-specific import in generic modules; no assumed global runtime bound; no loss of existing small-input constants; changed cache representation changes the cost without changing the combinatorial proof.

## W06. Source-to-cost bridge

[Universal checked public maximum and table teardown](evidence/memo-public-maximum-totality.md)
now constructs the complete public core under the existing addressed native
frame model: actual seven-local entry, all 17 parsed instructions, evaluator
call, result-field transfer, table destruction, return and checked stack close.
Cold whole-packet provenance survives guarded storage and the partial tuple
move, deriving the actual table-drop permission while retaining legal aliases.
No child contract, parent success, desired post-frame or successful table drop
is a premise of the public endpoint. Arbitrary finite queries retain native
optional/overflow behavior, matching pure source/full costs, readable output,
complete caller/external resources, every caller read, fresh output owners and
identical world/packet/cost at all larger sufficient fuel/readback bounds.
The separate mathematical endpoint keeps both independent semilength bounds
below 2^32 and proves an optimal ordered tree with the exact edge score.
The 4,360-job library build and eleven affected Lean suites pass. A kernel
consumer uses aliased three-edge queries beside an old dead Box/live scalar
stack cell. A focused actual public maximum checks aliased caller-owned inputs,
2,704 complete steps/five solver calls, full source/addressed cost equality and
retirement of every discarded table owner/new stack cell. All 2,163 audited
endpoints retain the accepted axioms; eight statement seeds export 1,311 unique
records without unknown references. Thirteen Rust tests and nine Python checks
pass. CI lists 59 suites. The separate fourteen-case runtime process remains
live and pending, not counted as a pass. See the evidence report for commands.
Next integrate actual dynamic parsed-region/destructor-instance interpretation,
then indexed/token/reconstruction wrappers, input/error policy/G3 and remaining
resource/representation/global time/space/APP and other planning requirements.
No full SRC-01/C3 or production resource closure is claimed; the full goal stays
active. Source-operation counts and logical retirement retain the D12 boundary.

[Cold evaluator ownership provenance](evidence/memo-evaluator-cold-provenance.md)
now derives freshness of the complete cold output packet, including its actual
updated table. Backward live-Box provenance excludes old dead-cell resurrection
and stack-to-Box conversion through actual stores/actions/helpers, selected
control, recursive dispatch, entry and checked close. Full caller-read
preservation retains caller owner identities even for smaller requested guards.
Complete old live-Box coverage and final owner uniqueness then exclude every old
owner from ownership-free input's returned packet. The cold universal endpoint
constructs actual execution, native/pure-source/full-cost agreement, complete
resources, all caller reads, whole-packet freshness and larger-bound stability;
no child contract, parent success, desired fresh table, cache soundness or width
bound is a premise. Mathematical consistency keeps its independent hypotheses.
The 4,349-job library build and new kernel consumer pass. The consumer uses
aliased three-edge queries beside an old dead Box and live scalar stack cell;
every returned owner lies beyond the entire nine-cell original heap. The public
maximum's exact 17-instruction body also has kernel identity to the parsed
source. Eight affected Lean suites, all 2,146 audited endpoints, thirteen Rust
tests and nine Python checks pass; eight statement seeds export 1,268 unique
records without unknown references. CI lists 57 suites. The prior fourteen-case
runtime process remains live and pending; it is not counted as a pass.
Validation details are in the evidence report.
Next construct the maximum's actual preparation/call/result-field transfer/table
drop/retirement/return with exact costs, using the proved cold provenance.
Dynamic parsed-region/destructor interpretation, wrappers/input policy/G3,
remaining resource/representation/global time/space/APP and other planning
requirements stay open. No full SRC-01/C3 or production resource closure is
claimed; the full goal remains active.

[Universal checked evaluator totality and witness provenance](evidence/memo-evaluator-universal-fresh.md)
now proves `native_total_fresh` for every finite native word pair and arbitrary
typed warm table under the existing legal native/caller/external frame model.
All four smaller contracts are discharged by induction on independent query
semilength, including both contractions. Actual cache/option/checked-add cases
reuse the checked branch constructors; independent functional evaluations supply
child native equations. No smaller contract, desired parent execution/post-frame
or preselected bound remains a premise. The old `NativeTotal` projection and
one-edge theorem remain available unchanged.
The direct endpoint constructs checked dispatch and pure `Evaluation` at the
same complete cost, native result/actual updated table, readable output,
well-formed memory, protected reads, complete ownership/live-Box coverage,
witness-only provenance and exact world/packet/cost at every larger sufficient
fuel/budget. The separate mathematical consistency endpoint retains `TableSound`
and both input semilength bounds below 2^32. It returns Some with the independent
mathematical witness and a sound table; arbitrary warm source execution still
retains every None/overflow behavior. Production complexity does not follow.
The 4,343-job library build and eleven affected Lean suites pass; the larger
fourteen-case runtime suite is running in its original process. The new kernel
consumer supplies two references to one old seven-owner cold three-edge query,
uses no smaller calling contracts and obtains the direct mathematical/source/
resource/stability guarantees. All 2,121 audited endpoints retain the accepted
axioms; five new theorems in three new proof modules are included. Eight statement
seeds export 1,084 unique records without unknown references. Thirteen Rust tests
and nine Python checks pass. CI lists fifty-six suites; this checkpoint runs the
twelve affected suites, not all fifty-six. See the evidence report for commands.
Next compose the public maximum body/cold-table teardown and actual dynamic
parsed-region/destructor interpretation. Indexed/token/reconstruction wrappers,
input/error policy, G3 adversaries, W04/MEM-03/W05/MEM-04 resources, representations/
global time/space, APP and all other planning requirements remain. This is scoped
addressed-source adequacy under D12; no full SRC-01/C3, physical allocator/compiler
or production resource closure is claimed. The full goal stays active.

[Helper owner provenance and constructive concatenation cleanup](evidence/memo-evaluator-owner-provenance.md)
now derives descendant-owner freshness from the actual helper allocation ledger.
Copy/lookup/concatenation helpers receive no owned input cells; every result Box
lies beyond the incoming heap. Guarded storage retains the exact packet owner
list. The native concatenation endpoint derives provenance relative to the
original heap and constructs its guarded owned-word drop while retaining legal
original query/table/caller aliases. Canonical inventories, closed reference
preparation and checked anchored-machine advances preserve established provenance.
Insertion/`boxNew` remain outside this fresh-output class because they transfer
owned descendants. The existing `NativeTotal` contract is unchanged.
The 4,218-job build and seven affected Lean suites pass, including eight runtime
cases. All 1,882 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,002 unique declarations with no unknown references.
Thirteen Rust tests and nine Python checks pass. Nonempty table-owned cache
aliases exercise fresh copy/lookup results and full derived storage; a parsed
nonempty concatenation derives and drops all four result Boxes; actual insertion
retains an old input owner, checking the freshness boundary.
The parent frontier remains the checked seventeen-checkpoint right-result scope.
Recursive witness provenance through complete evaluator execution, payload/
field transfers and choice still needs proof; helper provenance alone does not
supply it. Both optional joins, successful right payload transfer, general owned
cleanup, overflow exits, insertion, remaining parent returns and full pair/pair
induction remain. Dynamic regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and the remaining planning targets stay open.
The full goal remains active.

[Actual right recursion and complete right-result scope](evidence/memo-evaluator-right-scope.md) now
constructs all remaining twenty-one right-region instructions and the full
36-instruction prefix through seventeen stable checkpoints from parsed entry.
Original left-query view 91 and fresh right-word views 93/92 remain separate;
actual preparation ends 93, the call consumes 91/92/94, and original loan
origins are restored before physical retirement. Native option/table 88/89,
empty bound payload 95, both owned queries, held left witness, matched candidate,
exact original aliases and complete ownership/coverage persist. Every future
parent root at index 96 or above is unbound. Both actual contraction calls and
their complete costs are exposed. The fourth smaller `NativeTotal` premise is
explicit; the right result/table are derived. No physical parent success,
expected right post-frame/result, cache soundness or witness freshness is assumed.
The 4,214-job build and six affected Lean suites pass, including eight runtime
cases. All 1,871 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,312 unique declarations with no unknown references.
Thirteen Rust tests and nine Python checks pass. Three new consumers discharge
all four smaller calls with proved empty contracts: all seventeen checkpoints
with table-owned aliases; a two-Box left witness/six-Box candidate through right
cleanup; and cold head/left/right insertions reaching the actual right switch.
Both optional joins, successful right payload transfer, recursive witness
provenance/general owned cleanup, overflow exits, choice, insertion, remaining
parent returns and full pair/pair induction remain. Dynamic regions/destructors,
public maximum/cold-table teardown, wrappers/input policy/resources/G3 and the
remaining planning targets stay open. The full goal remains active.

[Successful-left payload and actual right-query concatenation](evidence/memo-evaluator-right-concatenation.md) now
constructs all fifteen initial right-region instructions through thirteen stable
prefix checkpoints from parsed entry. The owned left witness moves through
scratch 82 into 81; original right child reborrows execute concatenation into
85 and retire 86/87. The matched candidate, native table, exact original query
aliases and complete ownership/coverage persist; all future parent roots at
index 88 or above are unbound. Native append, helper events and the full actual
concatenation call cost are identified. Smaller head/tail/left `NativeTotal`
and independent native success/addition equations, including native left
success, remain explicit. No physical parent success/post-frame, cache soundness
or recursive witness freshness is assumed.
The 4,204-job build and six affected Lean suites pass, including eight runtime
cases. All 1,859 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,306 unique declarations with no unknown references.
Thirteen Rust tests and nine Python checks pass. Three new consumers cover all
thirteen checkpoints with table-owned repeated aliases, actual transfer of a
two-Box left witness beside a six-Box candidate, and a four-Box right query.
Right argument/fresh-view setup, right recursion and its remaining twenty-one
instructions, both optional joins, recursive witness provenance/owned cleanup,
overflow exits, choice, insertion, remaining parent returns and full pair/pair
induction remain. Dynamic regions/destructors, public maximum/cold-table
teardown, wrappers/input policy/resources/G3 and all other planning targets
stay open. The full goal remains active.

[Complete actual left contraction result scope](evidence/memo-evaluator-left-scope.md) now reaches the
real optional-result switch through twelve stable prefix boundaries and exposes
the composed sixty-instruction matched/left-contraction prefix. All eleven
instructions 49–59 retire moved arguments, extract option/table into 74/75,
clean the moved tuple, retire ended view/output roots and open payload 81.
Actual continuation preparation ends view 78; moved/ended masks restore the
strictly original loan family before physical stack retirement. Complete
ownership/coverage, exact queries, matched candidate, owned word 71 and native
left output survive. Every future parent local at index 82 or above is unbound.
Generic fresh-write memory preservation includes already retired cells; parent
root-change certificates cross actual calls. Smaller head/tail/left `NativeTotal`
and independent native head/tail/score successes remain explicit; no successful
physical parent run, expected post-frame, expected left result, cache soundness,
recursive witness freshness or global alias ban is supplied.
The 4,195-job build and six affected Lean suites pass, including eight runtime
cases. All 1,849 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,311 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. Three added kernel
consumers discharge all smaller contracts with proved empty cases: repeated
table-owned aliases derive all twelve checkpoints/full sixty-instruction prefix;
a six-Box matched candidate survives real cleanup; and cold recursive insertion
reaches native fields 74/75 and empty bound payload 81 at the actual switch.
Successful-left payload extraction, right concatenation/views/call, both left/
right joins, recursive witness provenance/owned cleanup, overflow exits, choice,
insertion, remaining parent returns and full pair/pair induction remain. Dynamic
regions/destructors, public maximum/cold-table teardown, wrappers/input policy/
resources/G3 and every other planning target stay open. The full goal is active.

[Constructed actual left contraction call](evidence/memo-evaluator-left-recursion.md) now reaches its native
recursive return through eleven stable actual prefix boundaries from parsed
entry. Four argument instructions reborrow the original right query into 79
and move the owned table from 42 into 80; the actual evaluator call consumes
77/79/80 and stores its native optional/table output in 76. The retained argument
checkpoint exposes one fixed actual call and complete call cost at every larger
shared helper bound pair. Complete ownership/coverage, exact original queries,
owned word 71, matched candidate, scalar holes and original/fresh loan provenance
persist. The explicit third recursive premise is universal `NativeTotal` for
the strictly smaller concatenated-left request. No successful physical parent
run, expected post-callee frame, expected left result, cache soundness, recursive
witness freshness or global alias ban is supplied.
The 4,185-job build and six affected Lean suites pass, including eight runtime
cases. All 1,833 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,304 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. Three new consumers
discharge all smaller contracts with proved empty cases: table-owned repeated
aliases derive all eleven prefixes and exact-cost call; a six-Box matched
candidate survives real recursion; and a cold external-alias parent executes
a contraction miss that inserts a second native table key.
Instructions 49–59 still require moved-argument retirement, result/table
extraction, fresh-view ending, moved-tuple cleanup and payload opening before
the actual left-result switch. Left/right contraction branches, recursive
witness provenance/owned cleanup, overflow exits, choice, insertion, remaining
parent returns and full pair/pair induction remain. Dynamic regions/destructors,
public maximum/cold-table teardown, wrappers/input policy/resources/G3 and every
other planning target stay open. The full goal remains active.

[Constructed fresh owned-word views](evidence/memo-evaluator-owned-word-loans.md) now reaches actual references
78/77 to concatenated word 71 through nine stable prefix boundaries from parsed
entry. All five setup instructions construct result/reference storage, borrow
the owned word and reborrow through the first reference. `AnchoredLoanMachine`
retains strict pre-entry bounds for original query loans and separate precise
support for fresh word loans. The word's actual read footprint contains its
Box owners and own stack root; other selected stack roots remain available
for moves/stores/retirement. Complete owner uniqueness also separates this
anchor from other locals' owners, leaving original-query destructor obligations
explicit. Exact native queries, matched candidate, updated table and original
origins persist. Smaller head/tail `NativeTotal` and independent native successes
remain explicit; no successful physical parent run, cache soundness, recursive
witness freshness or global alias ban is supplied.
The 4,177-job build and six affected Lean suites pass, including eight runtime
cases. All 1,820 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,293 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. New table-owned alias
and nonempty four-Box consumers discharge smaller contracts with proved empty
cases, derive all nine prefixes/result-root permission and separate matched
candidate owners from the fresh-loan anchor.
Right argument 79, table argument 80, the left contraction call and anchored
call preservation/cleanup remain. Recursive witness provenance/owned cleanup,
overflow exits, both contraction joins, choice, insertion, remaining returns
and full pair/pair induction remain. Dynamic regions/destructors, public maximum/
cold-table teardown, wrappers/input policy/resources/G3 and every other planning
target stay open. The full goal remains active.

[Constructed left-query concatenation](evidence/memo-evaluator-left-concatenation.md) now reaches owned appended word
71 through eight stable actual prefix boundaries from parsed evaluator entry.
All nine concatenation instructions construct original child reborrows, execute
the unchanged helper, retire moved argument roots and retain the matched
candidate, table, total and all seven exact original query/view snapshots.
Generic mask preservation supports actual calls and suffix preparation; exact
native append, structural helper events and complete concatenation call cost
are identified. Both native contraction requests strictly decrease the independent
Dyck-word induction measure. Smaller head/tail `NativeTotal` and independent
native success equations remain explicit; no successful physical parent run,
cache soundness, recursive witness freshness or global alias ban is supplied.
The 4,168-job build and six affected Lean suites pass, including eight runtime
cases. All 1,788 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,309 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. Two additional kernel
consumers discharge smaller contracts with proved empty cases: table-owned
repeated aliases derive all eight prefixes, and two nonempty concatenation
operands produce a four-Box owned word with complete external/table ownership.
Fresh references to word 71 and their selected loan permissions, both contraction
calls, recursive witness provenance/owned cleanup, overflow exits, choice,
insertion, remaining returns and full pair/pair induction remain. Dynamic
regions/destructors, public maximum/cold-table teardown, wrappers/input policy/
resources/G3 and every other planning target stay open. The full goal is active.

[Constructed owned matched witness](evidence/memo-evaluator-matched-scope.md) now
constructs the first thirty actual successful-root-score instructions through
matched candidate 64: total extraction, two real Box allocations, owned pair-word
assembly, score attachment and all moved-out temporary cleanup. The parsed
`Evaluator.entry_pair_matched_scope_complete` retains seven actual prefix
boundaries at shared sufficient bounds, complete original-loan machinery,
native candidate, scalar-only head/tail masks and fresh concatenation storage.
Smaller head/tail `NativeTotal` and independent native score successes stay
explicit; no physical parent success, cache soundness, witness freshness or
global alias ban is supplied. Generic Box/aggregate constructions transfer
complete owners through the unchanged actual helpers and checked stores.
The 4,158-job build and six affected Lean suites pass, including eight runtime
cases. All 1,757 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,301 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. Table-owned alias
consumers discharge both smaller contracts with proved empty cases: one derives
all seven prefixes; another uses nonempty cached witnesses and constructs a
candidate with six owned Boxes, preserving complete ownership and coverage.
Retaining exact query/view snapshots through the matched prefix, concatenation,
fresh query-loan tracking, both contraction calls, recursive witness provenance/
owned cleanup, overflow exits, choice, insertion, remaining returns and full
pair/pair induction remain. Dynamic regions/destructors, public maximum/cold-table
teardown, wrappers/input policy/resources/G3 and every other planning target
remain open. The full goal stays active.

[Constructed root-score arithmetic and native switch](evidence/memo-evaluator-root-score-scope.md) now
constructs all twelve actual root-score instructions after successful subtotal:
scalar payload copying, subtotal/temporary retirement, fresh total/result storage,
checked addition of the literal one and argument cleanup. The parsed endpoint
`Evaluator.entry_pair_root_score_scope_complete` retains all six actual prefix
boundaries, both owned witnesses, the updated table, native subtotal and exact
root-score result/overflow. `Calling.Prefix.shape` derives activation count and
untouched-root support across actual calls without extra readiness assumptions.
Smaller head/tail `NativeTotal` and independent native success equations remain
explicit; no physical parent success, cache soundness or alias ban is assumed.
The 4,148-job build and six affected Lean suites pass, including eight runtime
cases. All 1,744 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,295 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. Kernel consumers derive
root-score `Some 1` with table-owned query aliases, and root overflow from a valid
maximum-width subtotal with distinct cached head/tail scores and explicit external
query ownership. Both recursive contracts are discharged by proved empty cases.
Matched-witness construction, concatenated contraction queries and fresh query
loan tracking, recursive witness freshness/owned cleanup, overflow exits, both
contraction calls, choice, insertion, remaining returns and full pair/pair
induction remain. Dynamic regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and every other planning target stay open.
The full goal remains active.

[Constructed subtotal arithmetic and actual result switch](evidence/memo-evaluator-subtotal-scope.md) now
constructs all fifteen score-prefix instructions after native head/tail success:
owned tail extraction, both scalar score copies, actual checked addition and
argument retirement. `Evaluator.entry_pair_score_scope_complete` connects parsed
entry and all five common/miss/head/tail/score prefix boundaries at shared
sufficient bounds, retaining both owned witnesses, the updated table and the
actual subtotal discriminant. Native-width result/overflow and complete cost
are identified by source reflection. Smaller head/tail `NativeTotal` contracts
remain explicit. `original_checked_add_operands_complete` also supports the
literal operand needed by the subsequent root-score addition.
The 4,140-job build and six affected Lean suites pass, including eight runtime
cases. All 1,730 audited endpoints use only the accepted axiom baseline; eight
statement seeds resolve 1,314 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. Two kernel consumers
use proved empty-input contracts with table-owned query aliases: a head miss/
tail hit yielding subtotal zero, and warm maximum-width scores selecting overflow
without cache soundness or a successful physical parent premise.
Root-score arithmetic, recursive witness freshness/owned cleanup, overflow exits,
contractions, choice, insertion, remaining parent returns and full pair/pair
induction remain open. Dynamic regions/destructors, public maximum/cold-table
teardown, wrappers/input policy/resources/G3 and every other planning target
remain. The full goal stays active.

[Complete tail scope and owned-drop support](evidence/memo-evaluator-tail-scope.md) now
constructs all twenty-four tail-prefix instructions through the actual tail-result
switch: argument retirement, native optional/table extraction, moved-output
cleanup and fresh payload storage. `Evaluator.entry_pair_tail_scope_complete`
connects parsed entry and all four actual prefix boundaries at shared sufficient
bounds. The successful-tail path additionally moves its owned witness into 47
through the first six score instructions, retaining the owned head witness.
`OriginalLoanMachine.drop_fresh` constructs nonzero owned drops from explicit
selected-owner freshness, preserving original loan origins; deriving that
freshness for recursive witnesses remains open. No caller alias ban or successful
physical parent premise is added. Full pair/pair induction remains open.
The 4,133-job build, six affected Lean suites (including eight runtime cases),
1,719-endpoint axiom audit, eight elaborated statement seeds (1,302 unique
records, no unknown references), thirteen ordered Rust tests and nine Python
checks pass. A repeated table-owned alias consumer discharges both smaller
contracts using proved empty-input totality and reaches the actual tail switch.
Score arithmetic, recursive witness freshness and owned cleanup, overflow,
contractions, choice, insertion and remaining parent returns are still open,
as are dynamic regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and every other planning target.
The full goal remains active.

[Complete head failure and constructed tail recursion](evidence/memo-evaluator-head-failure-tail-call.md) now
constructs the entire selected head-failure invocation, including routing,
output/temporary cleanup, return, checked closure, complete ownership and stable
exact world/packet/full cost. The successful-head path also reaches the actual
tail recursive call through fourteen instructions, retaining the owned head
embedding, native queries/views and tail output. Both paths use explicit
universal contracts for strictly smaller requests; full pair/pair induction is
open. `Evaluator.head_failure_total` and
`Evaluator.entry_pair_tail_prefix_complete` record these endpoints. A repeated
table-owned alias consumer discharges both smaller contracts with proved empty
base cases and exercises a head miss followed by a tail hit.
The 4,127-job build and six affected Lean suites pass, including all eight
runtime cases. All 1,710 audited endpoints retain only the accepted axiom
baseline; ten statement seeds cover 1,321 unique declarations with no unknown
references. Thirteen ordered Rust tests and nine Python checks pass.
Tail result/argument cleanup, owned-witness destructor loan provenance, score
and contraction/choice/insertion paths, other parent returns and full pair/pair
induction remain. Dynamic regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and all other planning targets stay open.
The full goal remains active.

[Constructed pair/pair head recursion and result scope](evidence/memo-evaluator-head-scope.md) now
constructs parsed entry, common lookup, miss setup and all twenty-six actual
head-prefix instructions, including the recursive call, result/table extraction,
temporary retirement and head-result inspection. The explicit induction premise
is universal totality for the strictly smaller head query pair; no global
pair/pair instance or parent return is assumed. `Rust.SourceEval.Evaluator.entry_pair_head_scope_complete` retains native queries/Box-field views, fresh
payload/return storage, complete ownership, original loan origins and stable
prefix worlds at every larger helper bound pair. A repeated table-owned alias
consumer discharges the smaller contract using proved empty-input totality.
The 4,112-job build and six affected Lean suites pass, including all eight
recursive runtime cases. All 1,686 audited endpoints retain only the accepted
axiom baseline; ten statement seeds cover 1,322 unique declarations with no
unknown references. Thirteen ordered Rust tests and nine Python checks pass.
Selected head failure/tail recursion, overflow/contraction/choice/insertion,
parent return/closure and full pair/pair induction remain. Dynamic regions/
destructors, public maximum/cold-table teardown, wrappers/input policy/resources/
G3 and every other planning obligation remain open. The full goal stays active.

[Complete actual evaluator empty-query miss execution](evidence/memo-evaluator-empty-totality.md) now
constructs parsed entry, lookup, all eleven miss-setup and 47 empty-branch
actions, native insertion, both empty routes, return and checked closure.
`Rust.SourceEval.Evaluator.empty_miss_total` derives the empty witness/inserted
table, readable output, complete ownership/coverage and one exact final world,
packet and full cost at every larger fuel/readback pair. Original query-tuple
loans and temporary embedding views permit legal query/table/caller aliases;
no successful physical run, cache soundness or global owner/loan disjointness
is assumed. The 4,093-job build and six affected Lean suites pass, including
eight recursive runtime cases and two whole-invocation table-alias consumers.
Thirteen ordered Rust tests and nine Python frontend regressions pass.
All 1,652 audited endpoints retain only the accepted axiom baseline; ten
statement seeds cover 1,314 unique declarations with no unknown references.
Pair/pair recursion/overflow/failure, dynamic regions/destructors, public
maximum/cold-table teardown, wrappers/input policy/resources/G3 and every other
planning obligation remain open. The full goal remains active.

[Constructed evaluator miss setup and native word routing](evidence/memo-evaluator-miss-setup.md) now
constructs all eleven miss-setup instructions after parsed native entry and the
common lookup prefix. Exact shared-pointer copies assemble tuple 13, whose loans
are proved to originate below the pre-entry memory bound; all temporary roots
retire. `Rust.SourceEval.Evaluator.entry_miss_setup_complete` retains complete
ownership, native inputs/tuple, fresh empty return storage and stable prefix
worlds at every larger helper fuel/readback pair. Both actual word inspections
and native routing check. A table-owned repeated-query-alias consumer passes.
The 4,072-job build and six affected Lean suites pass, including eight recursive
runtime cases. All 1,599 audited endpoints use only the accepted axiom baseline;
ten statement seeds cover 1,109 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python frontend regressions pass. Empty-
branch insertion/return, pair/pair recursion/overflow/failure, public maximum,
dynamic regions/destructors and the remaining planning targets stay open.
The full goal remains active.

[Complete actual evaluator cache-hit execution](evidence/memo-evaluator-cache-hit-totality.md) now
constructs parsed entry, lookup, all twenty hit actions, return and checked closure
from independent native readable packets and complete ownership. Query-loan
origins derive selected fresh stack-root permissions while permitting queries
inside table-owned Boxes. `Rust.SourceEval.Evaluator.cache_hit_total` returns the
cached result and unchanged native table, complete output/caller/external owner
resources, and one exact final world/packet/full cost at every larger fuel/readback
pair. No cache soundness or successful physical run is assumed. The 4,061-job
build and five affected suites pass, including eight recursive runtime cases and
a whole-invocation table-alias consumer. All 1,559 audited endpoints use only the
accepted axiom baseline; ten statement seeds cover 1,326 unique declarations with
zero unknown references. Thirteen ordered Rust tests and nine Python frontend
checks pass. Empty-query misses,
pair/pair recursion/overflow/failure, public maximum, dynamic regions/destructors
and the remaining planning targets stay open; the full goal remains active.

[Complete common evaluator prefix and native lookup routing](evidence/memo-evaluator-common-prefix.md) now
constructs actual parsed entry and all fourteen common instructions through
lookup-temporary retirement, followed by actual native hit/miss inspection.
The checked scope retains the independent lookup answer, ended table view 6,
fresh empty return storage, original caller bytes and complete ownership/coverage.
Shared query/table/caller aliases remain allowed. Branch bodies, recursive
budget composition, return/closure, public maximum, dynamic regions/destructors
and the other planning targets remain open. The 4,042-job build and five affected
suites pass, including all eight recursive runtime cases and new warm-alias/cold-
caller consumers. The 1,480-endpoint audit includes 15 new theorems with only the
accepted axiom baseline. Ten selected statement seeds cover 1,085 unique
declarations with no unknown references. The full goal remains active.

[Constructed native evaluator entry and lookup prefix](evidence/memo-evaluator-native-prefix.md) now derives
all physical permissions for the actual parsed 113-local entry and first eleven
instructions through lookup/result storage. Native graph structure and preserved
old caller reads permit shared query/table aliases, including queries inside a
table-owned Box. Fixed sufficient fuel/readback thresholds retain one final
machine with protected caller bytes and complete ownership/coverage. Retirement
of lookup temporaries, every branch/recursive return/closure, public maximum,
dynamic regions/destructors and the other planning targets remain open.
The 4,035-job build and five affected suites pass, including all eight recursive
runtime cases. The 1,465-endpoint audit includes 64 new theorems with only the
accepted axiom baseline. Ten selected statement seeds cover 1,097 unique
declarations with no unknown references. The full goal is active.

[Constructed recursive helper and choice calls](evidence/memo-evaluator-call-totality.md) now compose actual
argument extraction, callee execution and checked result storage from independent
local source steps, types, ownership and selected loan permissions. Choice runs
through recursive dispatch with one fuel; whole helper calls have fixed joint
sufficient fuel/readback bounds and stable final state/full cost. Shared helper
aliases remain permitted; choice constrains only transferred owners versus actual
post-argument suspended loans. Evaluator/maximum all-path scope/loan discharge,
recursive budget composition, dynamic regions/destructors and the other planning
targets remain open. The 4,022-job build and five affected suites pass, including
all eight recursive runtime cases. The 1,401-endpoint audit includes 18 new
theorems with only the accepted axiom baseline. Eight selected statement seeds
cover 1,125 unique declarations with no unknown references. The full goal is active.

[Stable recursive fuel and readback budgets](evidence/memo-evaluator-stable-budgets.md) now preserve every
completed actual run's exact world/packet/full cost at all larger bounds.
Independently typed helper inputs give fixed joint sufficient thresholds, a stable
output and complete owner resources. Interpreted physical success and all other
planning obligations remain open. The 3,996-job build and two affected consumers
pass; 19 new theorems bring the accepted-baseline audit to 1,289 endpoints.
Eight selected statement seeds cover 1,070 unique declarations with no unknown
references. Broader regression evidence is inherited from the preceding commits.

[Typed helper totality and sufficient budgets](evidence/memo-evaluator-helper-totality.md) now derives actual
success for all eight helpers/intrinsics from independently typed readable input
packets. Sufficient fuel and ghost readback thresholds require no supplied native
height, expected output or successful run. Larger readback budgets preserve the
identical world/packet/full cost; source agreement and complete output/caller/
external ownership compose. Interpreted choice/evaluator/maximum physical success,
dynamic regions/destructors, public teardown/wrappers/resources/G3 and the other
planning targets remain open. The full goal is active.
The 3,992-job build and all four affected helper/typed/recursive/runtime suites
pass, including five new warm-cache/overflow/failure paths with complete owner
and cleanup checks. The 1,270-endpoint audit includes 27 new theorems with only the accepted axiom baseline;
eight selected statement seeds cover 828 unique declarations with no unknown
references. Full-suite/native-WP/Python/Rust evidence is inherited, not rerun here.

[Global ownership for recursive source execution](evidence/memo-evaluator-global-owners.md)
now composes exact helper input/fresh/output ledgers, complete actual calls,
selected calling control, parsed entry/return cleanup and recursive dispatch.
The native evaluator retains its existing result/table and full-cost refinement
plus complete output/caller/external owner resources and live-Box coverage.
Independent actual types derive call profiles; shared read aliases remain allowed.
Concrete success and initial ownership resources remain explicit. Adequate
budgets/every physical check, dynamic regions/destructor interpretation and the
other public core/wrapper/resource/G3/planning targets remain; no full-goal closure.
The 3,988-job build, all 47 Lean suites, native WP and nine Python tests pass.
The 1,243-endpoint audit includes 57 new theorems and only the accepted axiom
baseline. Ten selected statement seeds cover 1,388 unique declarations with
zero unknown references. Nonempty evaluator/maximum runtime checks now include
complete owner uniqueness, live Box classification and coverage.

[Owner ledgers through entry, storage and non-call destruction](evidence/memo-evaluator-owner-lifecycle.md)
now transfer the complete argument packet into actual parameter locals, retain
exact owners across real storage-live/dead operations, and compose through every
successful finite sequence of existing non-call actions. The complete removed
list is duplicate-free, its length equals the source Box destructor count, and it
consists of initially live Boxes that are dead in the final symbolic world. Actual caller/
external owners retain complete uniqueness/class/liveness and live-Box coverage;
shared reads may alias. Callee output transfer, selected calling control/full
recursive ownership, budgets/every physical check and dynamic regions/destructors
remain, followed by the other planning targets. The full goal stays open.
The 3,977-job build and four affected consumers pass. The 1,186-endpoint audit
includes twenty new theorems and only the accepted axiom baseline. Eight selected
statement seeds cover 335 unique declarations with no unknown references. CI now
lists 47 suites; the full preceding 46-suite/native-WP/nine-Python regression
remains baseline evidence from `40bcb57`.

[Exact owner transfer through packets, assignment, drops and return cleanup](evidence/memo-evaluator-owner-packets.md)
now preserves complete actual owner occurrences through nested moves, operand/
RHS packets, one-pass guarded assignment, exact Box retirement, the actual callee
input boundary, return extraction and successful stack closure. Initial uniqueness, Box class,
liveness and full live-Box coverage remain explicit; shared reference reads may
alias. No supplied post-RHS frame/guard list is needed for assignment. Concrete
callee output/fresh/retired transfer, whole recursive ownership, budgets/every
physical check and dynamic regions/destructors remain, then public core/wrappers/
resources/G3 and the other planning targets. W06-C3 and the full goal stay open.
The 3,974-job build, all 46 Lean suites, native WP and nine Python tests pass.
The 1,166-endpoint audit includes 51 new theorems and retains only `propext`,
`Classical.choice` and `Quot.sound`. Shared statement inspection covers 333
unique declarations from eight seeds with no unknown references.

[Derived typed call domains and recursive source refinement](evidence/memo-evaluator-typed-calls.md)
now derive selected call input conditions from the independently checked actual
source types. Successful concrete helper execution reflects to the old source
at the same fuel/value/cost, and typed inputs supply the scalar-width boundary.
The stronger recursive evaluator endpoint no longer assumes `Recursive.Ready`;
arbitrary native queries/warm tables retain the complete native result/table,
`Evaluation` cost relation, readable output and protected caller bytes.
Concrete success remains explicit. Adequate budgets, every physical check,
global exclusive transfer/dynamic regions/destructors and the remaining public
core/wrappers/resources/G3 stay open. W06-C3 and the full planning goal remain.
The 3,966-job build, all 45 Lean suites, native WP and nine Python tests pass.
The 1,115-endpoint axiom audit retains only `propext`, `Classical.choice` and
`Quot.sound`. Shared statement inspection covers 1,139 unique declarations from
eight selected seeds with no unknown references.


[Calling control, parsed entry and checked return cleanup](evidence/memo-evaluator-calling-entry.md)
now compose the existing helper call step with the shared switch/return engine. Callees receive
the actual post-argument activation and suspended stack. Selected-path input
readiness, source outcomes/full costs and caller validity are checked; cleanup
rejects remaining owners or escaping output/caller references and retires all
remaining bounded stack roots. Actual parsed choice retains its native tie rule
and complete cost through entry and cleanup. Recursive program dispatch, whole-
run protected caller preservation, universal readiness/physical success and
global exclusive ownership/dynamic region/destructor composition remain open,
then public maximum/wrappers/resources/G3. W06-C3 and the full goal stay open.
The 3,951-job build, all 41 Lean suites, native WP, nine Python tests and
1,030-endpoint axiom audit pass. Shared statement inspection covers 1,124 unique
declarations from five seeds with no unknown references.

[Concrete helper calls in the mixed world](evidence/memo-evaluator-helper-calls.md)
now execute six existing ordinary helpers and both intrinsics over actual stack/
Box prefixes. Output metadata comes from concrete readback; one-pass caller
argument moves, retained contexts and result storage preserve source costs and
caller resources. Native argument/fuel readiness discharges the local callee
contracts. Wiring this step into control/recursive entry, choice/evaluator/
maximum service, all-path readiness/check success and global ownership/storage/
region/destructor closure remain required, then public core/wrappers/resources/
G3. W06-C3 and the full planning goal stay open.
The 3,946-job build, all 40 Lean suites, native WP, nine Python tests and
1,007-endpoint axiom audit pass. Shared statement inspection covers 914 unique
declarations with no unknown references.

[Addressed switches, return packets and actual choice](evidence/memo-evaluator-addressed-control.md)
now read concrete retained tags after partial moves, execute boolean routing and
early returns through the shared source-control engine, and preserve exact
source results/costs and active/caller/packet validity. The actual choice bridge
reuses the checked source body and native tie rule. Ordinary/intrinsic calls,
universal physical check success, global exclusive transfer and callee storage/
region/destructor closure remain required, then public core/wrappers/resources/
G3. W06-C3 and the full planning goal stay open.
The 3,937-job build, all 39 Lean suites, native WP, nine Python tests and
962-endpoint axiom audit pass. Shared statement inspection covers 920 unique
declarations with no unknown references.

[Initial activations and executable storage/drop actions](evidence/memo-evaluator-storage-actions.md)
now construct argument frames from parsed local counts, derive storage/drop
contexts and compose successful non-call sequences with actual source execution
and unchanged complete costs. Drop protects stack roots as well as unique,
classified Box owners; reopening a local gets fresh storage. Calls, switches/
returns, actual branch check success, global owner/spatial and dynamic region/
destructor composition remain required, then public core/wrappers/resources/G3.
W06-C3 and the full planning goal stay open.
The 3,933-job build, all 38 Lean suites, native WP, nine Python tests and
949-endpoint axiom audit pass. Shared statement inspection covers 456 unique
declarations with no unknown references.

[Computed frame resources and assignment](evidence/memo-evaluator-derived-inventories.md)
now derive complete finite read/owner/loan inventories from actual roots/masks,
extract remaining contexts and preserve suspended caller inventories. Assignment
computes its own guards and post-RHS context while executing the RHS once, with
actual source/cost/frame correspondence. Initial/control/callee, exclusive owner/
spatial and dynamic region/destructor traces remain required, then public core/
wrappers/resources/G3. W06-C3 and the full planning goal stay open.
The 3,929-job build, all 37 Lean suites, native WP, nine Python tests and
929-endpoint axiom audit pass. Shared statement inspection covers 313 unique
declarations with no unknown references.

[Executable addressed RHSs and assignment](evidence/memo-evaluator-addressed-rhs.md)
now implement every operand/RHS constructor with actual cells/pointers and
incremental initialization metadata. Forward and reverse simulation preserve
source results/masks and concrete graphs; moves retain partial frames and check
physical root permissions. One-pass guarded assignment computes its RHS graph
and initializes the existing destination at unchanged source cost. Full actual
frame/loan/owner/control/callee and region/destructor traces remain required,
then public core/wrappers/resources/G3. W06-C3 and the full goal stay open.
The 3,925-job build, all 36 Lean suites, native WP, nine Python tests and
888-endpoint axiom audit pass. Shared statement inspection covers 283 unique
declarations with no unknown references.

[Guarded in-place writes and storage lifecycle](evidence/memo-evaluator-frame-writes.md)
now preserve concrete read/owner graphs across unrelated mutations. Actual
scalar assignments update existing stack roots at unchanged costs; storage
markers retain caller resources and reject protected/dead/wrong-class roots.
Storage-dead also handles the actual still-initialized nonowning references,
without losing Box owners. Full RHS/move/context/control/callee traces and
region/destructor composition remain required, then public core/wrappers/
resources/G3. W06-C3 and the full planning goal stay open.
The 3,918-job build, all 35 Lean suites, native WP, nine Python tests and
867-endpoint axiom audit pass. Shared statement inspection covers 245 unique
declarations with no unknown references.

[Addressable local storage and retained reference graphs](evidence/memo-evaluator-local-storage.md)
now give actual source address expressions concrete pointers into initialized
partial locals. Classified stack roots and Box owners are distinct; transitive
shared graphs derive caller read guards. Box creation and guarded destruction
retain the same caller frame and costs. Full addressed execution, initialization/
mutation conflict checking, active/suspended frame traces and dynamic region/
destructor composition remain required, then public core/wrappers/resources/G3.
W06-C3 and the full planning goal stay open.
The 3,914-job build, all 34 Lean suites, native WP, nine Python tests and
830-endpoint axiom audit pass. Shared statement inspection covers 278 unique
declarations with no unknown references.

**Addressed partial primitives:** [moves, Boxes and logical destruction](evidence/memo-evaluator-addressed-partials.md)
now reuse existing heap cells/full representations/footprints with initialized
source masks and complete owner lists. Concrete identities partition on field
moves, Box shells remain, fresh allocation preserves frames, and partial
traversal selects exact owners/work. Actual source move/Box/drop costs compose.
Reuse these primitives and the completed type/region/native/helper certificates.
Next complete addressed operation/control/callee simulation, addressable local
storage, active/suspended caller frames and real loan-derived guarded addresses,
then destructor-instance interpretation and public core/wrappers/resources/G3.
Raw stored-data readback is not liveness; owner separation does not protect
shared targets by itself. Full W06-C3 remains open.
The 3,910-job build, all 33 Lean suites, native WP, nine Python tests and
780-endpoint axiom audit pass. Shared statement inspection covers 275 unique
declarations with no unknown references.


**Recursive evaluator types and regions:** [actual recursive preservation and binding](evidence/memo-evaluator-recursive-typing.md)
now discharge every typed callee contract, including Box/checked add, and retain
scoped source signatures/locals with exhaustive region-use/call-arity checks for
all nine bodies. Actual JSON/native totality composes with independently typed
outputs and unchanged full costs. Do not repeat static/recursive snapshot typing,
region binding, helper proofs or evaluator functional correspondence. Next
addressed partial moves/owners/storage/spatial/local loans/regions/destruction,
including destructor-instance semantics, then public maximum/wrappers/input
policy/global resources/G3. Snapshot preservation and well-bound regions do not
supply dynamic local-loan safety; full W06-C3 remains open.
The 3,904-job build, all 32 Lean suites, native WP, nine Python tests and
734-endpoint axiom audit pass. Shared statement inspection covers 1,046 unique
declaration records with no unknown references.


**Evaluator source types:** [actual declarations and partial-local preservation](evidence/memo-evaluator-source-typing.md)
now check all nine source profiles, both actual Option layouts, complete nested
annotations and static constraints. Partial reads/owned field moves and expanded
operands/expressions/actions preserve independent declared types. Next shared
control induction, typed initial locals and recursive Box/checked-add/ordinary
callee discharge. Then addressed owners/storage/spatial/local loans/regions/live
destruction, public maximum/wrappers/input policy/global resources/G3. Do not
repeat source extraction, the new static certificate, partial-type primitives
or the completed functional evaluator/native correspondence. No full C3 closure.
The 3,898-job build, all 30 Lean suites, native WP, nine Python tests and
706-endpoint axiom audit pass. Shared statement inspection covers 752 unique
declaration records.


**Universal evaluator:** [actual source/native totality](evidence/memo-evaluator-native-totality.md)
now discharges all recursive success/failure/overflow cases for every finite
native query and warm table, retaining exact tables, full callee/local costs and
fuel-independent completed work. The independent consistency/memo refinement is
reused under its original sound-cache/width assumptions. Do not repeat evaluator
functional correspondence, primitive extraction or the seven helper proofs.
Next actual whole-profile types/regions/owners/storage/local borrows/addressed
live destruction, then public maximum, wrappers/input policy/global resources/G3.
No physical allocator or complete W06-C3 claim follows.
The 3,890-job build, all 29 Lean suites, native WP, nine Python tests and
675-endpoint axiom audit pass. Shared statement inspection covers 837 unique
declaration records.


**Evaluator base paths:** [the complete body/base increment](evidence/memo-evaluator-base-paths.md)
now kernel-checks all 113-local control and proves actual-program/native
cache-hit and either-empty-query totality, with arbitrary warm storage and
scores, exact output tables and complete source/helper/drop/call currencies.
Do not re-extract the body or reprove the seven helpers. Next recursive head/
tail and contracted-query cases, both checked-add failures and final choice/
insertion; compose exact native/overflow/table/cost behavior plus whole-profile
types/regions/owners/storage/local borrows/live destruction before core/wrappers/G3.
The 3,881-job build, all 28 Lean suites, native WP, nine Python tests and
645-endpoint axiom audit pass. Shared statement inspection covers 838 unique
declaration records.


**Owned choice:** [actual source/native choice](evidence/memo-owned-choice.md)
now consumes a kernel body certificate, retains the first on equal scores and
charges the losing witness's exact logical destructor work. The native API has
no word/score consistency premise. Reuse it with the preceding six helpers;
whole-evaluator typing/regions/owners/storage/local borrows/live destruction,
functional/error/table/resource correspondence and public core/wrappers/G3
remain required. No physical deallocation or full W06-C3 claim follows.
The 3,877-job build, all 27 Lean suites, native WP, nine Python tests and
634-endpoint axiom audit pass. Shared statement inspection covers 706 records.


**Expanded helper reuse:** [the checked bridge](evidence/memo-evaluator-helper-bridge.md)
identifies all six actual helper bodies with their earlier profiles and transfers
successful runs at identical nesting fuel/full work, with zero new destruction
and solver-call currency. Universal native contracts and completed addressed
owner/storage/spatial/typing/loan/region results compose with the expanded source
program. Do not reprove helper algorithms or their safety traces. Next evaluator
whole-program typing/regions/owners/storage/local borrows/destruction and universal
functional/overflow/table/resource correspondence, then public core/wrappers/G3.
The numeric-width premise is necessary and holds for every native input.
The 3,873-job build, 26 Lean suites, native WP, nine Python tests and
624-endpoint axiom audit pass. Shared statement inspection covers 1,239 records.


**Actual evaluator source follow-up:** [complete profile execution](evidence/memo-evaluator-source-profile.md)
now retains and kernel-reads all nine actual bodies/signatures/bounds/coverage,
including 113 evaluator locals and the public entry point. Partial moves,
scalars/checked add, live drops, tags and metadata use shared control/frontend
semantics; complete work is retained. Actual-program guards cover empty/nonempty
and overflow/table behavior. Next bridge helper refinements and compose whole
program typing/regions/owner/storage/addressed safety and universal functional/
resource correspondence, then separate wrappers/G3. Full W06-C3 stays open.
The 3,865-job build, 25 suites, native WP, nine Python tests, thirteen Rust
tests, full regeneration check and 592-endpoint axiom audit pass.

**Actual evaluator follow-up:** [partial-local foundations](evidence/memo-evaluator-partial-locals.md)
now support projected moves, preserved siblings/Box shells, exact transfer of
declared destructor work, unrelated locals and whole-local destruction. Pinned
inspection confirms these are actual evaluator/wrapper needs. Next consume
these primitives in checked normalization/execution, with scalar/checked-add,
metadata/unreachable control, local addressed borrows and full safety/cost
composition, then core/wrappers. This is not an evaluator source certificate;
W06-C3 remains open. The 3,858-job build, 24 suites, native WP, nine Python tests and
572-endpoint axiom audit pass.

**Memo loan/region follow-up:** [typed shared loans and source-region interpretation](evidence/memo-loan-regions.md)
now compose actual helper runs, parsed scoped declarations and retained-world
lifetime witnesses. Kernel route/type/body/scope checks and fuel induction cover
recursive contracts. Ordinary outputs are reference-free; Box preserves payload
loans. Insertion retains owned-table transfer and aliased key/witness loans.
Native endpoints retain storage/guard/spatial/returned-owner/full-cost results
and all typed caller loans. Next actual evaluator arithmetic, owned-local borrows,
destruction/errors, public core and wrappers. Full W06-C3 remains open; the
scoped model is explicit. The 3,855-job build, 23 suites, native WP, nine Python tests and
552-endpoint axiom audit pass.

**Memo storage follow-up:** [normal allocation/initialization traces](evidence/memo-stack-initialization.md)
now retain distinct live/dead markers and exact actual local declaration counts.
Generic checker soundness and fuel induction cover initialized reads, allocated
writes, moved-empty slots, normal frame closure and all recursive calls. Native
endpoints retain prior source/heap, typing, guard/spatial, returned-owner and
full-cost guarantees. Next dynamic loans/lifetime interpretation for these
helpers, then actual evaluator/core and wrappers. Logical storage alone does
not prove loan validity; W06-C3 remains open. The 3,850-job build, 21 suites, native WP, nine Python tests and
531-endpoint axiom audit pass.

**Memo guard/spatial follow-up:** [recursive intermediate owner traces](evidence/memo-spatial-ownership.md)
now cover clobbers, moved drops, return cleanup and complete owner lists across
locals, temporaries and suspended callers. Insertion uses its owned-table
profile; initial enumeration retains that owner. Kernel checks and fuel induction
discharge actual recursive contracts. Native endpoints retain prior source/heap/
readback/cost/returned-owner guarantees. Next normal storage/initialization and
dynamic loans/lifetimes, then actual evaluator/core and wrappers. `.scope`
owner guards are not storage liveness; W06-C3 remains open.

**Memo typing/scope follow-up:** [actual source certificates and preservation](evidence/memo-source-typing.md)
now check declaration layouts, nested annotations, argument/return prefixes,
static bodies and free/body region scope. Recursive operational type preservation
and ordinary output closure compile for the new helper set. Insertion retains
its owned input and three lifetimes for four value arguments. Shared checkers
and proofs accept explicit callee maps. Next guarded local/storage/spatial and
dynamic loan/lifetime traces, then actual evaluator/core and wrappers. Scope
is not dynamic liveness; W06-C3 remains open.

**Addressed memo follow-up:** [actual heap layouts and owner transfer](evidence/memo-heap-ownership.md)
now realize the certified memo primitives with full source costs and exact
allocation growth. Concatenation owns its fresh output; insertion preserves
the old table cell under its new tail Box. Its complete occurrence ledger adds
all new cells to the old list, preserving multiplicity and external owner
frames. Native typed readback and input inhabitation compile. Next independent
source/static/region checking and intermediate type/guard/storage/spatial/loan
traces for the new helper set, then actual evaluator/core and wrappers. Returned
ownership is not an intermediate trace proof; W06-C3 remains open.

**Memo primitive follow-up:** [actual insertion/concatenation](evidence/memo-source-primitives.md)
now have retained source, kernel normalization, successful native runs,
independent append/prepend and translated-Rust agreement, with explicit copy/
Box events. Existing control semantics/parser are polymorphic in callee targets.
Next extend addressed typing/ownership/storage/loans/regions to those bodies,
then actual evaluator arithmetic, owned-local borrows, losing-candidate drops,
overflow/table returns and one public core. Wrappers, input/error policy and G3
adversaries remain required. Source control alone does not imply heap safety;
W06-C3 stays open.

**Region follow-up:** [scoped lookup erasure](evidence/lookup-region-erasure.md)
checks actual source binders/uses/call arities and retains regional local types.
An independent shared-value interpretation is equivalent to typed loans under
an explicit immutable retained-world lifetime. Both source snapshots pass kernel
certificates; native lookup composes regional recursive traces with all prior
safety/readback/cost results. Next compose actual insertion, concatenation, memo
evaluation/core and wrappers, then input/error policy and G3 adversaries. Keep
the declared source/primitive and compiler/runtime boundaries explicit. D12's
initial source-operation endpoint does not require a whole-compiler proof.
Full W06-C3 remains open; do not duplicate the scoped lookup pilot.

**Shared-loan follow-up:** [typed retained-heap loans](evidence/lookup-shared-loans.md)
now prove actual shared-read validity through source-certified reborrows,
locals/temporaries and recursive calls. Ordinary results are borrow-free;
native lookup composes success, all prior safety and exact source currencies.
Both real programs pass kernel certificates without changing their input domain.
Next address source region/interpretation adequacy, then insertion,
concatenation, memo evaluation/core and wrappers. Dynamic loans are not a full
Rust borrow checker; W06-C3 remains open. Do not duplicate the completed loan
origin/preservation or result-closure proofs.

**Storage follow-up:** [normal local-storage lifetimes](evidence/lookup-stack-storage.md)
now distinguish allocation/deallocation, require initialized reads and allocated
writes, and produce recursive exact-cost traces on completed normal paths.
Both retained bodies and exact local counts pass kernel certificates. Next
address shared-borrow lifetime/source adequacy, then insertion, concatenation,
memo evaluation/core and wrappers. Physical stack addresses and borrow regions
are not modeled; W06-C3 remains open. Do not duplicate completed normal local
storage/initialization checking.

**Spatial follow-up:** [framed intermediate ownership](evidence/lookup-spatial-ownership.md)
now proves duplicate-free complete owned occurrences across live locals,
temporaries and all suspended caller frames for completed normal executions.
Recursive contracts are discharged for both real programs; actual traces retain
complete cost and native-input lookup has composed success/readback/ownership.
Next address stack storage/liveness, borrow/lifetime and official source
adequacy, then memo insertion/concatenation/evaluation and wrappers. W06-C3
remains open; do not duplicate completed intermediate separation.

**Operational typing follow-up:** [successful-run preservation](evidence/lookup-type-preservation.md)
now derives actual primitive/local/result types from the checked constraints.
Recursive call contracts, argument prefixes and generic Box are discharged for
both programs; source composition preserves complete cost. Next establish
intermediate spatial ownership, stack/borrow and official source adequacy.
Preservation is not initialization/progress or ownership uniqueness. W06-C3
remains open; do not duplicate the completed operational typing work.

**Source-type follow-up:** [lifetime-erased type certificates](evidence/lookup-source-typing.md)
now kernel-check actual retained field declarations against independent
`Heap.Shape`, nested annotations, signatures and all ordinary helper bodies'
static constraints in both programs. Next prove operational type preservation
from those constraints and intermediate spatial ownership, then stack/borrow
and official source adequacy. Lifetime regions are erased, and W06-C3 remains
open; do not repeat the completed declaration/annotation work.

**Local-frame follow-up:** [checked frame safety](evidence/lookup-frame-safety.md)
now validates moves, no-owned clobbers, empty moved drops, callee ownership
profiles and return cleanup for every completed normal run, with recursive
callee contracts discharged. Both original/mutant bodies pass and retained
source composition preserves full cost. Spatial ownership, stack/lifetime and
checked typed source adequacy remain open; this does not close W06-C3.

**Returned-ownership follow-up:** [exclusive returned regions](evidence/lookup-return-ownership.md)
now follow from exact generated copy/result-copy/lookup layout proofs. The
complete ownership-occurrence list is duplicate-free, covers every new Box,
has length equal to the allocation counter, and excludes old input cells.
Next prove intermediate frame/reset/move/destruction safety and checked source
typing/adequacy; returned reachability alone does not discharge these.

**Heap follow-up:** [addressed memory realization](evidence/lookup-heap-realization.md)
proves primitive and complete-call simulation, typed first-hit readback, exact
costs and fresh Box-cell growth for the immutable fragment. It constructs input
layouts and allows shared aliases. Next prove unique ownership/frame safety,
owned resets/destruction, JSON field typing and official source adequacy before
extending to memo insertion/evaluation and wrappers. This does not close W06-C3.

**Executed partial delivery:** [kernel-checked source-control certificates](evidence/lookup-source-certificates.md)
now validate both retained lookup JSON extractions against their normalized
programs and preserve complete outcomes/costs at every fuel. The real extra-work
mutant fails the original certificate and comparison allowance. This closes the
external Python control-reifier trust gap for those snapshots in the declared
primitive model. Typed heap/reference/move/Box adequacy, actual memo core and
wrappers remain required; W06-C3 and SRC-01 are not complete.

The [G1 decision](evidence/g1-backend-decision.md#w04w05-boundary-and-named-w06-c3-obligations)
retains a named W06-C3 package: checkable reification/source semantics, typed
heap/shared-reference/move/Box simulation, then the actual memo evaluator/core
and separate wrappers. Native C2 is the selected contract interface, not a
replacement for these adequacy obligations.

**Depends on:** W02/W03; starts before W05 is complete.

**Own:** SRC-01/MEM-04 and narrowly scoped source-generation/interpretation support, coordinated with existing Aeneas workflow.

**Task:** prove the selected event interpretation covers actual source control flow and primitives. Preserve existing functional specifications. Establish erasure separately from cost adequacy. Extend lookup/loop to the memo core, then one explicitly named wrapper.

**Deliver:** reproducible generation, source hashes, correspondence theorem, exact operation bound and explicit unsupported features. Include an extra-work mutation that forces a new resource obligation.

**Acceptance:** a reviewer can identify the exact C2/C3 boundary. A value-only twin proof is reported as incomplete for this assignment, even if it is independently useful.

## W07. Batch/repair abstraction

**Depends on:** stable SUB/WORK interfaces and real implementation inventory.

**Own:** BATCH-01/02 and an independent prepared-state client. Own AMO-03 only after demonstrating its necessity.

**Task:** identify baseline sharing, job occurrences, affected-job partition, workspace lifecycle and local repair contracts. Prove generic event composition and weighted charging. Exercise it with one matching family and one independent shared-work consumer.

**Deliver:** mathematical statement, backend realization, client proofs and a copy-per-job counterexample.

**Acceptance:** no double-spent baseline potential, no omitted restore/copy cost, no specialized matching assumption in the general theorem. Keep the result local if the claimed generality is not exercised.

## W08. Matching and schedule application audit

**Own:** local MATCH/SCHED/APP obligations; do not redesign the generic core during this assignment without an explicit interface proposal.

**Task:** map existing matching correctness endpoints to actual functions; determine the search/data-structure variant; prove or identify rectangular and repair cost obligations. For 2018, identify the implemented regime choice and oriented-table schedule. Preserve signed/forbidden/nonempty semantics.

**Deliver:** source-algorithm correspondence, matcher contracts, schedule producer/rank map, size/degree sum and remaining local proof census.

**Acceptance:** distinguish a paper existence result from the current implementation's result. Missing source optimization or correctness prerequisite remains a named blocker.

## W09. Space and asymptotic adapters

**Depends on:** stable execution/size interfaces and a chosen schedule.

**Own:** SPACE/ASY modules and rolling-row DP client.

**Task:** reuse existing occupancy-profile algebra, establish representation/lifetime link, and compose scratch/new-output peaks. Export uniform pointwise envelopes and Mathlib filter corollaries with explicit admissible domain. Check fixed-width/asymptotic distinctions.

**Acceptance:** no allocation-volume/peak-space confusion; no empty filter; no hidden fixed degree; a new consumer can use the public envelope without unfolding the implementation.

## W10. Independent review and upstream extraction

**Depends on:** two successful generic clients and source pilot.

**Own:** statement/API review report and candidate upstream package/proposal.

**Task:** independently read assumptions and reproduce a small client, rerun the related-work search, coordinate scope with maintainers and extract the smallest complete theory. Follow the actual upstream statement-file format and compile it.

**Deliver:** source/declaration census, reviewed complete roadmap, reproducible examples, precise limitations and placement recommendation.

**Acceptance:** substantial reusable proof content is demonstrated; supporting elementary lemmas are not presented as the main novelty; no experimental alternatives or local campaign backlog remain in the final timeless roadmap.
