# Common-subtree verification planning

For the latest stopping point and new-machine commands, read
[RESUME.md](RESUME.md).

**Current priority (2026-11-19): ship a usable, fast 0.3.0 release.** The user
selected 0.3.0 and explicitly deferred further proof/performance research.
The unordered algorithms already have Python and Rust endpoints. Focus on
documentation, installed API usability, distribution/CI validation and honest
verification scope. See [the release plan](release_0_3_0.md). The historical
formalization and optimization backlog below stays available for later budgets;
its remaining proof obligations are not ordinary package-release gates.

This folder contains the intended destination, proof obligations, implementation
work and concrete status for the Lozano-Valiente and Droschinsky formalization
program. Read these in order:

1. **[Verified common-subtree research program](verified_common_subtree_research_program.md)**:
   overall goals, decisions, reusable foundations, Rust/Aeneas architecture,
   implementation inventory, branch/provenance policy and definition of done.
2. **[Lozano-Valiente (2004): verified Rust and Lean](lozano_valiente_2004_verified_rust_lean.md)**:
   ordered rooted trees, contractions, Dyck words, decomposition bounds,
   recurrence/optimality proofs, true leaf counts, runtime model, and Rust
   refinement.
3. **[Pinned source statement crosswalk](paper_statement_crosswalk.md)**: exact
   source editions, mathematical corrections and result-by-result status.
4. **[Droschinsky (2016 and 2018): verified Rust and Lean](droschinsky_2016_2018_verified_rust_lean.md)**:
   weighted unordered isomorphism, weighted partial matching, topological
   embeddings with distance penalties, paper-correct scoring, faster
   algorithms and their verification.
5. **[Mathematical presentations and application study](common_subtree_presentation_and_application_paper.md)**:
   rendered standalone talks and the prospective controlled application pilot.

## Active priority: efficient Python APIs with functional correctness

User clarification, 2026-11-18: prioritize efficient ordered embedding and
isomorphism exposed through Python, with Lean proofs of functional correctness.
Exact integer affinities come first. Use exact rational/integer arithmetic in
the mathematical model; floating-point behavior may be justified by engineering
analysis and tests without a Lean IEEE-754 proof. Running-time proofs are not
part of this milestone. Keep the wider research program available as deferred
work. The user chooses each work budget; do not start an unbounded campaign or
assume a fixed tranche budget.

The product acceptance target includes Python exposure of a compiled formally
verified algorithm, with a source-connected Lean theorem proving feasible, optimal
original-input witnesses and the correct score on its stated domain. Retain
the optimized, empirically tested implementation as a separately selectable
Python backend. A verified mode may ship with a documented speed penalty;
competitive performance is a measured optimization target, rather than a reason
to hide a useful verified implementation or remove the faster tested one.
A mathematical recurrence without an implementation connection does not close
the implementation-proof milestone. Python/PyO3 conversion and any external primitive
model must have a named assurance boundary and direct integration tests.
Efficiency is assessed with installed-API benchmarks, without a running-time
theorem.

### Complete exact rational Python mode: 2026-11-18

`impl="verified-lean"` now runs the compiled, formally proved hash-memoized
ordered isomorphism solver for both root policies, with exact `int`/`Fraction`
affinities and a `Fraction` result. It preserves original identities and has
unconditional public optimality/score/order theorems; no correct child scores
or supplied sound cache are public hypotheses. This delivers the requested
full rational matching milestone through direct Lean compilation. Python/
NetworkX conversion and JSON/process transport are tested boundaries.

After optimization, the complete library, native executable, seven Lean
examples and 244 installed Python tests pass. Cached exact scores, cheap hashes
with full equality and reduced conversion work give a median 2.79× paired-case
speedup. The median latency ratio against optimized float Rust is now 4.23×
(1.87--8.56× range) on the original small dyadic workloads, and 2.05×/1.77×
against Cython/Python. Larger rooted paths expose a remaining full-matrix input
cost; uniform parity is not claimed. Keep all backends selectable; `auto` is
unchanged. See [optimization measurements and frontier](../../dev/benchmarks/2026-11-18-rational-optimization.md), the
[delivery/proof/benchmark evidence](../../dev/benchmarks/2026-11-18-verified-rational-ordered.md)
and [user instructions](../source/verified_rational_ordered.rst).

Direct Lean compilation is an additional delivery route alongside the original
Rust-first O01--O04 sequence. O01--O03's full optimized Rust refinement remains
open; it is not claimed by the compiled Lean endpoint. O04's Python delivery and
comparison gates are satisfied for this exact Lean isomorphism mode. Further
sparse affinity/representation optimization, optimized Rust source proofs and
weighted ordered embedding remain separately prioritizable work.

### Python delivery and backend choice

- Expose verified and optimized/tested implementations through the same public
  algorithm interfaces, with explicit selection and documented feature/scoring
  support. Preserve current backend names until an intentional API change;
  existing `verified-rust`, `reference-rust` and `iter-rust` have different scopes.
- An explicitly requested verified backend must enforce its proved input/model
  domain and report unsupported or unavailable modes. It must not silently run
  an unverified solver. The proof/primitive/numeric boundary must be visible.
- Keep the faster unverified implementation available while it remains useful
  and independently tested. Its documentation says empirically validated, not
  formally verified. `auto` may select an applicable optimized backend; it does
  not imply a formal guarantee. No default-selection change is part of this
  planning update.
- O04 must benchmark installed Python calls for both backends and relevant
  reference implementations on the same machine, inputs, scoring and root
  policies. Include conversion, core computation and witness reconstruction;
  report warmed repeated latency/variation, memory where practical, revisions,
  build mode and any speed penalty. Native-only timing is supplementary.
- Require the intended compiled backends in integration/benchmark runs so a
  fallback cannot masquerade as either implementation. Check both against
  independent small-input oracles and validate/rescore original-input witnesses;
  equally optimal tie witnesses need not be identical unless the API promises it.

Python delivery, a clear backend comparison and empirical correctness coverage
are release criteria for each supported mode. A slower verified release closes
that functional delivery milestone while leaving its performance gap explicit.

### Current frontier

| Family | What is already available | Remaining functional correctness frontier |
| --- | --- | --- |
| Ordered isomorphism | Complete exact rational `verified-lean` Python backend with proved memoized algorithm, original witnesses, both root policies and installed-API comparisons; optimized float Rust remains available | Reduce the measured Lean slowdown; separately connect optimized Rust DP, state interning, memoized scores and choices to independent optima |
| Ordered embedding | Fast Python/Rust affinity solver; source-proved unweighted token/indexed/guided solver exposed as `verified-rust` | An efficient source-proved affinity implementation; weighted original-identity embedding mathematics needs its own audit before implementation refinement is estimated tightly |
| Unordered 2016 | Fast public graph solver, independent recurrence/optimum mathematics, source-proved exact matching components | Production graph state/orientation/matching/score refinement and its public witness boundary |
| Unordered 2018 | Fast public path/penalty solver, independent path/skeleton mathematics and recurrences, exhaustive independent checks | Production path/skip/join/root-policy refinement, score composition and public witnesses; larger proof surface than 2016 |

The current fast ordered API extracts affinity values as `f64`, including Python
integers. Integer inputs alone therefore do not give an unrestricted exact
integer guarantee for that backend. `verified-lean` provides a separate exact
rational/integer execution path. A future verified Rust path must choose actual
integer arithmetic (with an explicit
overflow/error contract if bounded), or validate a domain where every represented
integer and intermediate sum is exact. Preserve the existing floating API while
making the assurance distinction visible.

### Budgetable ordered work, recommended order

These are preliminary planning ranges for model tokens and elapsed agent work,
not fixed-price quotes or promised completion times. The recent public-maximum
checkpoint used roughly 175k session-counted tokens, but it reused a mature proof
chain; new extraction/state-model problems can cost much more. Estimates are not
additive when tasks share infrastructure. Re-estimate after O00 and each actual
proof frontier; the user chooses how much of the next task to fund.

| ID | Concrete deliverable / acceptance | Difficulty | Initial token range | Initial elapsed range / confidence |
| --- | --- | --- | --- | --- |
| O00 | Numeric-model/extraction spike: a small Rust score/branching example translated with the pinned tools, exact `ℚ`/`ℤ` Lean model, explicit native arithmetic boundary and no copied solver | Moderate, bounded investigation | 30–90k | 0.5–2 h; medium |
| O01 | Separate a proof-friendly ordered score/choice kernel from Python callbacks and bindings; preserve current behavior, retain original IDs, demonstrate extraction and measure the installed path | Moderate–hard | 100–300k | 1–4 h; low–medium until O00 |
| O02 | Source correctness of fast root-preserving affinity isomorphism: state decomposition/interning, memo invariant, score optimum and reconstruction composed with existing mathematics | Hard; highest-value first algorithm proof | 300k–1M | 3–12 h; low before O01 |
| O03 | General isomorphism: descendant-root search and tie policy composed with the rooted proof; original-index witnesses and errors retained | Hard, but reuses O02 | 200–600k | 2–8 h; low |
| O04 | Exact-integer execution/API contract and installed Python release gate: expose verified and optimized/tested backends explicitly, reject unsupported/overflow cases, require intended compiled paths, validate conversions/witnesses and benchmark both end to end against relevant references | Moderate; some work can accompany O01 | 80–250k | 1–4 h; medium after kernel/arithmetic choices |
| O05 | Weighted ordered embedding: independent affinity/contraction optimum, fast DP/source refinement, witnesses and Python composition, reusing score/state infrastructure where valid | Hard; broader frontier | 500k–2M | 1–4 working days; low, split again after mathematics audit |
| O06 | Floating-point engineering note and targeted rational-oracle regression: exact-integer range, finite-value policy, score-gap/error reasoning, near ties and large magnitudes | Moderate; independent practical win | 40–120k | 0.5–3 h; medium |

O00 is complete: the pinned tools extract a real Rust local score/selection
step using four opaque arithmetic primitives with maintained rational
definitions. Lean proves total local selection, optimum score, invariant
preservation and agreement with the independent rooted recurrence given correct
child scores. Native float extraction is separately rejected as expected;
integer inputs alone demonstrably do not guarantee exact sums. The 4,365-job
library, six Lean examples, existing isomorphism suite and two Rust tests pass.
See the [O00 evidence and reproduction commands](../../proofs/experiments/ordered_score_model/README.md).
O01 remains a future optimized Rust task; production state/dictionary/callback
extraction is still untested, so its estimate remains 100–300k tokens / 1–4 hours
rather than a firm quote. The complete rational Python mode above uses a
different, directly compiled and proved memoized Lean implementation.

O02 gives a useful rooted-mode milestone before O03 closes the general mode.
O04 is required before calling a supported Python mode complete. Preserve the
existing scalar/callback API; do not quietly reinterpret float output as an
unconditional exact-rational theorem. For every funded task, report accepted
endpoints, actual code path, tests/measurements, consumed budget, remaining
obligation and a revised estimate. A discovery task may end with an explicit
blocker/frontier report rather than an invented success claim.

### Numeric model and practical float argument

The existing `AffinityDP.level_correct` and `AffinityDP.anywhere_correct`
instantiate at both `ℚ` and `ℤ` on the pinned Lean project (checked directly).
For any finite collection of rational affinities, multiplication by a common
positive denominator preserves score comparisons, feasibility's positive-weight
test and all maximizing witnesses. Rational arithmetic is a sufficient exact
model here; no analytic real-number machinery is needed.

The [pinned Aeneas source](https://github.com/AeneasVerif/aeneas/blob/5a392f4b80a4d0d05abc240eb2a7fa70622a9a35/src/symbolic/SynthesizeSymbolic.ml#L78)
rejects floats in symbolic expansion. Its [external/opaque model mechanism](https://github.com/AeneasVerif/aeneas/blob/5a392f4b80a4d0d05abc240eb2a7fa70622a9a35/README.md#adding-models-of-rust-definitions-to-the-lean-backend)
provides the route now demonstrated in O00: an opaque score type and four
primitive operations with explicit rational definitions in Lean. This validates
the extracted local step under that ideal model; there is no global switch or
correspondence theorem making arbitrary native `f64` execution exact. Do not
edit generated files or insert new axioms to simulate a proof.

The informal float analysis should bound score aggregation error under stated
finite-value/no-overflow assumptions and explain stability when competing
scores are separated by more than the error budget. Near ties can change the
chosen witness; quantify score degradation where possible. Compare against
independent rational oracles on small, near-tie and large-magnitude cases.
Do not give an unconditional probability of correctness without an input model.
Integer-only inputs through a floating implementation require bounds on all
intermediates for an exactness argument, not just integral final answers.

### Deferred research

Retain the existing paper and complexity plans, completed proofs and benchmark
evidence. Defer new source-cost instrumentation, dynamic region/destructor
interpretation beyond what functional refinement needs, running-time/space and
asymptotic proofs, generic resource frameworks, optimized-paper-bound proofs,
and application/publication studies. Unordered correctness remains a later
product milestone. Its graph-source proofs are hard; 2018 adds path/skeleton
and penalty obligations. Give those tasks a separate estimate after the ordered
kernel/model decisions, rather than promising completion from a reference proof.

The optional fourteen-case addressed resource runtime run was deliberately
cancelled after the priority change (exit 143), with no pass/fail claim. Its
previous thirteen-case evidence and the focused public-maximum correctness/
cleanup check remain recorded. Do not automatically resume that expensive run.
The unfinished destructor-instance checker was saved in local Git stash
`2b35dfa3298eb96ea406805f368c73ca76d525e5`; it is not an accepted proof endpoint
or part of the primary milestone.

## Preserved source-operation research checkpoints

[Universal checked public maximum and table teardown](lean-complexity-campaign/evidence/memo-public-maximum-totality.md)
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

[Cold evaluator ownership provenance](lean-complexity-campaign/evidence/memo-evaluator-cold-provenance.md)
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

[Universal checked evaluator totality and witness provenance](lean-complexity-campaign/evidence/memo-evaluator-universal-fresh.md)
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

[Helper owner provenance and constructive concatenation cleanup](lean-complexity-campaign/evidence/memo-evaluator-owner-provenance.md)
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

[Actual right recursion and complete right-result scope](lean-complexity-campaign/evidence/memo-evaluator-right-scope.md) now
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

[Successful-left payload and actual right-query concatenation](lean-complexity-campaign/evidence/memo-evaluator-right-concatenation.md) now
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

[Complete actual left contraction result scope](lean-complexity-campaign/evidence/memo-evaluator-left-scope.md) now reaches the
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

[Constructed actual left contraction call](lean-complexity-campaign/evidence/memo-evaluator-left-recursion.md) now reaches its native
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

[Constructed fresh owned-word views](lean-complexity-campaign/evidence/memo-evaluator-owned-word-loans.md) now reaches actual references
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

[Constructed left-query concatenation](lean-complexity-campaign/evidence/memo-evaluator-left-concatenation.md) now reaches owned appended word
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

[Constructed owned matched witness](lean-complexity-campaign/evidence/memo-evaluator-matched-scope.md) now
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

[Constructed root-score arithmetic and native switch](lean-complexity-campaign/evidence/memo-evaluator-root-score-scope.md) now
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

[Constructed subtotal arithmetic and actual result switch](lean-complexity-campaign/evidence/memo-evaluator-subtotal-scope.md) now
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

[Complete tail scope and owned-drop support](lean-complexity-campaign/evidence/memo-evaluator-tail-scope.md) now
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

[Complete head failure and constructed tail recursion](lean-complexity-campaign/evidence/memo-evaluator-head-failure-tail-call.md) now
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

[Constructed pair/pair head recursion and result scope](lean-complexity-campaign/evidence/memo-evaluator-head-scope.md) now
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

[Complete actual evaluator empty-query miss execution](lean-complexity-campaign/evidence/memo-evaluator-empty-totality.md) now
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

[Constructed evaluator miss setup and native word routing](lean-complexity-campaign/evidence/memo-evaluator-miss-setup.md) now
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

[Complete actual evaluator cache-hit execution](lean-complexity-campaign/evidence/memo-evaluator-cache-hit-totality.md) now
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

[Complete common evaluator prefix and native lookup routing](lean-complexity-campaign/evidence/memo-evaluator-common-prefix.md) now
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

[Constructed native evaluator entry and lookup prefix](lean-complexity-campaign/evidence/memo-evaluator-native-prefix.md) now derives
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

[Constructed recursive helper and choice calls](lean-complexity-campaign/evidence/memo-evaluator-call-totality.md) now compose actual
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

[Stable recursive fuel and readback budgets](lean-complexity-campaign/evidence/memo-evaluator-stable-budgets.md) now preserve every
completed actual run's exact world/packet/full cost at all larger bounds.
Independently typed helper inputs give fixed joint sufficient thresholds, a stable
output and complete owner resources. Interpreted physical success and all other
planning obligations remain open. The 3,996-job build and two affected consumers
pass; 19 new theorems bring the accepted-baseline audit to 1,289 endpoints.
Eight selected statement seeds cover 1,070 unique declarations with no unknown
references. Broader regression evidence is inherited from the preceding commits.

[Typed helper totality and sufficient budgets](lean-complexity-campaign/evidence/memo-evaluator-helper-totality.md) now derives actual
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

[Global ownership for recursive source execution](lean-complexity-campaign/evidence/memo-evaluator-global-owners.md)
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

[Owner ledgers through entry, storage and non-call destruction](lean-complexity-campaign/evidence/memo-evaluator-owner-lifecycle.md)
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

[Exact owner transfer through packets, assignment, drops and return cleanup](lean-complexity-campaign/evidence/memo-evaluator-owner-packets.md)
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

[Derived typed call domains and recursive source refinement](lean-complexity-campaign/evidence/memo-evaluator-typed-calls.md)
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


[Calling control, parsed entry and checked return cleanup](lean-complexity-campaign/evidence/memo-evaluator-calling-entry.md)
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

[Concrete helper calls in the mixed world](lean-complexity-campaign/evidence/memo-evaluator-helper-calls.md)
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

[Addressed switches, return packets and actual choice](lean-complexity-campaign/evidence/memo-evaluator-addressed-control.md)
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

[Initial activations and executable storage/drop actions](lean-complexity-campaign/evidence/memo-evaluator-storage-actions.md)
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

[Computed frame resources and assignment](lean-complexity-campaign/evidence/memo-evaluator-derived-inventories.md)
now derive complete finite read/owner/loan inventories from actual roots/masks,
extract remaining contexts and preserve suspended caller inventories. Assignment
computes its own guards and post-RHS context while executing the RHS once, with
actual source/cost/frame correspondence. Initial/control/callee, exclusive owner/
spatial and dynamic region/destructor traces remain required, then public core/
wrappers/resources/G3. W06-C3 and the full planning goal stay open.
The 3,929-job build, all 37 Lean suites, native WP, nine Python tests and
929-endpoint axiom audit pass. Shared statement inspection covers 313 unique
declarations with no unknown references.

[Executable addressed RHSs and assignment](lean-complexity-campaign/evidence/memo-evaluator-addressed-rhs.md)
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

[Guarded in-place writes and storage lifecycle](lean-complexity-campaign/evidence/memo-evaluator-frame-writes.md)
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

[Addressable local storage and retained reference graphs](lean-complexity-campaign/evidence/memo-evaluator-local-storage.md)
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

[Addressed partial moves and logical destruction](lean-complexity-campaign/evidence/memo-evaluator-addressed-partials.md)
now retain concrete Box identities through owned field moves, fresh allocation
and partial destruction, with typed readback and caller-owner frames. The actual
source move/Box/drop primitives keep their complete costs. Live, duplicate-free
owners and guarded addresses are explicit resources. Whole addressed execution,
caller-local storage/loans and destructor interpretation remain required, then
public core/wrappers and global resources/G3. W06-C3 and the full goal stay open.
The 3,910-job build, all 33 Lean suites, native WP, nine Python tests and
780-endpoint axiom audit pass. Shared statement inspection covers 275 unique
declarations with no unknown references.

[Recursive evaluator typing and source regions](lean-complexity-campaign/evidence/memo-evaluator-recursive-typing.md)
now connect all nine actual type profiles to complete recursive snapshot
execution, with typed initial locals, both intrinsics and deep ordinary-output
closure. Actual scoped signatures/locals, call-region arities and all region-use
positions are kernel checked. Native totality composes with these types at the
same complete costs. Addressed moves/owners/storage/local loans/destruction,
public maximum/wrappers and global resources/G3 remain. Full W06-C3 stays open.
The 3,904-job build, all 32 Lean suites, native WP, nine Python tests and
734-endpoint axiom audit pass. Shared statement inspection covers 1,046 unique
declaration records with no unknown references.

[Actual evaluator source typing](lean-complexity-campaign/evidence/memo-evaluator-source-typing.md)
checks all nine lifetime-erased declaration/control profiles and both actual
Option instances. Independent partial-local typing now preserves reads, owned
field moves, expressions and actions, retaining holes, siblings and Box shells.
Next recursive control/callee typing, then addressed owners/storage/local loans/
regions and live destruction. Public maximum/wrappers and global resource/G3
obligations remain; this does not close W06-C3 or the full planning goal.
The 3,898-job build, all 30 Lean suites, native WP, nine Python tests and
706-endpoint axiom audit pass. Shared statement inspection covers 752 unique
declaration records.


[Universal actual evaluator/native agreement](lean-complexity-campaign/evidence/memo-evaluator-native-totality.md)
now covers every finite native word pair and warm table, all success/overflow/
error paths and exact returned tables. Full costs compose from actual syntax,
destruction and completed callees; sufficient fuel does not change them.
Independent consistency/memo-table results reuse their original sound-cache and
width premises. Whole-profile types/regions/owners/storage/local borrows and
addressed destruction, public core/wrappers and global resources remain next.
This functional milestone does not close W06-C3 or the full planning program.
The 3,890-job build, all 29 Lean suites, native WP, nine Python tests and
675-endpoint axiom audit pass. Shared statement inspection covers 837 unique
declaration records.


[Actual evaluator body and base paths](lean-complexity-campaign/evidence/memo-evaluator-base-paths.md)
now kernel-check the complete 113-local control and prove actual source/native
agreement for every cache hit and every query with either word empty. Arbitrary
warm tables/scores, exact returned table order and complete helper/local costs
are preserved. Recursive pair/pair error/overflow/success/resource composition
and whole-profile typed addressed safety remain next, then public core/wrappers
and G3. This does not close the full planning program or W06-C3.
The 3,881-job build, all 28 Lean suites, native WP, nine Python tests and
645-endpoint axiom audit pass. Shared statement inspection covers 838 unique
declaration records.


[Actual owned score choice](lean-complexity-campaign/evidence/memo-owned-choice.md)
now has a kernel body certificate, universal source/native and first-on-ties
contracts, and exact losing-witness destructor/work counts. For `n` losing-word
pairs, work is `30 + 4n`, visits `4n + 3`, Boxes `2n`; no score/word consistency
is assumed. Addressed live destruction and whole-evaluator/core composition
remain next. This completes another source fragment, with W06-C3 still open.
The 3,877-job build, all 27 Lean suites, native WP, nine Python tests and
634-endpoint axiom audit pass. Shared statement inspection covers 706 records.


The [evaluator helper bridge](lean-complexity-campaign/evidence/memo-evaluator-helper-bridge.md)
kernel-checks identity of all six actual helper bodies with their completed
profiles. Successful recursive execution preserves the same nesting fuel and
complete old cost, with zero additional destruction/solver-call currency.
Native contracts and addressed typing, owner/storage/spatial, loan and region
results are reused. Numeric-width premises are explicit and hold for all native
inputs. Next compose evaluator typing/regions/owners/storage/local borrows and
destruction, functional/overflow/table behavior and resources, then public core
and separate wrappers. Full W06-C3 and remaining planning targets stay open.
The 3,873-job build, 26 Lean suites, native WP, nine Python tests and
624-endpoint axiom audit pass. Shared statement inspection covers 1,239 records.


The [actual evaluator source profile](lean-complexity-campaign/evidence/memo-evaluator-source-profile.md)
now kernel-checks all nine retained bodies, including the 113-local evaluator
and public entry point, and binds source reading to complete profile execution.
Partial moves, scalar/checked-add operations, live drops, metadata and early
returns use the shared control executor/frontend. Native guards exercise actual
empty/nonempty and warm-cache overflow paths. Universal source/native and typed
addressed safety/resource composition remain next. The 3,865-job build, 25 suites, native WP, nine Python tests, thirteen Rust
tests, full regeneration check and 592-endpoint axiom audit pass.

The [actual evaluator/partial-local increment](lean-complexity-campaign/evidence/memo-evaluator-partial-locals.md)
inspects the pinned evaluator/public-entry extraction and proves partial-field
moves with exact transfer of declared destructor work. Siblings and Box shells
remain available; shared referents are readable but cannot be moved through.
Whole-local destruction charges the remaining structure and preserves other
locals. These primitives are not yet consumed by an evaluator source/heap
certificate. Next normalization/execution with arithmetic, metadata, local
borrows and full safety/cost composition. The 3,858-job build, 24 suites, native WP, nine Python tests and
572-endpoint axiom audit pass.

The [memo loan/region proof](lean-complexity-campaign/evidence/memo-loan-regions.md)
now composes actual helper runs with recursive typed shared loans, reference-free
ordinary outputs and parsed region-bearing local annotations. The existing
retained-world valuation and erasure lemmas are reused; insertion retains its
owned table while keys/witness may borrow into it. Native endpoints preserve
all prior source/heap, storage, guarded/spatial, owner-transfer and exact-cost
conclusions plus typed caller loans. Next actual evaluator/core, wrappers,
input/error policy and G3 adversaries. The 3,855-job build, 23 suites, native WP, nine Python tests and
552-endpoint axiom audit pass.

The [memo storage/initialization proof](lean-complexity-campaign/evidence/memo-stack-initialization.md)
retains distinct source allocation/deallocation markers and exact declared local
counts for all four helpers. Generic storage checker soundness and fuel induction
produce recursive traces of actual initialized reads, allocated writes, moved
slots and frame closure with unchanged complete costs. Native totality composes
storage, guarded/spatial traces, typed readback, exact events and insertion's
original table under its new tail Box. Dynamic loans/lifetimes are next, then
actual evaluator/core and wrapper composition. The 3,850-job build, 21 suites, native WP, nine Python tests and
531-endpoint axiom audit pass.

The [memo guard/spatial proof](lean-complexity-campaign/evidence/memo-spatial-ownership.md)
now traces every completed helper call through owner-safe local clobbers,
moved drops, return cleanup and separated complete ownership lists. Insertion's
owned table is retained in initial locals and suspended callers; no all-shared
shortcut is used. Native source/heap endpoints retain full costs, typed readback,
old-table identity and returned ownership. The 3,847-job build, twenty suites and
516-endpoint audit pass. Next storage/initialization and dynamic loan/lifetime
traces, then actual evaluator/core and wrapper composition.

The [memo type/region-scope proof](lean-complexity-campaign/evidence/memo-source-typing.md)
now kernel-checks actual layouts, signatures, nested annotations, static
constraints and free/body region binding for all four memo helpers. Generic
preservation lemmas prove actual operational typing; ordinary outputs are
borrow-free even inside owned payloads. Insertion retains its owned table
argument and has three lifetimes for four value inputs. The 3,842-job build,
nineteen suites and 484-endpoint audit pass. Next guarded local/storage/spatial
and dynamic loan/lifetime traces, then the actual evaluator/core and wrappers.

The [addressed memo primitive proof](lean-complexity-campaign/evidence/memo-heap-ownership.md)
now composes actual source runs with heap execution, independently typed append/
prepend readback and exact allocation growth. Concatenation owns its fresh
output; insertion transfers the original table under a new tail Box and preserves
external owner frames. A complete ledger retains old occurrences and adds each
fresh cell once. The 3,835-job build, eighteen suites and 461-endpoint audit pass.
Next establish intermediate type/storage/owner/loan/region traces for these
functions, then actual evaluator/core and wrapper composition.

The [actual memo primitive bridge](lean-complexity-campaign/evidence/memo-source-primitives.md)
now retains and kernel-normalizes concatenation/insertion source, constructs
successful native-input runs, and proves agreement with independent append/
prepend models and the translated Rust functions. Structural copy/Box counts
are explicit. The shared control semantics/parser now support different callee
sets. The 3,829-job build, seventeen suites, nine Python tests, thirteen ordered
Rust tests, full regeneration and 430-endpoint audit pass. Next extend addressed
safety to these bodies, then the actual memo evaluator/core and wrappers.

The [scoped region-erasure proof](lean-complexity-campaign/evidence/lookup-region-erasure.md)
now checks actual signature/body region binders and call arities, retains
region-bearing local types and proves their erasure equivalent to typed loans
under an explicit immutable retained-world lifetime. Both source snapshots
pass kernel certificates. `lookup_source_total` composes parsed source,
recursive regional traces, native success, safety, ownership, independent
first-hit readback and existing costs. The 3,823-job build, sixteen suites and
414-endpoint axiom audit pass. The next W06-C3 work is actual insertion,
concatenation, memo evaluation/core and wrappers, with the source/runtime trust
boundary explicit.

The [shared-loan proof](lean-complexity-campaign/evidence/lookup-shared-loans.md)
now backs each shared reference with a typed read in the retained caller heap,
checks source borrow routes and preserves loans through all recursive completed
runs. Ordinary results contain no shared references, including inside Boxes.
Native lookup composes this with prior safety/readback/cost theorems. The
3,815-job build, fifteen suites and 382-endpoint audit pass. Source region and
official interpretation adequacy remain W06-C3 work.

The [normal storage-lifetime proof](lean-complexity-campaign/evidence/lookup-stack-storage.md)
now retains distinct allocation/deallocation markers and checks initialized
reads plus allocated writes through every recursive completed normal run.
Both source bodies and exact declaration counts pass kernel certificates.
Native lookup composes storage, spatial/frame safety, typed readback and costs.
The 3,807-job build, fourteen suites and 338-endpoint audit pass. Shared-borrow
lifetimes and official source adequacy remain W06-C3 work.

The [intermediate spatial-ownership proof](lean-complexity-campaign/evidence/lookup-spatial-ownership.md)
now tracks duplicate-free Box occurrences across all live locals, temporaries
and suspended caller frames on completed normal paths. Both real programs have
recursive traces with unchanged complete costs; native lookup composes this
with success, final ownership and typed first-hit readback. The 3,800-job build,
thirteen suites and 304-endpoint audit pass. Stack/borrow/lifetime and official
source adequacy remain W06-C3 work.

The [operational type-preservation proof](lean-complexity-campaign/evidence/lookup-type-preservation.md)
now connects checked static constraints to actual addressed reads, borrows,
moves, aggregates and recursive execution. Both programs preserve typed output
and old memory at every fuel for successful runs, retaining complete source
costs. The 3,794-job build, twelve suites and 252-endpoint audit pass. Spatial
ownership, stack/borrow and official source adequacy remain W06-C3 work.

The [source type certificates](lean-complexity-campaign/evidence/lookup-source-typing.md)
now check lifetime-erased field declarations, signatures, local/nested
annotations and static constraints for all four helpers in both retained
extractions. Independent `Heap.Shape` witnesses and concrete certificates are
kernel checked. The 3,790-job build, eleven suites and 225-endpoint audit pass.
Operational type preservation, spatial ownership and stack/borrow/source
adequacy remain W06-C3 work.

The [checked frame-safety proof](lean-complexity-campaign/evidence/lookup-frame-safety.md)
now covers intermediate local clobbers, moved drops, callee ownership profiles
and return cleanup for both generated programs' completed normal executions.
Its sound analysis and recursive call proof preserve exact execution/cost.
The 3,785-job build, ten suites and 210-endpoint audit pass. Spatial ownership,
checked source typing/lifetimes and official adequacy remain W06-C3 work.

The [returned ownership proof](lean-complexity-campaign/evidence/lookup-return-ownership.md)
connects actual generated lookup/copy execution to exclusive fresh output
regions. Every new Box occurs once in the returned footprint; input Boxes are
not reused as owned output. The 3,779-job build, nine suites and 190-endpoint
audit pass. Intermediate ownership/frame/destruction and typed source adequacy
remain the next W06-C3 obligations.

The [addressed lookup realization](lean-complexity-campaign/evidence/lookup-heap-realization.md)
now preserves typed readback, complete costs and fresh Box-cell growth in an
immutable heap with shared aliases. Lookup succeeds for all represented native
inputs at sufficient fuel; input layouts are constructible. The 3,776-job build,
nine suites and 175-endpoint audit pass. Unique ownership/destruction, stack
lifetimes, checked JSON field typing and official source adequacy remain open.

The [checked source-control certificates](lean-complexity-campaign/evidence/lookup-source-certificates.md)
validate both actual lookup extractions, preserve complete outcomes/costs for
all fuels and reject the real extra-comparison mutant's old certificate/budget.
The 3,770-job build, eight Lean suites and 152-endpoint axiom audit pass.
Typed heap/reference/ownership/Box adequacy and the actual memo core remain
the next W06-C3 obligations; this is a snapshot-primitive control result.

The [whole-run memo work envelopes](lean-complexity-campaign/evidence/memo-work-envelopes.md)
now derive representation budgets from actual local operations and compose
nonuniform finite work bounds, with native Std.WP and two independent clients.
Cold list/dense setup and encoded index work are included. The 3,765-job build,
seven suites and 140-endpoint axiom audit pass. This closes the declared-model
run-budget gap; remaining input/body/key/materialization and source realization
keep MEM-03/W05, W04's other interfaces and W06-C3 partial. Earlier milestones
below retain their checked scope.

The [native memo core](lean-complexity-campaign/evidence/memo-interpreter.md)
now proves sequential interpreter correctness, once-only expansion, exact
root-plus-body request counts and finite warm-cache envelopes. Two counted
cache representations and the existing LV recurrence body fit the interface;
the [reuse audit](lean-complexity-campaign/evidence/memo-statement-audit.md)
records selected upstream declarations and compatibility. The
[LV follow-up](lean-complexity-campaign/evidence/memo-lv-correspondence.md) now
proves exact old-evaluator values/tables/counters and warm D-product bounds.
The 3,757-job build, updated memo suite and 115-endpoint axiom audit pass;
the unchanged suites passed in the preceding core build.

The [independent edit-distance client](lean-complexity-campaign/evidence/memo-edit-distance.md)
now proves minimum-cost edits and consumes the same generic memo theorem with
list/dense caches. The 3,761-job build, new suite and 125-endpoint axiom audit
pass. Dense index conversion and full cache setup are explicitly counted.
W04/W05 remain partial: complete representation work envelopes and other
size/substitution interfaces are open, including local input/body costs.
W06-C3 and the wider program's production/runtime/release/application work
remain open. Earlier dated milestones follow.

The [reified lookup operational pilot](lean-complexity-campaign/evidence/lookup-source-pilot.md)
adds checked instruction accounting and universal first-hit/event correspondence
inside the declared read-only model, plus a compiled extra-work Rust mutation.
All 3,750 main Lean jobs, four example suites and seven frontend regressions
pass. The reifier/reference interpretation remain trusted; full G1 and
SRC-01/C3 are still open.

The [2026-11-16 lookup packet model](lean-complexity-campaign/evidence/lookup-packets.md)
now proves structural comparison/copy/allocation envelopes and erasure to the
actual extracted function results. All 3,744 main Lean jobs and three example
suites pass. The source-event adequacy bridge remains open; this does not
establish Rust runtime bounds or complete G1/SRC-01.

The 2026-11-14 reprioritization supersedes the earlier proof-first sequencing.
Finish public Python/PyO3 algorithm coverage, independent correctness/parity,
and measured performance before substantial remaining proof work. Preserve
all established proofs. Full mathematical, production Rust correspondence and
applicable complexity verification remain blockers for the final verified
release, while development builds and use can proceed. The concise current
inventory and evidence are in [capabilities.md](capabilities.md).

The original-identity affinity isomorphism extension now has independently
specified operational pruning witnesses and complete mathematical optimum
proofs for both parent policies. Its witnesses preserve original order,
parent edges and endpoint uniqueness. The production arena has a conditional
feasibility/readback bridge; full weighted Rust DP/memo/score correspondence
and runtime remain open. All 3,739 main Lean jobs and both example suites pass.
Rust/Python and performance targets are unchanged.

The preceding actual production choice append and materializer milestone has composed source
contracts: old choices remain meaningful, new head/tail assembly is exact, and
bounded stored endpoints produce bounded emitted coordinates. All 3,735 main
Lean jobs, both example suites, 13 ordered-core tests and 234 required-native
installed Python tests pass. Complete production DP/memo/choice provenance,
parent feasibility, optimality and runtime refinement remain open.

The preceding integer-materializer milestone established
a source proof of exact token emission and safe termination from valid
arena/root/output bounds, with 3,732 main Lean jobs and 234 required-native
installed API tests passing at that milestone.
[Source theorem and the small stack-representation check](../../dev/benchmarks/2026-11-14-iso-choice-stack.md).

Production ordered isomorphism now caches scores/choices and reconstructs only
the winner. Rooted calls compute only the level recurrence. All 234 required-native
installed API tests, 13 ordered-core tests and 3,728 Lean jobs pass; the optimized
production score/choice refinement remains open.
[Short timing and memory evidence](../../dev/benchmarks/2026-11-14-ordered-iso-choices.md)
records the improvement without changing backend selection.

The exact matching API now bypasses square assignment for inputs without a
positive edge; its actual-source total-correctness theorem covers that branch.
All 3,728 main Lean jobs and 232 required-native installed Python tests pass.
[Small before/after measurements](../../dev/benchmarks/2026-11-14-exact-nonpositive.md)
record the effect. The preceding proof milestone also justifies the production
float family's transposed occupied-column restriction over exact ordered
arithmetic; actual float source/control-flow and runtime refinement remain open.

Implementation stability comes from exhaustive/differential objectives, independent
witness checks and native tests, plus short representative performance checks.
Use small workloads and about three timed samples during development; accept
some timing variance. Commit coherent implementation milestones before the
long final benchmark campaign. The new [complexity-library reuse audit](lean_complexity_library_reuse_audit_2026_11_14.md)
now has an [executed arlib experiment](../../proofs/experiments/arlib_cost/README.md)
with a proved memo-lookup bridge and operation bound. Its 3,744-job joint build
passes; arlib stays optional and main dependency pins remain unchanged.

## Initial proof scope: arithmetic boundary

Per the author's 2026-11-14 instruction, **IEEE-754 correctness is deliberately
excluded from the initial proof scope**. Prove the mathematical algorithms,
matching, witnesses, optimized schedules and applicable complexity results.
Rust correspondence must state its arithmetic model and any arithmetic
preconditions explicitly. Exact integer-core proofs retain their existing
checked-arithmetic guarantees. Do not identify idealized ordered-ring/real
operations with actual `f64` operations or claim an end-to-end IEEE-754 proof.

Floating-point rounding, numerical stability and overflow correspondence are
not initial proof-completion gates. Keep finite-input, overflow and precision
regressions as software tests. This exclusion does not remove the remaining
algorithmic, witness, production-structure or complexity proof obligations.
The [proof ledger](../../proofs/PROOF_STATUS.md) must distinguish those open
obligations from this intentionally excluded numerical scope. This decision
supersedes earlier planning text listing floating arithmetic equivalence as
required proof work.

Both Droschinsky Rust families and the verified exact assignment/partial
matching cores are now callable through public Python APIs. A fresh installed
wheel passes all 228 tests with native backends mandatory. Independent graph
witness rescoring and exhaustive optimum comparisons are included. Installed
API measurements cover both optimized schedules, matching deletion families,
conversion overhead and independent witness rescoring. See the capability
matrix and benchmark evidence before continuing the remaining ordered
coverage, correctness and optimization tasks.

The ordered isomorphism APIs now expose the existing root-preserving level
state with `rooted=True`, alongside the default general state. Independent
parent-preserving subset enumeration validates both contracts and fractional
affinities. Normal and genuine Rust-only ABI3 wheels are tested; the latter
passes the complete 228-test API suite on each CPython 3.10–3.14.

2018 now uses the fixed-left mapped/skipped schedule and includes the skipped
highest-vertex path case. Independent high-degree/path oracles pass; installed
APIs improve 179× on 32/32 stars and 19–36× on module trees. Directed view IDs
and original edge metadata now remove the remaining core lookup cost. Supplied-path
witness rescoring now passes independent checks and enables complete 512-node
scaling runs; production refinement and formal complexity remain open.
[Implementation and evidence](../../dev/benchmarks/2026-11-14-embedding-schedule.md).

2016 now reuses high-degree right-parent deletion families; exhaustive matching
and graph-witness checks pass. Measured 32/32 chain-versus-star and double-star
speedups are 2.74× and 1.69×. Later choice-table and dense-view changes address module costs; the current
2018 optimized schedule is implemented and measured separately.
[Evidence and assurance boundary](../../dev/benchmarks/2026-11-14-matching-families.md).

Both graph families additionally expose fixed ambient roots and the separate
root-to-root restriction, with original-node witnesses and all existing signed
scoring modes. Independent rooted oracles and 47 native / 199 installed tests
pass, including every host ABI3 runtime. A source-only portable rebuild at
`e272d36` also passes 199 tests on the glibc floor and all five runtimes. [Root contracts and measurements](../../dev/benchmarks/2026-11-14-graph-root-modes.md).

The 2018 API now also accepts positive infinity as the distance penalty,
forbidding skipped vertices under every root policy. Independent enumeration
and both witness formats validate this case; 48 native and 209 installed tests
pass, including each host ABI3 runtime. [Evidence](../../dev/benchmarks/2026-11-14-infinite-penalty.md).

The source-proved structural ordered isomorphism reference is now callable
from both balanced-sequence and NetworkX APIs as `reference-rust`, with
`node_affinity=None` and either root policy. Original-index reconstruction is
independently tested and extracted, but its refinement remains open. All 219
installed tests, 10 ordered-core tests, 3,713 Lean jobs and both Lean example
suites pass. Eight-pair stars are 625× slower than optimized Rust; this explicit
reference stays outside `auto`. [Evidence](../../dev/benchmarks/2026-11-14-ordered-isomorphism-reference.md).

## Verified actual one-path sparse augmentation: 2026-11-14

The actual signed-integer sparse search and checked path flip now have an
end-to-end independent minimum-permutation theorem from a feasible/tight
single-deficit matching and the paper's two-sided numeric invariant:
`Rust.SparseSearch.augment_sparse_permutation_spec`. Original-index readback,
rank/path construction, arithmetic safety and termination are derived. The
compact copied-graph deletion caller is implemented and tested, with projection
and warm-start source refinement still in progress. Full-matrix scans remain
a reference; the published optimized queue/runtime is open.

## Actual token and forest APIs with guided witnesses: 2026-11-14

The flat Boolean Rust API is totally verified with original token readback,
maximum contraction score and exact malformed-input side rejection. The
one-pair-per-vertex forest convention has an independent optimum bridge using
a retained virtual parent. The opt-in Python `impl="verified-rust"` integrates
that core for `node_affinity=None`; its token/NetworkX conversions remain tested
boundaries. Actual guided indexed reconstruction now has complete feasibility
and original-index correctness plus a recorded `2*n+1` witness-call bound.
Earlier reference backtracking is retained separately. Combined memo/copy costs,
optimized dictionaries, isomorphism indices and the paper runtime remain open.

## Verified actual indexed LCBE reference: 2026-11-14

The public Rust indexed contraction solver now returns independently maximum
trees with exact scores and canonical original edge/pair identities in both
inputs. `Rust.IndexedOrderedSolver.maximum_common_embedding_indexed_of_trees`
and `maximum_common_embedding_indexed_indices` prove success, actual original
pair deletions, unique indices in bounds and one pair identity per output edge.
The bound is fewer than 2^32 edges per input. Efficient witness reconstruction,
isomorphism indices and token/NetworkX conversion remain open; the current
reconstruction backtracks and makes no paper runtime claim.

## Verified actual exact assignment API: 2026-11-14

The actual square signed-i64 Rust assignment API now has an end-to-end total
correctness theorem (`Rust.AssignmentEntrypoint.min_cost_assignment_total_spec`).
Admitted matrices return a minimum-cost permutation with exact cost and
feasible/tight exported potentials; other represented inputs return the
specified size/shape rejection. Arithmetic safety and termination are derived
for every actual phase, including empty input. The actual rectangular optional
signed-i64 partial-matching API is also proved by
`Rust.MatchingEntrypoint.max_weight_partial_matching_total_spec`: exact input
indices, unique pair list, independently maximum compatible matching and exact
weight, or prescribed shape/size rejection. Graph/Python integration and
published optimized costs remain open. See
[proof status](../../proofs/PROOF_STATUS.md).

## Verified Rust memoization: 2026-11-14

The actual owned-memo Rust entry point now has a compiled end-to-end optimum
and exact-score theorem (`Rust.MemoizedOrderedSolver.maximum_common_embedding_of_trees`).
Its returned cache equals the numeric memo model after erasing witnesses;
cache keys are unique and bounded by the proved D-product. Both Rust solvers
pass all 38,809 ordered pairs through six edges. The linked-list table has
linear scans and copied witnesses; efficient dictionary/representation cost,
input-index mappings, ordered isomorphism and Python integration remain open.
See [proof status](../../proofs/PROOF_STATUS.md) and
[shape benchmarks](../../dev/benchmarks/2026-11-14-ordered-memo.md).

## Verified Rust ordered reference: 2026-11-14

The maintained Rust core now returns a structural maximum common tree and
exact score. Its Charon/Aeneas-translated entry point is proved correct for
all independent input trees below 2^32 edges each, with representation,
termination and arithmetic safety proofs. The exhaustive Rust oracle checks
all 38,809 pairs through six edges. The initial core is an exponential reference; the verified memoized entry
point is described above. Index mapping, efficient representation costs, Python
conversion and the unordered paper proof chains remain open.

## 2004 proof tranche accepted: 2026-11-14

The operational Lemma 8 recurrence now has a general constructive correctness
proof (`paperCommon_correct`, `paperCommon_tree_correct`), plus a separate
numeric recurrence theorem (`paperLcs_optimum`). Definition 4's least state
family, Lemmas 1--6, Fact 2, corrected actual-leaf bounds and Theorem 1 in
independent tree parameters compile. Theorem 2 is proved for operational
containment. Exact endpoints and all remaining obligations are in the
[paper statement crosswalk](paper_statement_crosswalk.md).

This closes the ordered LCBE mathematical optimum and state-bound chain.
Full implementation cost, input-index witness reconstruction, the distinct
ordered-isomorphism contract and Python integration remain open.
A fresh source-only checkout reproduced the previous full library build.

## Executed progress: 2026-11-14

The full Lean 4.35.0 library now builds in the VM with its nested `.lake`
bind-mounted to ext4. The current evidence and exact theorem names are in
[`proofs/PROOF_STATUS.md`](../../proofs/PROOF_STATUS.md); reproduction and
translation pins are in [`proofs/VERIFICATION.md`](../../proofs/VERIFICATION.md).
The older starting-point table below is historical.

Completed increments:

- Two-way operational contraction/encoding bridge and the printed Definition 2
  counterexample compile; the public endpoint dependency baseline is reviewed.
- An independent executable Lean contraction oracle is proved to return an
  `IsMaximumCommon` tree, with a complete contraction enumeration theorem.
- An executable finite integer-weight partial-matching oracle has a global
  optimality theorem against independently defined feasible matchings.
- Actual Rust source translates with pinned Charon/Aeneas; generated Lean
  builds and a refinement theorem connects the contraction budget to trees.
- The 2018 Python scorer/oracle and Rust reference DP use Definition 4's path
  scoring; both 1.75 discriminator cases pass. Omitted branch-point selections
  are rejected; exhaustive Rust mapping enumeration validates optimal scores
  and returned witnesses on small trees.
- Focused Lean, Rust, regeneration and independent-oracle CI is configured;
  the first remote run remains pending.

Next: paper statement ledgers, D/R/S combinatorics and the 2004 DP optimality
proof, then verified matching/graph recurrences and actual solver extraction.
The exhaustive reference solvers establish baselines, not published running times.

## Starting point as of 2026-11-13 (after reported successful Lean build)

| Priority | Immediate action | Evidence of completion |
| --- | --- | --- |
| 1 | Record the now-passing Lean 4.35.0 foundation build, check theorem axioms, pin the Lake manifest and add Lean CI | Reproducible build from a fresh checkout, accepted theorem inventory and dependency audit |
| 2 | Pin ordered-tree contraction/root conventions and independently enumerate tiny tree contractions | Small examples and oracle agree with mathematically specified embeddings |
| 3 | Prove encoding round trips and both directions of Dyck-word containment/contraction correspondence | Checked independent tree/sequence theorem |
| 4 | Test a minimal Charon/Aeneas-generated Lean function against a mathematical specification | Translated real Rust source, matching toolchain pins and a checked refinement lemma |
| 5 | Specify finite weighted partial matching and independently correct the 2018 paper path scorer | Matching oracle and 2018 edge-label/skipped-path counterexamples pass |

Other paper and implementation work can proceed in parallel **after** its
own prerequisites are met. Do not treat passing source compilation as
completion of the original paper, or correctness of a slow reference DP as
proof of the published optimized running time.

## Relevant files elsewhere in the repository

- `proofs/README.md` and `proofs/PROOF_STATUS.md`: current Lean workspace and
  declaration-level build/assurance state.
- `proofs/SubtreeProofs/Paper2004/`: fresh mathematical Lean source. The old
  versioned proof development is in Git history, not an import dependency.
- `rust/src/lib.rs`: existing optimized ordered balanced-sequence solvers
  (`Solver::emb`, `Solver::iso`) and Python bindings.
- `rust/crates/common_subtree_algorithms/`: Droschinsky Rust reference algorithms,
  matching solver, tests and benchmark drivers.
- `networkx_algo_common_subtree/common_subtree_reference.py`: slow independent
  reference logic for parts of the unordered algorithms; its current 2018
  scorer must be corrected before being a paper-faithful oracle.
- `dev/common_subtree_algorithms_notes.md` and
  `docs/source/common_subtree_correctness.rst`: historical implementation notes;
  the latter's 2018 path-scoring description needs review.

## Updating the plans

When completing a milestone, record the exact checked theorem, file, Rust
entry point (if applicable), command/test evidence, hypotheses, benchmark
configuration and outstanding gaps. Distinguish **authored**, **compiled**,
**proved**, **extracted**, **tested**, and **measured**. Keep paper statements
and corrections in an explicit theorem crosswalk rather than renaming weaker
results after stronger claims.

The program charter holds decisions shared between papers. The individual
paper plans hold their detailed proof and algorithm obligations. Avoid
reintroducing obsolete proof-reset instructions or duplicating an entire
program history inside new subtask plans.

## Native backend parity and migration

See [`backend_parity_and_cython_retirement.md`](backend_parity_and_cython_retirement.md)
for the independent oracle and cross-backend test plan, reproducible
comparative benchmarks, and requirements for replacing Cython as the fallback
with fully verified Rust implementations.
