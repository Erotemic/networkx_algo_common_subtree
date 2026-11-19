# Scoped lookup regions and erasure: 2026-11-17

Baseline: `94db2f3`. Eight `Rust/LookupRegion*.lean` modules extend the
[typed shared-loan proof](lookup-shared-loans.md) with checked source region
binders, region-bearing local types and an explicit erasure equivalence.
`lookup_source_total` composes these with successful native lookup, independent
first-hit readback, ownership, storage and the existing operation currencies.
This is the immutable retained-world source-operation pilot. Full W06-C3 still
requires insertion, concatenation, memo evaluation/core, wrappers and adversaries.

## Pinned source meaning and accepted scope

The inspected Charon revision is `454586e9b770231e66d2062993e632dfc06463e2`
(schema 0.1.315). Its `ast/type_level/regions.rs` distinguishes free signature
variables, body-bound existential regions, static/erased regions and region
least-upper-bounds. `ast/bodies/unstructured.rs` freshens body regions;
`transform/typecheck_and_unify.rs` subsequently unifies body IDs. Used body IDs
can repeat and leave gaps; requiring a dense list of used IDs would reject
valid source. Bounds are checked against `bound_body_regions` instead.

The pinned Aeneas revision remains
`5a392f4b80a4d0d05abc240eb2a7fa70622a9a35`. Its `src/llbc/Substitute.ml`
erases environment-value regions; `src/llbc/RegionsHierarchy.ml` separately
analyzes signature lifetime relations. This increment supplies a named Lean
erasure theorem for the selected shared-only helper model. It does not prove
the OCaml interpreter or Rust compiler correct.

The reader accepts canonical late-bound signature region parameters, with the
known helper arity and empty explicit outlives/type-constraint arrays. Signature
uses must be `Var.Free` within the signature binder; body uses must be `Body`
within the body binder. Static, erased, bound-variable and other region forms
are rejected. Shared-only source types remain checked by the previous reader.
There are no new mutable-reference or stack-reference cases.

| Helper | Signature regions | Original body regions | Mutant body regions | Original/mutant locals |
| --- | ---: | ---: | ---: | --- |
| copy word | 1 | 19 | 19 | 10 / 10 |
| compare words | 2 | 47 | 47 | 15 / 15 |
| copy result | 1 | 10 | 10 | 6 / 6 |
| lookup | 3 | 52 | 60 | 20 / 23 |

`LookupRegionReader` attaches region-bearing types to the exact earlier erased
types. `Checked`/`CheckedFields` carry erasure equality and independent inductive
scope proofs. `LookupRegionScope` recursively checks all JSON descendants of
each selected signature and body for reference-region positions and generic
region lists, including annotations nested in unwind metadata. Calls to each
selected helper have the expected number of region arguments; generic Box has
zero. `Tree.mentions_bound` proves any recognized region use in any descendant
is bound. This checks unwind annotations, not unwind execution.

`LookupRegionProgram` retains the actual JSON signature/body and all their
scope certificates, parameter/output annotations, local annotations, previous
static constraints and argument/return prefixes. Explicit coverage includes
all four ordinary helpers. `check_sound` also exports exact normalized bodies
and checked old-heap borrow routes. Both complete retained source snapshots
pass `decide +kernel` in `LookupRegionCertificate`; their JSON is unchanged.

## Independent interpretation and erasure

`LookupRegionTypes` defines region-bearing shared, owned, tuple and scalar/ADT
types. Scope is an inductive judgment, independent of parser success. Renaming
preserves erasure. `instantiate_scoped` proves free-signature substitution is
body-scoped when argument count and each argument's bounds are established.

`LookupRegionSemantics.Value` interprets a shared reference using an actual
current pointer read, a typed loan in the retained caller heap, a live region
under a supplied valuation, and a recursively interpreted pointee. Owned values
follow actual current heap reads; tuples cover all fields. ADTs use the previous
independent typed-loan interpretation of their closed layouts.

The selected valuation is explicit: `callLifetime base region current` means
`Extends base current`, for every region. Under this retained-world witness,
`scoped_erasure_iff` proves equivalence between a well-scoped region-bearing
value and the earlier `Borrow.Safe` judgment. `instantiate_value` additionally
constructs a scoped interpretation after well-bounded signature substitution.
The reverse direction depends on memory extension and actual old typed loans.
It is not valid for arbitrary region valuations; a regression exercises this.

All source-created shared pointers in this helper profile refer into the
retained caller heap, every completed run extends that heap, and ordinary
results contain no shared reference, even inside owned payloads. These previous
proved facts justify a common retained-world lifetime witness for this pilot.
It is not a statement about physical time, unique region identities, general
outlives inference, mutable loans, freeing, or stack-address provenance.

## Actual execution and public endpoint

`LookupRegionCalls.trace_regional` interprets the actual checked local
annotations at any loan-trace frontier. `RunScoped` records the parsed source
declaration and those regional locals for each ordinary call, plus the actual
loan trace and recursively scoped callees. `run_scoped` discharges the callee
contract by fuel induction using the checked source constraints, prefixes and
borrow routes. The generic Box case uses the actual fresh allocation.
`RunScoped.erases` recovers the same completed execution and full cost.

`LookupRegionRefinement.lookup_source_total` constructs a successful addressed
lookup for represented native inputs and sufficient fuel. Its conclusion
retains the actual successful source-program read, regional recursive trace,
loan-safe and borrow-free result, stack/spatial/frame traces, exclusive output
ownership, independent typed first-hit readback, old-memory extension, exact
allocation growth, unchanged declared events and the existing instruction
bound. External owner frames and pre-existing typed reads survive. Successful
execution is supplied by native totality, not inferred from parser acceptance.
The same generic recursive theorem applies to the certified mutant program.

## Validation and reproduction

The 3,823-job main build, all sixteen Lean suites, native WP example, seven
Python reifier tests and 414-endpoint axiom audit pass. All 32 added audited
closures stay within `propext`, `Classical.choice`, `Quot.sound`. New modules
have no warnings. Rust, generated code/JSON, dependencies and extraction pins
are unchanged. The existing pinned extraction is the provenance baseline.
Shared `leanq` inspected `lookup_source_total`'s elaborated statement closure
(623 records), including the unchanged represented native inputs, successful
source read and actual execution, regional/loan/storage/spatial/frame witnesses,
independent readback, costs and retained external frames.

`Tests/LookupRegions.lean` is in CI. Focused JSON/type fragments exercise
unbound body IDs accepted by the earlier erased reader, signature/body scope
confusion, out-of-range signature variables, erased regions, nested unwind
annotations and missing/invalid call-region arguments. Semantic examples cover
a live typed old loan, a false valuation, independent binder invalidity and
well-scoped signature substitution. These are explicit fragments, not new
compiled Rust mutants. Both actual retained programs separately pass complete
kernel certificates.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/LookupRegions.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement SubtreeProofs.Rust.LookupSource.Heap.Regions.lookup_source_total \
  --root-module SubtreeProofs.Rust.LookupRegionRefinement
```

## Remaining campaign work

The scoped interpreted lookup pilot now composes source control, types, actual
addressed reads/moves, local storage, owners, immutable loans, region erasure,
independent output readback and declared costs. The boundary is the pinned
Charon/data import and the declared normal-path primitive/source interpretation,
including fresh Box behavior. There is no theorem connecting this interpreter
to compiled machine instructions, physical stack layout, full Rust provenance,
mutable references, freeing or failed/unwind execution. Those boundaries must
remain explicit; the accepted initial source-operation endpoint in dossier D12
does not require a whole-compiler proof before the memo pilot can proceed.

Next compose actual insertion, concatenation, memo evaluation and one public
core entry point, then the indexed/token/reconstruction wrappers, input/error
policy and G3 adversaries. Keep unpriced local/input/key/materialization work
and physical space separate from the current declared-currency theorem.
W06-C3, SRC-01, MEM-04 and the full planning objective remain open.
