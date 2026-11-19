# Existing helper proofs in the actual evaluator profile: 2026-11-17

Baseline: `6137120`. This increment connects the expanded actual evaluator
program to the completed lookup/memo-helper proofs. It reuses the old source
executions, native correctness and addressed safety results, rather than proving
those algorithms again. The evaluator/choice/public-entry bodies themselves
still need universal functional, resource and addressed safety composition.

## Domain and exact execution bridge

`SourcePartialReadback` proves full lifted-state place-read compatibility,
including shared and owned dereferences, guarded variants and retained tags.
`SourceEvalLegacy{Values,Actions,Control,Run}` embeds the original helper
instructions/control in the expanded profile. All successful old executions
preserve the returned value and the *entire* old instruction/event cost at the
same call-nesting fuel. The new destruction and evaluator-call currencies are
zero on those executions. A general driver theorem consumes the existing
interpreters' actual zero/successor equations; it introduces no new interpreter.
Control routing and early returns continue to use the shared `Control.execWith`.

The bridge requires recursively bounded numeric inputs. This is necessary:
old snapshot values contain arbitrary naturals, whereas the expanded profile
checks `u32` copies. `Bounded`/`FieldsBounded` express only that numeric domain,
not a replacement for the existing source or heap type system. Operand and
expression simulation preserve it, and native word/result/table encodings
satisfy it for every native value, including maximum-width scores.

The generic theorem is successful-old-run preservation, not equality on failed
arbitrary programs. The expanded profile permits live destruction, while the
old conditional-drop profile fails on a nonempty local. The regression suite
records both this difference and the over-wide numeric counterexample.

## Actual body identity and native contracts

`SourceEvalHelperCertificate.lookup_body` and `memo_body` kernel-check that all
six actual helper bodies in `SourceEval.Certificate.original` equal the embedded
previously certified bodies. Both generic Box identities are included. They
consume the actual pinned JSON readers; no external normal-form template or
native proof oracle supplies these identities.

`Helpers.lookup_run`/`memo_run` discharge recursive callee compatibility at every
fuel. `lookup_normalized`/`memo_normalized` connect the earlier normalized source
programs too. Universal native contracts now execute the expanded actual
program for word copy, structural comparison, result copy, first-hit lookup,
concatenation and insertion. They retain the existing sufficient nesting-depth
hypotheses, complete costs and structural event formulas. Arbitrary tables,
duplicate keys and unsound stored witnesses/scores remain admitted; no cache
soundness or optimality premise was added to these helper APIs.

## Addressed results reused without changing their scope

`SourceEvalHelperSafety` composes the new source runs with the existing
addressed lookup/memo source-region theorems. The generic scoped endpoints
retain representation, operational typing, actual checked region annotations,
retained-world shared loans, old-memory extension and exact allocation growth.

The native concatenation/insertion totality endpoints retain all previously
completed addressed, owner, spatial/frame, storage/initialization and typed
loan/region conclusions, with exactly the same old work cost. Concatenation's
output owns fresh Boxes. Insertion retains the actual owned table cell beneath
its fresh tail Box; keys and supplied witness may borrow into that table.
External-frame separation remains conditional on its explicit valid separated
input premise, and caller loans remain stable.

These are compositions with the existing logical addressed helper model.
They do not establish addressed execution of evaluator partial locals,
caller-owned-local borrow validity, live destruction, compiler behavior or
physical allocator safety. Parsed evaluator typing/regions and complete
owner/storage/local-borrow/destruction simulation, then functional/error/table
and resource correspondence for evaluation/choice/public core remain next.
Wrapper/input-policy and G3 obligations follow. D12's scoped source-operation
boundary remains unchanged; SRC-01/C3, MEM-03/04, W04 and APP targets stay open.

## Reproduction and evidence

From the repository root, verify the VM-local cache mounts, then run Lake from
`proofs/`:

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceEvalHelpers.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

The aggregate library publicly imports the new safety endpoint and CI runs the
new independent consumer/domain-regression suite. Production Rust, generated
artifacts, parser/executor implementations and all dependency pins are unchanged.
Validation passes:

- Full library: 3,873 jobs; the actual-body kernel certificate took 365 seconds.
- All 26 Lean suites, native WP example and nine Python reifier tests.
- 624 distinct audited endpoints, including 32 new endpoints; axiom closures
  remain within `propext`, `Classical.choice`, `Quot.sound`.
- Shared `leanq` statement inspection of `lookup_run` and `insert_source_total`:
  1,239 records, retaining actual program execution, numeric-domain and
  addressed/native/ownership/cost premises and conclusions.
- New modules have no warnings. `git diff --check` passes.

Local logs: `/var/tmp/subtree-eval-helper-full-build.log`,
`subtree-source-eval-helper-cert.log`, `subtree-eval-helper-regression.log`,
`subtree-eval-helper-axioms.log` and `subtree-eval-helper-statements.{json,txt}`.
All but the first explicit path share the `/var/tmp/` directory. The preceding
`6137120` full pinned regeneration and thirteen Rust tests remain the unchanged
provenance/behavior baseline; this increment changes no Rust/generated data.
