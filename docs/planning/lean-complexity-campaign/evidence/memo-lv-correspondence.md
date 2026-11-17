# Exact LV evaluator correspondence, 2026-11-16

**Further follow-up:** [independent edit-distance client](memo-edit-distance.md)
now supplies minimum-edit correctness and both list/dense consumers. The
remaining W05 work is complete priced representation/local-cost envelopes;
source adequacy and W04's other interfaces remain open. The evidence below
records this earlier milestone's checked scope.

`Complexity/Paper2004/MemoCorrespondence.lean` connects the
[native memo interpreter](memo-interpreter.md) to the **unchanged existing
`memoLcs` computation**, preserving values, full table order and all three
existing counters. This closes that named W05 correspondence obligation at
C1. It does not complete W05, source/Rust refinement, or the paper runtime.

## Checked endpoints

In namespace `SubtreeProofs.Complexity.Paper2004`:

| Declaration | Statement/scope |
| --- | --- |
| `read_eq_memoFind` | The list implementation's counted read equals existing `memoFind`, including its exact comparison count, for every table. |
| `contents_eq_memoLookup` | The representation's abstract contents equal existing first-hit `memoLookup`, including duplicate-key tables. |
| `eval_refines_memoLcs` | Above the existing semilength rank, native evaluation succeeds with the old evaluator's exact value and table. Each event counter increases by the old evaluator's exact calls/misses/comparisons. No cache soundness/distinctness premise. |
| `sound_of_memoSound` | The established independent `MemoSound` invariant implies the new cache-soundness contract. |
| `envelope_closed` | The existing D-product is closed under the four actual direct requests. Uses the already proved `states_closed` rules. |
| `roots_envelope_spec` | Arbitrary roots in that D-product, repeated roots and sound valid warm storage satisfy the generic initially-absent expansion/call envelope. Unrelated sound warm entries may lie outside the D-product. |
| `memoLcs_calls_from_generic` | Under sound distinct warm storage, the generic exact-request theorem recovers the old computation's `calls <= 4 * misses + 1`. |
| `memoLcs_warm_misses_from_generic` | Actual old-evaluator misses are bounded by D-product keys absent from the initial warm table. |

The strong correspondence quantifies over any incoming event prefix. If
`r := memoLcs left right initial.cache`, it produces `final` satisfying

```
eval listOps body fuel (left,right) initial = ok r.value final
final.cache = r.table
calls(final) = calls(initial) + r.calls
completedLength(final) = completedLength(initial) + r.misses
lookupWork(final) = lookupWork(initial) + r.comparisons.
```

Its only input bound is `left.semilength + right.semilength < fuel`.
Soundness and distinctness are unnecessary for operational agreement, so the
theorem includes stale/duplicate warm tables rather than silently excluding
them. Such tables do not acquire independent value correctness from this
equality. Soundness/validity remain explicit premises of the generic
once-only and envelope applications.

The proof follows actual counted reads, empty-side branches and all four
sequentially threaded children. It identifies intermediate cache tables and
then composes the counters. It does not derive cost equality from final score
equality. The original `memoLcs_counts` theorem remains unchanged, including
its unconditional scope; the new conditional corollary demonstrates generic
reuse rather than replacing it with a weaker theorem.

## What the client reuses and retains

The application supplies the existing independent `paperLcs` recurrence,
local body correctness, semilength descent, D-product closure and four-request
bound. The generic interpreter supplies soundness/preservation, actual trace
uniqueness/domain accounting and root-plus-body accounting. The warm miss and
multi-root envelope applications use those theorems without redoing the
recursive memo-count induction. The operational correspondence still needs a
local proof because matching final values alone cannot identify table work.

List comparisons remain whole-key tests, exactly as in existing numerical
`memoFind`. Structural word comparisons, key construction, witness copying,
source allocation and machine runtime are not included in this currency.
The generic body and the existing numerical evaluator are score-only; this
does not identify their costs with the owned-witness Rust memo implementation.

## Validation and remaining work

The main 3,757-job build and updated `Tests/Memo.lean` pass. The suite now also
checks empty cold/warm inputs, the one-pair recurrence's exact tuple
`(value,calls,misses,comparisons) = (1,5,4,4)`, and first-hit unsound duplicate
storage returning 17 with `(calls,misses,comparisons) = (1,0,1)`.
All decisions are kernel-checked. Four new endpoint axiom closures are listed
in `BaselineAudit.lean`; the full audit has 115 endpoints within the established
baseline axiom set. New modules have no warnings. No main pin, old evaluator,
Rust source or generated file was changed.

```bash
(cd proofs && lake build)
(cd proofs && lake env lean Tests/Memo.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

W05 still requires the unrelated independently specified client and complete
run-level work envelopes for both representations, with initialization/key
conversion/finalization accounted for. W04's other substitution/size contracts
remain open. W06-C3's source/reification/heap bridge remains separate. No
overall G2, MEM-03/MEM-04, APP-01 or research-program completion is claimed.
