# Whole-run memo work envelopes, 2026-11-16

The native memo core now derives representation primitive budgets along actual
runs and composes them into whole-run declared-currency bounds. Both the LV
and edit-distance clients consume the theorem. Edit distance exercises list
and dense implementations with actual cache setup and index encoding included.
These are **C1 event-model bounds**, not complete Lean/Rust runtime or source
adequacy results. Retained input/body/key operations remain explicit below.

## Checked interface and proof

`Complexity/Memo/Work.lean` adds `WorkModel ops` with only local obligations:
a storage-size measure, monotone read/write budget functions, bounds for the
actual primitive counters on valid/fresh storage, and at-most-one size growth
per insertion. It assumes neither the total work nor the number of misses.
The measure controls primitive budgets; it need not mean live memory.

`eval_spec`/`evalRoots_spec` now ask lookup invariants to survive the **actual
`ops.read` counter on valid storage**. The old premise quantified over arbitrary
counter values, which could not express these cost invariants. Conclusions and
the executable evaluator are unchanged; previous consumers still compile.

`WorkInvariant` proves along execution that storage size is at most initial
size plus actual completions, and that all emitted read/write counters fit the
current size envelope. `roots_work_spec` obtains it through the existing native
interpreter invariant theorem. Closure, unique completion, independent values
and exact root-plus-body accounting remain supplied by the previous core.

For initially absent envelope keys `M`, put

```
m0   = model.size initialStorage
Qbar = roots.length + sum (key in M) arity(key)
Lbar = sum (key in M) bodyBound(key).
```

`roots_weighted_work_envelope` proves successful independent results and

```
Event.totalWork(hReq,hExp,final.events)
  <= (hReq + readCost(m0 + M.card)) * Qbar
     + (hExp + writeCost(m0 + M.card)) * M.card
     + Lbar.
```

Premises are local body arity/work bounds, finite request closure, initial
cache validity/soundness and sufficient descent fuel. They do not include
budgets for final emitted events. Warm entries outside the envelope are
permitted; their contribution to initial representation size is retained.

`Event.localWork_eq` identifies actual local work with the sum over the
canonical completed bodies; trace correctness supplies that identification.
Mathlib list-to-finset sums and subset/nonnegative sum inequalities lift it to
the initially-absent envelope. `roots_work_envelope` specializes uniform body
budgets; `roots_weighted_work_wp` exports the same result through installed
native `Std.WP`, with false error postcondition under the totality hypotheses.
There is no second resource monad or predicate-transformer engine.

## Actual representations

`Complexity/Memo/RepresentationWork.lean` instantiates the local laws:

| Representation | Size measure | Read budget at size `s` | Write budget |
| --- | --- | --- | --- |
| Association list | actual list length | `s` whole-key tests | one cons |
| Bounded direct array | allocated array length | one cell unit | one cell unit |
| Dense pair array | allocated array length | two encoding arithmetic units plus one cell unit | same three units |

The array measure is deliberately not presented as live occupancy or peak
space. Writes preserve allocated length and satisfy the generic size-growth
upper bound. The paired implementation uses the existing checked
`column + width * row` encoding; its two arithmetic units are included in both
primitive counters.

## Client bounds

`Complexity/Paper2004/MemoWork.lean` proves `roots_list_work` for sound distinct
warm tables and arbitrary roots in the existing D-product. If `m` keys in that
product are initially absent, its bound is

```
(hReq + initialTable.length + m) * (roots.length + 4*m) + (hExp + 5)*m.
```

`cold_list_work` additionally executes and charges empty-list initialization.
The established exact correspondence with unchanged `memoLcs` remains in
scope: its values, full tables, calls, misses and comparisons are identified.
No original unconditional counter theorem or small-input case was removed.

`Complexity/EditDistance/Work.lean` supplies uniform and nonuniform bounds for
both actual runners. Mathlib `Fin.card_filter_val_lt` and product/filter
cardinality prove that exactly `n*m` index pairs are interior. Boundary bodies
have zero direct requests and local score operations. For `N=(n+1)*(m+1)` and
`P=n*m`, the sharper cold-cache bounds, **including cache setup**, are

```
list:  1   + (hReq + N) * (roots.length + 3*P) + (hExp + 1)*N + 5*P
dense: N+1 + (hReq + 3) * (roots.length + 3*P) + (hExp + 3)*N + 5*P.
```

These are the same generic theorem with different primitive contracts. They
are not performance measurements. A fully allocated dense cache still has
setup cost with no roots, and unrelated warm list entries still cost scans.

## Validation and reproduction

The main **3,765-job build**, all **seven Lean suites**, and **140 endpoint axiom
closures** pass. Fifteen new audit endpoints stay within the established
`propext`, `Classical.choice`, `Quot.sound` set. New modules have no warnings.
No dependency pin, production Rust or generated source changed.

`Tests/MemoWork.lean` checks actual total declared work with cache setup:
one-symbol replacement costs 13 for the list and 34 for encoded dense storage;
the nonuniform dense theorem also proves the latter bound. Empty roots still
cost dense setup. A warm-table example has two unrelated entries outside a
one-key reachable envelope, demonstrating why initial list size cannot be
discarded. An extra-read implementation preserves functional cache laws while
failing the old empty-list primitive budget; a paired dense lookup fails the
one-cell-only budget. These are C1 adversaries, not new Rust mutations. All
finite decisions are kernel-checked. The suite is registered in CI.

```bash
(cd proofs && lake build)
(cd proofs && lake env lean Tests/MemoWork.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement \
  SubtreeProofs.Complexity.Memo.roots_weighted_work_wp \
  --root-module SubtreeProofs.Complexity.Memo.Work \
  --out /var/tmp/subtree-work-statement.json --hide-boundary
```

The shared `leanq` tool inspected 108 elaborated statement records for that
seed. The disposable statement JSON and `/var/tmp/subtree-work-*.log` outputs
are not dependencies or substitutes for the maintained proofs. No custom
parser/checker was added.

## Remaining scope

The gap from **assumed final-trace primitive caps to proved run-level caps** is
closed for these implementations and currencies. MEM-03/W05 are still partial
outside this declared model: structural word equality/copy, symbol comparison,
list/input access, computing lengths, body/key construction, persistent array
copying, arithmetic width/bit cost, output/finalization and source allocator
work need their own primitive or source realization. The local four/five units
still count score arithmetic/minima only. Cache setup counters do not account
for complete input conversion or output materialization.

W04's result-size/substitution interfaces, W06-C3's checked reification and
typed heap/reference/move simulation, and the actual source memo/public-wrapper
cost bridges remain open. These theorems do not close SRC-01, MEM-04, APP-01,
peak-space obligations, independent upstream review or the wider research
program's release/application-study requirements.
