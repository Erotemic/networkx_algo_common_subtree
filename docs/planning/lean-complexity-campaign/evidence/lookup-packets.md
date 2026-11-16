# Executed structural lookup packet bounds

Baseline: `2240373` (2026-11-16). This is a bounded W02 increment, not completion
of G1, W03, W06 or SRC-01. No production Rust, generated Lean, dependency pin,
backend choice or mathematical optimum specification changed.

## Checked computation and statements

[`Rust/LookupEvents.lean`](../../../../proofs/SubtreeProofs/Rust/LookupEvents.lean)
implements a deterministic event interpreter on the **actual extracted owned
types**. It follows `words_equal`, `copy_word`, `copy_result` and `memo_lookup`.
The independent result contract remains `MemoizedOrderedSolver.findResult`:
first structurally equal key, including duplicate keys. A sound/unique cache is
not assumed for this result contract.

The event vector distinguishes table visits, structural comparison visits,
word-copy visits, Box creations and result-copy packets. Each local packet
includes the associated field/discriminant/control/return work at this model
level. These are selected source-operation packets, not RAM instructions,
allocator time, allocation bytes, physical peak space or hardware time.

All declarations below are in `SubtreeProofs.Rust.LookupEvents`:

| Checked declaration | Contract |
| --- | --- |
| `compare_value`, `compare_erases` | The short-circuit comparator decides equality and erases to the extracted comparator |
| `compare_bound`, `compare_self` | At most `2*L+1` visits for a query with L pairs; equality visits exactly that many |
| `copy_exact`, `copy_erases` | Copying W pairs visits `2*W+1` word constructors and creates `2*W` Boxes; erasure agrees with extracted copying |
| `copyResult_exact`, `copyResult_erases` | The complete witness word is copied and one result-copy packet is charged |
| `lookup_value`, `lookup_erases` | Independent first-hit result and extracted lookup value/termination correspondence |
| `lookup_bound` | The previously proposed table/comparison/copy packet envelope, now proved for every represented table/query |
| `sound_output_bound` | Cache soundness bounds witness-copy size by the smaller query; no arbitrary output-size premise |
| `sound_unit_bound` | A complete unit-packet upper bound, including the empty-table case |
| `first_hit_exact`, `left_mismatch` | First hits ignore the suffix; left-key mismatches skip the right-key comparator |
| `extra_scan_changes_cost` | A second scan preserves the answer but strictly increases table visits for every table/query |

For table length t and query pair counts L/R, `lookup_bound` gives

```text
table visits       <= t + 1
comparison visits  <= t * ((2*L + 1) + (2*R + 1))
copy visits         = 0 on a miss, 2*W + 1 on a hit
Box creations       = 0 on a miss, 2*W on a hit
result-copy packets = 0 on a miss, 1 on a hit
```

W is the **returned** witness's pair count. An unsound table with empty keys
can store a large witness, so query size alone does not bound copying. Under
the existing `TableSound` predicate, the independent contraction theorem gives
`W <= min(L,R)`. With unit prices for all five packets, the composed bound is

```text
t * (2*L + 2*R + 3) + 4*min(L,R) + 3.
```

## Executed verification

From `proofs/`:

```bash
lake build
lake env lean Tests/LookupEvents.lean
lake env lean Tests/RootedDynamicProgram.lean
lake env lean Tests/OrderedIsomorphism.lean
lake env lean BaselineAudit.lean
```

The full library passes **3,744 jobs**; all three example suites pass. The ten
new kernel-reduced examples cover empty/missing/first/last hits, duplicate keys,
both short-circuit levels, long equal keys, oversized unsound witnesses and an
extra scan. CI now runs this suite. The seven newly audited public endpoints
depend only on the accepted baseline `propext`, `Classical.choice`, `Quot.sound`.
There are no proof placeholders or new axioms in this increment.

Source SHA-256:

```text
6bf420368c037348b65a3c20d14c2fe54aee2b55e6ac4b5b6eb3baef4b11eaf1  rust/crates/verified_ordered_core/src/lib.rs
b6a57c5b06aedbcde4c414bbb1f7efe7f14ccea34448f29c918051959e6a051a  proofs/SubtreeProofs/Rust/Generated/VerifiedOrderedCore.lean
0ac20d4941cd6a02d869d22f3926ee0bf8990ba4021a13b0f70d19d5524ec164  proofs/SubtreeProofs/Rust/LookupEvents.lean
```

## Remaining source obligation and decision

The subsequent [reified lookup pilot](lookup-source-pilot.md) adds a checked
operational interpreter, universal value/event correspondence inside that
model, and a compiled Rust extra-comparison mutation. Its Python reifier and
immutable-reference interpretation remain trusted; SRC-01/C3 and full G1 are
still open. The paragraph below records the boundary of this earlier increment.

The four erasure theorems establish **functional** correspondence. They do not
prove that every operation in Rust/LLBC execution emits its packet, or that
packet prices bound that execution's work. The event interpreter was written
manually; the cost interpretation has not been certified by the compiler or a
source operational semantics. A source mutation adding a scan must eventually
invalidate a **source adequacy** certificate, not merely make the model's
`lookupTwice` counter larger. That acceptance condition is still open.

This increment discharges the proposed mathematical packet envelopes and their
value-erasure obligations. It leaves G1's stop condition in force: do not grow
a generic memo backend on the strength of these erasure theorems. Next, obtain
a bounded source/LLBC event interpretation for these same functions, with
explicit handling of local control, structural access and allocation. Reuse
the existing arlib realization or upstream semantics where its concrete types
fit; no competing backend has been selected by this increment.
