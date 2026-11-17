# Actual memo evaluator: partial local initialization: 2026-11-17

Baseline: `1db724d`. Three maintained `SourcePartial{Value,Moves,Locals}`
modules establish partial-field move and declared destructor-work primitives
needed by the actual memo evaluator/public entry point. They preserve independent
mathematical specifications and the completed helper proofs. This increment
is not an actual evaluator source-normalization or addressed-safety certificate.

## Inspection of the actual pinned extraction

The pinned Charon/Aeneas-preset extraction rooted at
`verified_ordered_core::maximum_common_embedding` was inspected, retaining the
original serialized AST rather than its value-only translation. The maintained
Rust file SHA-256 is
`6bf420368c037348b65a3c20d14c2fe54aee2b55e6ac4b5b6eb3baef4b11eaf1`.
The temporary extraction and log are `/var/tmp/subtree-memo-evaluator.llbc` and
`/var/tmp/subtree-memo-evaluator-extract.log`.

The evaluator has 113 declared locals. Its normal blocks, counting all branch
arms but excluding unwind cleanup, contain 521 statements: 160 storage-dead,
121 storage-live, 114 assignments, 79 conditional drops, 16 calls, 16 borrow-check
annotations, 10 switches, four returns and one undefined-behavior leaf. These
are inspection counts, not execution bounds or kernel source certificates.
`Use` assignments alone include 15 projected moves. All normal evaluator drop
places are whole locals. `choose_longer` has six locals and 20 normal statements;
the public entry point has seven locals and 18. Its projected move returns the
option field of the evaluator's tuple and drops the remaining table.

This exposes requirements absent from the helper fragment: partial field moves,
live conditional destruction, scalar comparison/constants, opaque checked `u32`
addition, caller-owned-local borrows, recognized borrow-check annotations and
proof that the undefined-behavior leaf is unreachable for supported inputs.
Unwind cleanup additionally contains termination markers. These features must
receive explicit supported semantics/profile checks; they cannot be silently
erased or treated as moved-only drops.

Reproduce the inspection extraction with the pinned binary directory:

```bash
cd rust/crates/verified_ordered_core
RUSTUP_TOOLCHAIN=nightly-2026-09-17 "$AENEAS_BIN_DIR/charon" cargo \
  --preset=aeneas --start-from verified_ordered_core::maximum_common_embedding \
  --no-dedup-serialized-ast --dest-file /var/tmp/subtree-memo-evaluator.llbc
```

`AENEAS_BIN_DIR` is the pinned release described in `proofs/VERIFICATION.md`.
This extraction is diagnostic evidence; no new generated Lean file is edited or
claimed certified by its hash.

## Partial values and exact transfer

`Partial.Slot` extends local initialization state with holes at subfields.
Nodes retain their constructor and remaining fields. A Box retains its shell
when its payload is moved. Shared referents are immutable snapshots, and moving
through a shared reference is rejected. This is a maintained program semantic
component, not a new source-analysis tool or duplicate source parser.

`ofValue` embeds the existing full source values. `materialize_ofValue` proves
readback; `eq_of_materialize` proves that a successfully materialized slot is
exactly its full embedding. A partially moved parent cannot be materialized or
moved as a whole, while its initialized siblings remain available.

`Slot.take_read`, `take_hole` and `take_otherField` prove that a successful
projected move reads the selected full value, leaves a hole at that exact path,
and preserves every distinct sibling projection (including any suffix).
Bounds and variant mismatches fail. A move cannot cross a shared reference.

`DropWork` records declared logical destructor visits and Box tokens. Empty
fields contribute zero; a shared pointer contributes one visit and zero Boxes,
without traversing its referent. A Box shell contributes its own visit/token
even after its payload is moved. `take_work` proves componentwise exact transfer:

```text
before.dropWork = ofValue(moved).dropWork + remaining.dropWork
```

This counts occurrences, not sets. It is a logical source-destructor currency,
not a claim of an exact Rust drop-glue instruction count, allocator cost, freed
heap bytes or physical time. Addressed identity/uniqueness and an actual source
call/drop interpretation remain required when connecting these primitives.

`Locals.move_spec` lifts selection, hole and work-transfer facts to actual
local environments. `move_other` preserves every other local. `drop_spec`
clears exactly one whole local and returns its complete remaining work;
`drop_twice` charges zero on the second drop. `move_local_lift` proves unchanged
whole-local move behavior against the existing source interpreter, including
the complete resulting environment. Existing storage status/type/ownership and
loan invariants are still separate and must be composed for the evaluator.

## Validation and next work

The 3,858-job build passes, as do all 24 CI Lean suites, native WP and nine
Python reifier tests (26 command checks). The opt-in audit reports 572 distinct
endpoints; all 20 new closures remain within `propext`, `Classical.choice` and
`Quot.sound`. New modules/tests have no warnings; existing unrelated warnings
remain. Shared `leanq statement` inspection of `Slot.take_work` and
`Locals.move_spec` produced 60 elaborated statement records, confirming the
actual selected-value/remaining-work and complete local-update statements.
This supplements Lean checking and the axiom audit.

Rust, generated artifacts, parser/reifier and pins are unchanged. Build caches
were checked as VM-local ext4 bind mounts. Local logs are
`/var/tmp/subtree-source-partial-{full-build,regression,axioms}.log` and
`/var/tmp/subtree-source-partial-statements.{json,txt}`.

```bash
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourcePartial.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement \
  SubtreeProofs.Rust.LookupSource.Partial.Slot.take_work \
  SubtreeProofs.Rust.LookupSource.Partial.Locals.move_spec \
  --root-module SubtreeProofs.Rust.SourcePartialLocals
```

The suite checks retained siblings/constructor tags, rejected partial-parent and
repeated moves, bounds/variants, exact remaining work, moved Box payloads and
retained shells, readable shared referents with rejected moves, unrelated locals,
conditional destruction/idempotence and old whole-local compatibility.

Next consume these primitives in actual evaluator source normalization and
execution, with scalar/checked-add semantics, recognized metadata/unreachable
control, owned-local addressed borrows and full safety/cost composition. Then
compose `maximum_common_embedding` including destruction of its returned table,
other wrappers, input/error policy and G3 adversaries. W06-C3, SRC-01, MEM-03/04
and the full planning goal remain open. Do not duplicate completed helper
storage/guard/spatial/loan/region work or invent a whole-compiler gate.
