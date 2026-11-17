# Checked lookup source-control certificates: 2026-11-16

Baseline: `06d2e88`. This advances W06-C3's reification obligation for the
pinned read-only lookup fragment. It does not close its typed heap/reference,
ownership, source primitive adequacy or complete memo-core obligations.

## Data and trust boundary

`dev/regenerate_lookup_source.py` now also emits `LookupSourceInput.lean` and
`LookupSourceExtraCompareInput.lean`. Each is the entire extracted JSON value,
including declaration/type tables, source text, statements, source branch
indices, spans, unwind blocks and operands. Only `options.dest_dir` and
`options.dest_file` are canonicalized to `.` and `lookup.llbc`; the Lean reader
does not consume these fields. Object ordering is canonical JSON ordering,
and each file records that canonical JSON's SHA-256. Chunked data definitions
avoid a single enormous elaborator expression. They do not filter instructions.

Extraction still uses Charon `454586e9b770231e66d2062993e632dfc06463e2`
(serialization 0.1.315), bundled with the pinned Aeneas release, and Rust
`nightly-2026-09-17`. The mutant is a fresh temporary Rust crate containing
`let _ = words_equal(left, left);` at the start of `memo_lookup`.
Production Rust and existing Aeneas/normalized-Code output are unchanged.

The JSON embedding remains a reproducible external data import, and Charon,
Rust extraction and the chosen source primitive semantics remain boundaries.
The Python **control reifier is no longer trusted for the two certified
normalizations**: a Lean reader checks retained source syntax against the
proposed normalized `Code`. This does not establish official LLBC/Rust typed
semantics merely by giving our source blocks an interpreter.

## Executable reader and semantic preservation

`Rust/LookupSourceFrontend.lean` defines a total fuel-bounded `Except` reader.
It checks extraction profile, exact root/function/type identities, duplicate
IDs and duplicate supported identities, helper signatures and body arities,
canonical local declaration indices and bounds, whole-local moves, thin shared
borrows, supported aggregate/retag syntax, direct-call identity and arity,
binary routing and the restricted unwind profile. Unsupported statements and
representations fail explicitly. It retains raw switch keys/indices/fallback,
both arms, the common continuation and distinct storage-live/dead markers.
Field/region/ownership typing is not proved by these syntactic checks.

`Rust/LookupSourceControl.lean` provides a separate source-index dispatcher
and source-block executor. They directly execute retained source routing;
execution is not defined as execution of a normalized body. Local primitives
explicitly reuse the existing snapshot `evalAction`. Conditional drops of live
owned values fail in this model. Allocation is its declared Box primitive,
not a proved heap allocator. Normal-path behavior and failure remain those
of this declared model.

The universal checked endpoints are:

- `Control.dispatch_preserves`: supported source routing agrees with lowered
  routing, including swapped arm indices and first-match duplicate keys.
- `Control.exec_lower`: lowering preserves the complete outcome and `Cost`
  for every environment and callee interpretation. Early returns skip the
  shared continuation in both interpreters.
- `Control.run_lower`: all fuels, functions and argument lists have identical
  results and complete costs, including the declared Box call primitive.
- `Frontend.check_iff`: Boolean acceptance is equivalent to successful reading
  and exact normalization for every supported helper.
- `Frontend.checked_run`: acceptance yields a source program and universal
  result-and-cost preservation, rather than equality on selected examples.

## Concrete certificates and adversary

`Rust/LookupSourceCertificate.lean` proves `original_read`, `mutant_read`,
`original_lower` and `mutant_lower` by kernel reduction. Their explicit
implementation imports expose the pinned JSON/string-ordering definitions
needed by Lean's module system. There is no native-evaluation proof oracle.

`Certificate.original_checked` and `mutant_checked` certify both actual
extractions against their respective normal forms. `mutant_rejects_original`
proves the mutant cannot receive the original normalization certificate.
`original_run` and `mutant_run` preserve complete execution/cost at every fuel.
`original_run_bound` transfers `steps ≤ 256 * events.units` to the checked
source-control execution. `mutant_violates_old_comparison_budget` transfers
the real empty-table adversary: the same returned `None`, one comparison,
and the old comparison allowance zero. This refutes that comparison component,
not necessarily the slack aggregate instruction envelope.

## Validation

The 3,770-job main build and 152-endpoint axiom audit pass; all twelve new
closures stay within `propext`, `Classical.choice`, `Quot.sound`. New modules
have no warnings. Full pinned Aeneas and four-output source regeneration pass.
See [`PROOF_STATUS.md`](../../../../proofs/PROOF_STATUS.md). Eight Lean suites
include the new `Tests/LookupSourceFrontend.lean`; its small rejection fixtures
are explicitly source fragments, not claimed well-typed complete crates.
They cover nested helper aliases, duplicate IDs/type identities, local bounds
and malformed local tables, projected moves, unsupported retag/borrow/union/
call/statement forms, code after return, invalid routing, swapped indices and
early-return versus continuation costs. The seven existing Python reifier
regressions and exact fresh four-output regeneration pass.

From the root, after VM bind-mount setup:

```bash
dev/regenerate_rust_lean.sh --check
python3 proofs/checks/test_lookup_source_reifier.py
(cd proofs && lake build)
(cd proofs && lake env lean Tests/LookupSourceFrontend.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

The historical thirteen-hash pilot ledger remains historical: the generator
changed in this increment. Main dependency pins and production Rust are
unchanged. A fresh full extraction check and canonical source snapshots
replace any inference from the old generator hash.

## Remaining W06-C3 work

This is checked **source control and snapshot primitive interpretation**.
Actual typed heap addresses, shared aliasing/lifetimes, ownership/local moves,
Box allocation/destruction and their simulation to the existing Aeneas/Rust
semantics remain open. So do unwind/failure costs, physical allocation/layout,
stack bounds and machine-time/space realization. Next connect the read-only
lookup's typed heap behavior, then insertion, concatenation, memo evaluation
and a named public core; wrappers retain separate obligations. C1 memo work,
this control certificate and functional Aeneas correctness do not by themselves
prove that combined source runtime. SRC-01, MEM-04 and APP-01 stay open.
