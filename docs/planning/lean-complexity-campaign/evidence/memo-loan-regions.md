# Memo typed shared loans and source-region interpretation: 2026-11-17

Baseline: `f4a22df`. Five `MemoBorrow{Certificate,Calls,Refinement}` and
`MemoRegion{Calls,Refinement}` modules compose actual memo helper execution
with stable typed shared loans, ordinary reference-free outputs and actual
source-region annotations. The preceding [storage proof](memo-stack-initialization.md)
and guarded/spatial/returned-owner guarantees remain in the native endpoints.
The actual evaluator/core and wrappers are the next W06-C3 work.

## Shared loan semantics and checked routes

The existing `Borrow.Loan`, `Safe`, `FieldsSafe`, `EnvSafe`, place simulation and
primitive lemmas are reused. A loan retains an actual typed read in one fixed
caller heap. Every recursive helper world extends that heap immutably. Owned
values may contain loans; allocating a Box preserves its payload's existing
loans instead of asserting every Box is reference-free.

`LookupBorrowLoans.actionRoutes`/`codeRoutes`, intermediate traces and action
witnesses now accept different callee types. `CallsSafeWith`, `action_safeWith`
and `exec_safeWith` take an explicit callee type map; original lookup entry
points specialize the same theorems. The primitive interpreter and loan meaning
are unchanged.

`MemoBorrowCertificate.original_checked` kernel-checks the actual source read,
local type/argument/return constraints, normalized body correspondence and all
shared-root borrow routes for four helpers. `check_sound` produces these
contracts. `MemoBorrowCalls.run_safe` discharges recursive callee obligations
by fuel induction, retaining every actual local/temporary loan and complete
cost in `RunSafe`. `RunSafe.erases` recovers the same addressed execution.

`ordinary_loans` covers every completed ordinary call from its actual typed
inputs; insertion's first input is its owned table value. `result_unborrowed`
uses the checked output type's closure, including owned payloads. Generic Box
is deliberately excluded from this ordinary-output conclusion. Native totality
permits both keys and the witness to borrow into the table transferred under
the new tail Box; all typed caller loans survive, including unrelated loans.

## Actual region-bearing declarations

The existing memo region checker now also checks borrow routes in its parsed
declarations. `check_sound` and `Certificate.original_program_routes` retain
that stronger conclusion; `Certificate.original_program` keeps its earlier
weaker API. Actual parsing, source binder scope, static typing, code equality
and routes are kernel-certified together. Value and lifetime arities remain
distinct: insertion takes four values and has three shared lifetime parameters.

`LookupRegionCalls.trace_regional` now applies to any callee type.
`MemoRegionCalls.run_scoped` uses that shared theorem and generic loan execution
to consume each actual declaration's `CheckedFields` annotations. `RunScoped`
retains the declaration, recursive loan trace, scoped region-bearing local
interpretation and exact cost at every ordinary callee. Erasure recovers the
same run. Box remains a primitive with its loan-safe payload contract.

The reused lifetime valuation is explicitly
`callLifetime base region current = Extends base current`. Under that valuation,
checked region-bearing values and their erased typed loans are equivalent.
The trace's environment safety and the declaration's checked annotations yield
regional values at its normal instruction frontiers; the entry interpretation
is retained explicitly in `RunScoped`. Source binder validity is still needed:
the common valuation does not make an unbound source region well scoped.
A typed pointer alone also does not satisfy an arbitrary false valuation.

`source_run_scoped` composes the actual source run with a successfully parsed
scoped program, addressed execution, scoped recursive trace, safe output,
readback, extension and allocation growth. `concatenate_source_total` and
`insert_source_total` retain independent append/prepend results, native Rust
agreement, operational typing, reference-free ordinary outputs, stable caller
loans, source storage traces, owner guards, intermediate/caller separation and
complete costs/events. Concatenation owns its fresh result. Insertion preserves
the original table under the new tail and each valid separated external owner
frame. Separation remains an explicit conditional premise, independent of loan
validity and type safety.

This is the same scoped immutable source-operation boundary as the lookup
pilot. It does not model mutation/freeing, physical lifetimes, compiler/runtime
provenance, unwind paths or physical peak space. The shared-root borrow profile
also does not cover every legitimate borrow from newly owned caller locals.
The actual evaluator must extend that profile where needed; rejecting a
well-typed fresh-owned-root fragment is not a claim that the Rust borrow is
invalid.

## Validation

The full 3,855-job build passes. All 23 CI Lean regression suites, native WP
and nine Python reifier tests pass (25 command checks). The opt-in axiom audit
reports 552 distinct endpoints; the 21 new closures remain within `propext`,
`Classical.choice`, and `Quot.sound`. Existing lookup storage/borrow/region and
memo type/scope/ownership tests pass with the generalized interfaces. New
modules have no warnings; existing unrelated warnings remain.

Shared `leanq statement` inspection of `Regions.insert_source_total` and
`Regions.RunScoped` produced 791 elaborated statement records. The native endpoint
retains the actual successful region-bearing source read, source and heap runs,
scoped recursive trace, safe and reference-free ordinary output, storage/guard/
spatial traces, original-table tail, exact costs and stable caller loans. Spatial
frame preservation remains conditional. This inspection supplements Lean and
its axiom closure; it does not replace them.

Rust, generated inputs, source-control parser/reifier, toolchain and dependency
pins are unchanged; the prior pinned regeneration remains applicable. The memo
region checker is explicitly strengthened with routes as described above.
Caches were checked as VM-local ext4 bind mounts before building. Local logs
are `/var/tmp/subtree-memo-loan-regions-{full-build,regression,axioms}.log` and
`/var/tmp/subtree-memo-loan-regions-statements.{json,txt}`.

```bash
(cd proofs && lake build)
(cd proofs && lake env lean Tests/MemoBorrow.lean)
(cd proofs && lake env lean Tests/MemoRegions.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement \
  SubtreeProofs.Rust.MemoSource.Regions.insert_source_total \
  SubtreeProofs.Rust.MemoSource.Regions.RunScoped \
  --root-module SubtreeProofs.Rust.MemoRegionRefinement
```

The new suites cover retained versus merely fresh pointer validity, source
shared-root routing, loans inside primitive Box, ordinary output closure,
aliased key/witness loans into insertion's owned table, unrelated caller loans,
source/lifetime arity distinction, scoped erasure, false valuations, unbound
regions, and actual scoped concatenation/insertion calls. Existing source/type/
region rejection tests and all earlier safety regressions remain required.

Next inspect `memoized_common_embedding` in the maintained Rust source:
checked arithmetic, owned-local borrows,
losing-candidate destruction, overflow/table returns and source control. Compose
its memo evaluator and one public core, then indexed/token/reconstruction
wrappers, input/error policy, local/source work and G3 adversaries. W06-C3,
SRC-01, MEM-03/04 and the full planning objective remain open; D12 does not
require an invented whole-compiler gate before this work.
