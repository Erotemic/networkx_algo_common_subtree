# Actual concatenation and insertion source bridge: 2026-11-17

Baseline: `9203cee`. This is the next W06-C3 source-composition increment after
[scoped lookup](lookup-region-erasure.md). It adds actual retained Charon
source for concatenation and memo insertion, kernel-checked normalization,
successful native-input execution, agreement with the existing translated Rust
functions and independent append/prepend models, and explicit operation counts.
It does not transfer lookup's addressed heap/owner/loan theorems to these new
functions. The memo evaluator/core and wrappers remain open.

## Reused semantics and source provenance

`LookupSource.Action`, `Code`, primitive execution, budgets and control
`Action`/`Block`/normalization are now polymorphic in the call-target type. Their
default remains the original lookup function set. `Control.exec_lower` proves
complete value/outcome/cost equality for any call-target type. Existing lookup
readers, generated files and all lookup refinements continue to use the same
operations, costs and public statements specialized at their original targets.
One test of a call-free destruction action supplies an explicit lookup callee
type to disambiguate the generalized API; its assertion is unchanged.

`Frontend.actionWith` and `sequenceWith` factor the existing checked parser
through a supplied callee resolver and arity. The old parser is the specialization
at lookup's resolver. The new reader reuses place/operand/rvalue/switch/unwind
validation and the control preservation theorem; there is no second primitive
or statement interpreter with subtly different behavior.

`dev/regenerate_memo_source.py` invokes pinned Charon on maintained
`verified_ordered_core::memo_insert` and `verified_ordered_core::concatenate`
with the existing Aeneas preset, Rust nightly 2026-09-17 and non-deduplicated AST.
It uses the existing configurable renderer and source-data emitter. These
produce `Generated/MemoSourceProgram.lean` and `MemoSourceInput.lean`.
Only output destinations are normalized in retained JSON. Source statements,
spans, declarations, local types/regions, generic arguments and unwind metadata
are retained. This is a distinct extraction, not a splice of old lookup data.

The source JSON SHA-256 is
`e6c074f15f1d5188cfb3b3ca84585ce0b367bb0e718d23a1524f4156ab8bc12a`;
proposed normalized code SHA-256 is
`9bc92a64c3e570d809c90fd162798ee261fb7210182fbe0ee0dd447a0ef307f9`.
The schema remains 0.1.315 and all dependency/toolchain pins are unchanged.

| Function | Extracted ID | Arguments | Locals | Body region binder count |
| --- | ---: | ---: | ---: | ---: |
| memo insert | 11 | 4 | 15 | 33 |
| concatenate | 12 | 2 | 13 | 30 |
| copy word | 22 | 1 | 10 | 19 |
| copy result | 23 | 1 | 6 | 10 |

`MemoSourceFrontend` resolves exact root helper identities and generic Box,
rejects duplicate identities, unsupported calls/control and wrong arities,
checks canonical local slots and signatures, and distinguishes insertion's
owned table input from its three shared inputs. The reader does not yet prove
static field typing or region scope for this new function set. Merely retaining
those annotations does not certify them.

`MemoSourceCertificate.original_read` and `original_lower` reduce the actual
source read and each proposed body in the Lean kernel. `original_exec` transfers
arbitrary callees/environments; `original_run` transfers every fuel/function/
argument list, preserving failures as well as complete successful cost pairs.
The Python reifier is not trusted for these normalizations. Charon/data import
and the declared normal-path snapshot primitive semantics remain boundaries.

## Successful execution and independent outputs

`MemoSource` has its own function set: copy word, copy result, concatenate,
insert and Box. It uses the existing polymorphic instruction interpreter and a
single recursive call driver. Every function entry costs one step, and Box
creation has its existing allocation event. Lookup's existing event fields
retain their meanings. Concatenation/insertion entries introduce no new marker
in that projection; all their local instruction work remains in `Cost.steps`.
No theorem equates this projection alone with total runtime.

`MemoSourceRefinement.copy_source`/`copyResult_source` establish successful
execution of the actual new helper bodies with the original structural-copy
events. `concatenate_source` follows the actual recursive tail concatenation
and head copying, producing the independent `OrderedSolver.appendWord`.
`insert_source` returns exactly the independent table prepend with the supplied
owned table as tail, after copying both keys and the supplied result. Invalidating
local moves and conditional moved drops remain part of the executed body.
There is no table-soundness, unique-key, optimal-witness or score-consistency
premise; duplicate keys and arbitrary cached witnesses remain supported.

`concatenate_checked` and `insert_checked` retain actual source execution and
complete cost while also proving agreement with the existing Aeneas-translated
`concatenate`/`memo_insert` functions. Existing functional correctness proofs are
reused; they are not substituted for source work preservation.

Sufficient fuel is explicit and controls call nesting, not work:
`concatenateDepth Empty right = wordHeight right + 1`, and the Pair case is
`1 + max (wordHeight head) (concatenateDepth tail right)`.
`insertDepth` is one plus the maximum of the two key heights and the result
word height plus one. The theorems construct actual successful executions at
these depths. The owned table's length does not affect insertion's local work.

## Resource endpoints

Let `L`, `R`, `W` denote the semilengths of the two input words and result word.
`insertEvents_exact` proves exactly `2*(L+R+W)+3` copy-node visits,
`2*(L+R+W)+2` Box creations and one result-copy entry, with zero lookup/compare
visits. In particular, neither copying an arbitrarily large cached witness nor
copying keys is priced as a constant operation.

`concatenateEvents_bound` proves exactly `2*(L+R)` Box creations and at most
`2*(L+R)+1` copy-node visits, with zero lookup/compare/result-copy entries.
Recursive concatenate visits are retained in instruction costs, not added to
the copy-node projection. A final instruction envelope and addressed allocation/
space theorem for these new functions remain separate obligations.

## Validation

The main 3,829-job build, all seventeen Lean suites, native WP example, nine
Python frontend tests, thirteen ordered Rust tests and 430-endpoint axiom audit
pass. The sixteen new audit closures use only the accepted baseline axioms;
new modules have no warnings. Full `dev/regenerate_rust_lean.sh --check` passes,
including both original Aeneas crates, old lookup/mutant files and the new
concatenation/insertion files. No maintained Rust, existing generated file or
pin changes are required. Shared `leanq` inspected the two new checked
endpoints' elaborated statement closure (525 records), confirming sufficient
fuel as the only extra precondition, actual source execution, translated-Rust
agreement and explicit events, without cache-soundness premises.

`Tests/MemoSource.lean` is in CI. Reader fragments distinguish owned/shared
table input, exact/nested helper identity and four-argument call arity. Source
execution examples exercise nonempty concatenation and insertion into a warm
table with a duplicate key and an intentionally inconsistent witness score.
They check actual success and explicit copy/allocation counts. Exhausted fuel
fails explicitly. The JSON fragments are not claimed to be compiled Rust
mutations; complete actual extraction is checked separately by the certificates.
The Python tests retain the original seven cases and add configurable helper
identity/arity/namespace and missing/nested-root cases.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/MemoSource.lean)
(cd proofs && lake env lean BaselineAudit.lean)
dev/regenerate_rust_lean.sh --check
python3 proofs/checks/test_lookup_source_reifier.py
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
```

## Next required composition

Extend addressed execution and the checked type/owner/storage/loan/region
invariants to these actual bodies, including transfer of the owned input table.
Then add the actual memo evaluator: it additionally borrows owned local tables,
results and contracted words, performs checked arithmetic, returns a table on
overflow and discards losing candidate witnesses. Reuse the existing independent
memo correctness/evaluator bridge. Do not require all new borrows to point into
the initial caller heap: that stronger lookup-only profile excludes legitimate
local borrows here. Establish their actual scopes and frame/owner interaction.

One public core entry point, normal work and input/error policy, then indexed/
token/reconstruction wrappers and G3 adversaries still follow. Runtime/compiler,
physical provenance, unwinding and physical space claims remain explicit
boundaries. This advances W06-C3; it does not close C3, SRC-01, MEM-04, APP-01 or
the full planning goal.
