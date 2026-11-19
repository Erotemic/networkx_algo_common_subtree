# O00: exact-score extraction spike

Completed 2026-11-18 with the repository's pinned Charon/Aeneas release
`nightly-2026.11.09-5a392f4` and Lean 4.35.0. This is a standalone extraction
experiment, not a new Python backend or a proof of the complete fast solver.

## Result and arithmetic boundary

The maintained [Rust example](score_model.rs) uses a native `Score(f64)` wrapper.
Charon makes **only** `score_model::arithmetic` opaque. Aeneas translates the
real callers `improve` and `level_step`, including strict comparisons, empty
initialization, right-before-left tie order, positive-affinity guard and the
two additions. Four hand-maintained external definitions interpret zero,
addition, positivity and comparison over `ℚ`; the opaque type is an abbreviation
for `ℚ`. No generated template axioms are imported or retained as models.

This establishes an exact-arithmetic interpretation of the extracted control
flow. It does **not** establish that native `f64` implements the rational model.
The exact model deliberately has neither NaN/infinity nor rounding. The Rust
test `integral_float_inputs_do_not_imply_exact_sums` demonstrates the distinction:
`2^53 + 1` rounds to `2^53` natively, whereas a kernel-checked Lean example
returns `2^53 + 1` and selects the strictly better witness.

The same source extracted without opacity is rejected by pinned Aeneas at
float operations (`Invalid inputs for binop`, and float-constant diagnostics).
The regeneration script requires both successful abstract extraction and this
specific native rejection, so an unrelated compiler failure is not counted as
confirmation of the boundary.

## Checked endpoints

In namespace `SubtreeProofs.Rust.ScoreModel`, in
[Correctness.lean](../../SubtreeProofs/Rust/ScoreModel/Correctness.lean):

- `improve_eq`, `improve_tie`: exact returned candidate and first-witness ties.
- `level_step_eq`: total success and exact candidate identity for the Rust step
  under rational primitives.
- `level_step_score`: maximum among zero, the two deletion candidates and,
  precisely when affinity is positive, the matched head/tail sum.
- `level_step_preserves`: any invariant established for all eligible candidates
  is retained by the actual translated selection. Its candidate-invariant
  premises are explicit; this is not a completed tree-feasibility proof.
- `level_step_recurrence_score`: when the deletion candidates have the
  mathematically correct child scores and the matched child scores come from
  `AffinityDP.level`, the actual step has the independent recurrence's optimum
  score. Production state/memo/arena correspondence is still required.

The new endpoint axiom closures contain only `propext`, `Classical.choice` and
`Quot.sound`. No new arithmetic or opaque-function axioms are used. Existing
whole-forest optimum theorems also compile at `ℚ` and `ℤ` in the regression suite.
The shared `leanq` exporter audited all 45 declarations in the five new modules
(including 22 theorem declarations with generated equations/injectivity facts).
Its statement closure for `level_step_recurrence_score` contains 197 records,
594 edges and no unknown references. A redundant whole-library inventory was
stopped after about four minutes; no full fresh inventory result is claimed.

## Reproduction

Run cache setup from the repository root before compiling:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
dev/regenerate_rust_lean.sh --score-model-only --check
```

Run Lean commands **from `proofs/`**:

```bash
lake build
lake env lean Tests/ScoreModel.lean
lake env lean Tests/OrderedIsomorphism.lean
```

For the focused axiom audit, reuse the shared exporter from `proofs/`:

```bash
printf '%s\n' SubtreeProofs.Rust.ScoreModel.Correctness > /var/tmp/subtree-score-model-modules.txt
lake env lean --run ../submodules/aiq-lean-formalization-tools/src/leanq/lean/decl_index.lean \
  SubtreeProofs.Rust.ScoreModel /var/tmp/subtree-score-model-modules.txt full
leanq --project . statement SubtreeProofs.Rust.ScoreModel.level_step_recurrence_score --json
```

The focused regeneration command compiles and tests the Rust example, checks
the expected native extraction rejection, and compares both generated Lean
files byte for byte. Omit `--check` to regenerate. The ordinary full
`dev/regenerate_rust_lean.sh --check` includes the spike, and CI runs its Lean
tests. Only `Types.lean` and `Funs.lean` are generated; `TypesExternal.lean`,
`FunsExternal.lean` and `Correctness.lean` are maintained. The experiment has no
Cargo/Lake manifest of its own, runtime dependency or Python dispatch change.
Compiler outputs live in VM-local `/var/tmp`, not beside the Rust source.

The local execution passed the 4,365-job main library build, six Lean examples
(four actual-step cases and two exact-domain instances), the existing ordered
isomorphism suite, two Rust tests and regeneration comparison. Logs on this VM
are under `/var/tmp/subtree-score-model-spike/`: `regeneration.log`,
`lean-build.log`, `library.log`, `lean-tests.log`,
`existing-isomorphism-tests.log`, `axioms-scoped.jsonl` and `statement.json`.
No installed-Python benchmark is claimed: production behavior did not change.

## Decision for O01 and remaining work

Use a narrow score interface for the pure ordered kernel. Keep Python affinity
callbacks/conversion outside its algorithmic representation, while preserving
the current lazy callback/error behavior. The production kernel must remain
the implementation being extracted; do not replace it with an unrelated Lean
or Rust reference solver. The spike validates the arithmetic interface route,
not extraction of production `FxHashMap`, state interning, callbacks or loops.

Retain the float implementation as empirically supported. For an exact Python
guarantee, supply real integer execution (checked overflow/rejection is an
acceptable explicitly supported domain), or prove and enforce a range where
every intermediate is exact. Integral callback values alone are insufficient.
Integer/rational mathematical models do not remove that implementation task.

Next is O01: separate the actual score/choice/state kernel from PyO3, extract
it with explicit primitive contracts, retain original token IDs and measure
the installed path. The initial 100–300k-token / 1–4-hour range remains rough;
arithmetic extraction risk is reduced, while dictionary/state/callback and
ownership extraction remain untested. O02/O03 then connect that real kernel's
memo and witnesses to the independent rooted/general optimum specifications;
O04 delivers the exact-domain Python interface and comparative benchmarks.
Running-time proofs remain deferred.
