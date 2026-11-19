# Actual owned score choice and declared destruction work: 2026-11-17

Baseline: `8ac86d7`. Four maintained `SourceEvalChoice*` modules establish
universal source/native correspondence for the actual `choose_longer` body, including a live losing-value drop. The six previous
helper contracts are reused through the preceding bridge; no previous helper
algorithm is reproved. Whole-evaluator/public-core and addressed live-destruction obligations
remain open.

## Actual source and functional behavior

`Choice.actual_body` kernel-checks the complete retained source body against
the proposed maintained control term. It retains all storage markers, copied
scores, bounded scalar comparison, moved boolean switch, both winner moves,
conditional drops of both inputs, cleanup and return. Only the losing input
remains live at the drops. The winner is moved into the return local. There
are no recursive calls or new allocations in this function.

`body_exec` computes the complete result and cost for every pair of native
`CommonEmbedding` values and any callee interpretation. `run_body` adds the
function-entry charge. `source_run` consumes the actual-body identity;
`source_execute` binds the result to the retained JSON reader. Every positive
nesting fuel suffices. `source_native` reuses the existing independent
`OrderedSolver.selectResult` and translated Rust `choose_longer_correct`.
`first_on_tie` preserves the first witness when scores agree, even if their
words differ.

Stored scores need not agree with word sizes. Only the actual native `u32`
width is used for scalar copies/comparison. This keeps the helper applicable
to arbitrary stored witnesses, without adding a cache-soundness premise.

## Exact declared work

For a native word with `n` pairs, `word_dropWork` proves `4n + 1` visits and
`2n` Boxes in the partial-local destructor currency. `result_dropWork` adds
the embedding node and scalar, giving `4n + 3` visits and `2n` Boxes.

Let `n` be the losing witness word's semilength. `cost_exact` proves:

| Returned currency | Exact value |
| --- | --- |
| Complete source work steps, including entry and declared drop visits | `30 + 4n` |
| Destructor visits | `4n + 3` |
| Destructor Boxes | `2n` |
| Allocation, lookup, comparison, copy and result-copy events | all zero |
| Evaluator calls | zero |

The fixed source work before adding visits is 27. The scalar comparison is
charged through its expression/instruction work; lookup's structural word-
comparison event is not used. The discarded witness's *word structure*, rather
than its supplied score, determines the destruction work. These equalities
retain all cost components.

This is the existing source-operation/partial-local currency. It is not an
instruction-by-instruction interpretation of opaque Rust drop glue, a wall-time
bound, physical deallocation, peak residency or allocator safety. Addressed
typing/owners/storage/local-borrow/destruction simulation for this profile and
the evaluator remains required. D12's scoped runtime boundary is unchanged.

## Verification

The aggregate library imports the source/native API and CI runs
`Tests/SourceEvalChoice.lean`. Closed consumers cover distinct-word ties and
inconsistent word/score inputs with exact work/Box counts; a universal consumer
retains translated-native agreement and actual source decoding/execution.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceEvalChoice.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Validation passes:

- Full library: 3,877 jobs; the actual-body kernel certificate took 87 seconds.
- All 27 Lean suites, native WP example and nine Python reifier tests.
- 634 distinct audited endpoints, including ten new endpoints, with axiom
  closures within `propext`, `Classical.choice`, `Quot.sound`.
- Shared `leanq` statement inspection of `source_native` and `cost_exact`:
  706 records, retaining actual program/native execution and complete
  structural cost components, with no word/score consistency premise.
- New modules have no warnings; `git diff --check` passes.

Local evidence: `/var/tmp/subtree-eval-choice-{full-build,cert,regression,axioms}.log`
and `/var/tmp/subtree-eval-choice-statements.{json,txt}`. Rust/generated inputs,
parser/interpreter implementation and all pins remain unchanged. The preceding
`6137120` full regeneration and thirteen Rust tests remain the unchanged
provenance/behavior baseline.
