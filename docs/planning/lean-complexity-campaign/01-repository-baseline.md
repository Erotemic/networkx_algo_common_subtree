# 01. Repository baseline and existing proof boundaries

## 1. Reproducible input

The source is the user-supplied archive:

```
networkx_algo_common_subtree-source-2026-11-14T164724-5-4291e8bd12d6.tar.gz
SHA-256 62a06164534e701cbb39a336071c5c9b9884baee87cfd4ce7b8ab6cc76236a82
Git HEAD 4291e8bd12d693fbb0d1a6a8737ed96c5f6705e3
```

The older library audit describes its own baseline as `e272d36b09de`. That is not the HEAD of this delivered archive. Treat claims from that audit as dated observations, then compare them with the present source. The overlay changes no existing files.

The maintained Lean workspace is `proofs/`, not the repository root. It uses Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, and Aeneas `5a392f4b80a4d0d05abc240eb2a7fa70622a9a35`. Exact paths, declaration locations and SHA-256 hashes for inspected files are recorded in [repository-observations.json](evidence/repository-observations.json).

## 2. Existing 2004 cost evidence

The actual reference evaluator is in `proofs/SubtreeProofs/Paper2004/MemoizedDynamicProgram.lean`.

| Declaration | Source locator | Meaning |
|---|---|---|
| `memoFind` | lines 30--36 | Association-list lookup returning a value and number of whole-key comparisons |
| `memoFind_value` | lines 38--44 | Its value agrees with `memoLookup` |
| `memoFind_comparisons` | lines 46--53 | Comparisons are bounded by input table length |
| `MemoSound` | lines 56--57 | Every stored value agrees with independently specified `paperLcs` |
| `MemoRun`, `memoLcs` | lines 86--115 | Actual table-threading recursion and counters |
| `memoLcs_correct` | starts line 118 | Value correctness and preservation of cache soundness |
| `memoLcs_counts` | lines 191--220 | Each miss adds one entry; calls at most `4 * misses + 1` |
| `memoLcs_nodup` | starts line 315 | Cache-key uniqueness is maintained |
| `memoLcs_table_bound` | lines 360--376 | Cache cardinality bounded by a finite product of decomposition states |
| `memoLcs_operation_bound` | lines 380--388 | Explicit miss and call bounds |
| `memoLcs_tree_operation_bound` | lines 392--400 | Call bound using edge count, depth and actual leaf count |
| `memoLcs_comparison_bound` | starts line 404 | Whole-key comparisons at most calls times final table length |
| `memoLcs_comparison_state_bound` | starts line 461 | State-count specialization of the comparison bound |

For trees `a,b`, define the existing state envelopes

\[
S_a=e_a(\min(d_a,\ell_a)+1)+1,\qquad
S_b=e_b(\min(d_b,\ell_b)+1)+1.
\]

The existing declaration gives `calls <= 4 * (S_a * S_b) + 1`. The extra constants handle small/degenerate cases and should survive in exact bounds. These declarations already provide meaningful execution-linked counters for this evaluator. They should become compatibility consumers of a generic theorem; they should not be replaced by a less precise axiom that merely assumes a state bound.

They do **not** measure the cost of structural equality inside one whole-key comparison, the construction of Dyck-word keys, concatenation, cloning values, output reconstruction, or a randomized dictionary. The maintained table is an association list. A proposed generic theorem must make its representation cost explicit.

## 3. Actual Rust correspondence

`rust/crates/verified_ordered_core/src/lib.rs` contains `memo_lookup`, `memo_insert`, `memoized_common_embedding`, and `maximum_common_embedding`. The source pilot should start with the real `memo_lookup` and its callers, not a newly invented stand-in. `proofs/SubtreeProofs/Rust/MemoizedOrderedSolver.lean` and the verification documentation establish the existing functional/cached-state connection. Read their signatures before changing them.

`proofs/VERIFICATION.md` explicitly separates source correctness from runtime, allocation and stack guarantees. It also identifies the indexed reconstruction wrapper as additional work not covered by the shape-memo count. Generated files are checked by `dev/regenerate_rust_lean.sh --check` and must not be hand-edited.

The source/extraction boundary includes a pinned Rust compiler, Charon/Aeneas translation, and their primitive models. Aeneas functional equivalence does not identify a Rust program's cost with that of an arbitrary Lean function having the same output. A new resource theorem must name the instrumented semantics and show which source operations it covers.

## 4. Weighted matching is already substantially formalized

The repository's `WeightedMatching` and `Rust` areas have substantial duality, reduction, deletion, sparse search and repair correctness. The crosswalk identifies, among other endpoints:

* `WeightedMatching.IsMaximum.deleteRight` and `deletion_repair_card_bound`;
* `CopiedAssignmentReduction.initial_dual_feasible`, `initialPairs_tight`, `initial_edge_deficit`;
* `matched_deletion_ready`, `deletion_preserves_tight`, `feasible_tight_decodes`, `normalize_tight`;
* `matched_single_cycle_repair`, `matched_single_cycle_decodes`;
* `Rust.SparseSearch.augment_sparse_permutation_spec`;
* `Rust.MatchingDeletionEntrypoint.max_weight_matching_deletions_total_spec`.

These endpoints are reported by the maintained crosswalk and should be rechecked at their declarations before an implementation work order relies on them. They do not establish the optimized total operation count for the family caller.

**Terminology trap:** `proofs/SubtreeProofs/Rust/MatchingCostSpecification.lean` defines assignment **objective costs** derived from weights. Its `costAt` is not a running-time counter. A textual search for `cost` is not a complexity-proof census.

## 5. Paper obligation map

Source: `docs/planning/paper_statement_crosswalk.md`; this is repository evidence, not a fresh re-verification of every paper proof.

| Paper obligation | Existing mathematical/source support | Remaining resource obligations |
|---|---|---|
| LV2004 Theorem 3 | Corrected tree/Dyck relation, corrected state bounds, actual memo counts | Key/word costs, suitable dictionary contract, any expected hashing model, wrapper costs |
| DKM2016 Lemma 5 | Assignment reduction and substantial Hungarian/sparse invariants | Rectangular matcher operation bound under its actual data structures |
| DKM2016 Lemma 6 | Deletion reuse and repair correctness components | Whole family schedule, initialization/copy/reset costs, amortized or bounded-fiber accounting |
| DKM2016 Theorems 4/7 | Rooted recurrence and optimum correctness | Sum over concrete DP and matching invocations; source algorithm must be the optimized one |
| DKM2018 Lemmas 9/10 | Independent recurrence infrastructure; production implementations/tests | Remaining unrooted structural proofs, then schedule correspondence |
| DKM2018 Lemmas 12/13 | Production oriented views and two-pass right messages described | Valid evaluation order; maxima reuse and total matching work |
| DKM2018 Lemma 14 | Related matching mathematics available locally | `O(s^4 + s^2 t)` family cost for `s <= t` with exact work model |
| DKM2018 Theorem 15 | Written production operation argument and independent tests | Formal time `O(|T||T'| Delta)` and space `O(|T||T'|)` in the stated model |

The integer-weight improved time bounds and corresponding memory bounds have extra source qualifications. Do not infer a linear-space integer algorithm from a real-weight statement or from a citation to a different matcher.

## 6. Preserve discrepancies and API conventions

The printed LV2004 containment definition has a documented counterexample. The maintained mathematical development repairs the operational notion rather than proving a false literal statement. This campaign must retain that distinction.

The production Python/Rust APIs permit an empty score-zero result in default modes. Nonempty entry points, infeasibility, negative optima and negative-infinity mathematical weights have distinct meanings. Floating weights are not arbitrary exact reals; exact arithmetic assumptions must be limited to reached operations or attached to an explicit abstract arithmetic model. These facts affect correctness premises and sizes even when the operation-count proof itself is purely combinatorial.

## 7. What was and was not executed here

The source archive and selected local declarations were inspected, and its Git HEAD and file hashes were obtained. No Lean/Lake executable was available in this authoring environment. The previous verification results in `proofs/VERIFICATION.md` are historical repository reports; they were not rerun for this documentation overlay. No source, generated code, manifest or toolchain was changed.

The planned implementation checks are copied from the maintained verification instructions in [10-validation-and-review.md](10-validation-and-review.md). Documentation-link and overlay-integrity checks are separate and are reported with this delivery.
