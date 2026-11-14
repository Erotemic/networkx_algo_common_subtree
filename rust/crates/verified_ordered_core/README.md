# Verified ordered-tree reference core

This safe Rust crate represents an unlabeled balanced word by an empty case or
a matched pair's interior and suffix. Every value is balanced by construction.
The singleton tree has the empty word and edge score zero.

`largest_common_embedding` returns a structural witness and an exact `u32`
edge count using the 2004 three-branch recurrence. It uses checked arithmetic;
`None` reports candidate-score overflow. `copy_word`, `concatenate`, and
`choose_longer` use the subset supported by the pinned Charon/Aeneas release.
Explicit Option matches avoid a missing model for Rust's `?` implementation in
that release. Generated Lean is never edited.

The Lean theorem
`SubtreeProofs.Rust.OrderedSolver.largest_common_embedding_of_trees`
proves: for every pair of independently specified finite ordered trees with
fewer than 2^32 edges each, the actual translated Rust function succeeds,
returns an independently maximum common contracted tree, and reports its exact
edge count. Both representation round trips are proved. Checked additions fit
under those input bounds; no overflow or divergence is admitted in the theorem.

`maximum_common_embedding` is the memoized entry point. Its real generated
function is certified by `Rust.MemoizedOrderedSolver.maximum_common_embedding_of_trees`.
Every cache update refines the numeric Lean memo table exactly;
`memoized_common_embedding_cache_bound` transfers the finite D-product bound
and uniqueness of cached keys to the actual Rust result. The owned association
list has linear scans and copies witnesses; it is not the paper's expected
constant-time dictionary. `largest_common_embedding` remains the independent
exponential source baseline. Both are checked against all tree pairs through
six edges.

The witness is a tree, rather than a map to original input indices.
The optimized existing PyO3 backend remains an independent baseline.
The Aeneas allocation and recursive-call model does not establish an OS-level
memory/stack budget. Performance refinement and the public input adapter remain
separate obligations; this crate is not the default Python backend.

Deterministic shape measurements are recorded in
[`ordered benchmarks`](../../../dev/benchmarks/2026-11-14-ordered-memo.md).
An independent test enumerates ordered-tree contractions directly and validates
both the optimum and returned witness. The generation/build procedure and exact
pins are documented in [`proofs/VERIFICATION.md`](../../../proofs/VERIFICATION.md).

```bash
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
dev/regenerate_rust_lean.sh --check
(cd proofs && lake build)
```
