# Verified owned-memo ordered solver: 2026-11-14

Rust 1.95.0, Cargo optimized bench profile, Linux x86-64 VM exposing 12
Intel Core i9-11900K virtual CPUs. Same hardware context as the graph-reference
baseline. Each row is one execution, without warmup; it is a smoke measurement,
not a statistical confidence interval or a published complexity certification.

```bash
/usr/bin/time -v cargo bench --locked \
  --manifest-path rust/crates/verified_ordered_core/Cargo.toml --bench ordered_shapes
```

| Shape | Edges per input | Seconds | Stored states |
| --- | ---: | ---: | ---: |
| Chain | 12 | 0.000432 | 169 |
| Chain | 24 | 0.00791 | 625 |
| Star | 24 | 0.00784 | 625 |
| Chain vs star | 24 | 0.01046 | 625 |
| Full binary, height 4 | 30 | 0.01044 | 961 |
| Full binary, height 5 | 62 | 0.36656 | 3969 |

Scores match the full input edge count except chain vs star, whose optimum
is one edge. Exact CSV rows are in the companion file. Process-wide peak RSS
was 107,144 KiB, CPU user/system 0.53/0.06 seconds, elapsed 0.63 seconds.
Those resource numbers include Cargo/compilation and are not per-row heap data.

`maximum_common_embedding_of_trees` verifies the actual translated memoized
Rust entry point. `memoized_common_embedding_cache_bound` proves the real
cache has no duplicate keys and is bounded by the proved D-product. The
linked-list cache still has linear scans and copies structural witnesses.
The comparison scaling of the Lean model includes an extra state factor;
no expected constant-time lookup or full Rust wall-clock bound is claimed.

The same Rust test run compares both source solvers against all 38,809
ordered pairs through six edges, checking the returned tree in each independent
contraction set. The debug test took 14.39 seconds for both solvers together;
that is test duration, not an isolated performance comparison.
