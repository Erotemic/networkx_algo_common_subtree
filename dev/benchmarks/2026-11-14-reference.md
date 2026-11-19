# Corrected graph-reference baseline, 2026-11-14

Source: commit `6dbf81e` (graph implementation fixed at `d188b67`).
Rust: `rustc 1.95.0 (59807616e 2026-04-14)`, optimized Cargo bench profile.
VM: Linux 6.8.0-147-generic, x86-64, 12 virtual CPUs exposing an Intel
Core i9-11900K at 3.50 GHz. Runs use shared VM hardware; these measurements
are a smoke baseline and do not establish statistical scaling or optimized
paper complexity.

Command from the repository root:

```bash
COMMON_SUBTREE_BENCH_REPEAT=1 COMMON_SUBTREE_BENCH_WARMUP=0 \
COMMON_SUBTREE_BENCH_FORMAT=jsonl /usr/bin/time -v \
  cargo bench --locked --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml \
  --bench pytorch_sized_trees
```

| Fixture | Vertices | Isomorphism seconds | Embedding seconds |
| --- | --- | ---: | ---: |
| Identical ResNet50-like trees | 166 / 166 | 0.0935 | 0.4259 |
| Wrapped convolutions | 166 / 214 | 0.0801 | 0.4234 |
| ResNet50 vs ResNet101 | 166 / 319 | 0.1909 | 0.9101 |

The wrapped-convolution embedding has weight 271 under corrected Definition 4
scoring. The per-row weights and witnesses are in the companion JSONL file.
Peak RSS for the entire Cargo invocation was 195,336 KiB; user/system CPU
3.73/0.21 seconds, elapsed 2.83 seconds. These process-wide numbers include
compilation and cannot be interpreted as per-solver allocations or peak RSS.
Allocator statistics, state/matching counts and a pinned before/after
performance comparison remain future measurements.
