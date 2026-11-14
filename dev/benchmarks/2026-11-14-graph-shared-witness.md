# Share memo witnesses and reduce graph heap traffic, 2026-11-14

Source follows `b862520`; graph baseline is the unchanged fixed-root core from
`c6906f8`. New Release wheel SHA256:
`da933d265ddb389f4cb04a2250d341f7c5c5ba7090bd08d616bcd63afdb7903c`.
Python 3.13.2, Rust 1.95.0, same shared Linux VM and benchmark configuration.

Memo results and skip states now share immutable original-node vectors through
`Rc`; score adjustments no longer copy whole witnesses. Rooted combinations
reserve their exact output length, leaf states avoid empty child matrices, and
skip transitions iterate over borrowed input edges without temporary vectors.
Cache keys encode absent parents with an impossible node index, reducing four
optional-parent coordinate words to four ordinary words while retaining the
explicit parent types in the recurrence. Public results still own ordinary
vectors, moved out after the memo tables are dropped. The recurrence, scoring,
tie comparison and public witness representation are preserved.

The new `graph_allocations` benchmark wraps the system allocator **only inside
that executable**. Counts include allocation/reallocation calls and requested
sizes; peak extra live requested bytes exclude input allocations established
before each solver call. These are not allocator metadata, fragmentation,
physical RSS or exact source-proved resource bounds. Instrumented runtimes
include counter overhead and are not used for the API speedup table.

| 2018 workload | Allocation/reallocation calls before → after | Total requested MB before → after | Peak extra requested MB before → after |
| --- | ---: | ---: | ---: |
| Identical 166/166 | 1,551,053 → 394,937 | 395.84 → 104.39 | 94.46 → 51.32 |
| Wrapped 166/214 | 1,717,821 → 394,938 | 450.79 → 117.23 | 110.38 → 57.53 |
| ResNet50/101 166/319 | 3,324,757 → 792,809 | 818.76 → 209.98 | 193.05 → 106.17 |
| Star 32/32 | 1,179,040 → 94,005 | 88.52 → 36.06 | 2.58 → 2.06 |

Decimal MB above. On the largest case this removes 76% of allocation calls,
74% of cumulative requested bytes and 45% of peak extra requested heap. The
chain64 isomorphism peak is nearly unchanged (5.91 → 5.86 MB), so memory
improvement is workload dependent. All ten rows are retained in the
[before](2026-11-14-graph-allocation-baseline.jsonl) and
[after](2026-11-14-graph-allocation-shared-witness.jsonl) artifacts.

Five-repeat installed public-API medians, including original-node/path witnesses:

| Workload | 2016 seconds / speedup | 2018 seconds / speedup |
| --- | ---: | ---: |
| Chain 32/32 | 0.001008 / 1.15x | 0.003075 / 1.54x |
| Star 32/32 | 0.000667 / 1.32x | 0.118776 / 1.33x |
| Balanced 32/32 | 0.000961 / 1.17x | 0.003576 / 1.50x |
| Random 32/32 | 0.000950 / 1.24x | 0.004039 / 1.56x |
| Identical 166/166 | 0.006898 / 1.23x | 0.196926 / 1.37x |
| Wrapped 166/214 | 0.007898 / 1.34x | 0.209171 / 1.44x |
| ResNet50/101 166/319 | 0.015535 / 1.17x | 0.457808 / 1.35x |

[All 156 API/raw/oracle rows and machine/binary metadata](2026-11-14-unordered-shared-witness.json).
Comparison is to [the fixed-root artifact](2026-11-14-unordered-fixed-root.json).
Shared-VM noise remains visible in individual samples, particularly larger raw
calls. Whole-process RSS high-water mark falls 271 → 166 MiB; this includes
Python, fixtures and rescorers across the full run, not just one solver.
Every public witness was independently rescored outside the timed region.

Validation: all **41 Rust graph tests**, including exhaustive matching,
Prüfer-tree and path witnesses, plus **149 installed-wheel tests, zero skips**
with compiled backends required. Signed/forbidden callback-table objectives
continue to agree with independent exhaustive Python. No new Lean source or
complexity theorem is claimed. Specialized 2016 matching and the optimized
2018 path schedule remain open.

```bash
cargo bench --locked --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml \
  --bench graph_allocations
# Outside the checkout, using the installed Release wheel:
python /path/to/checkout/dev/bench_unordered_apis.py \
  --sizes 4,8,16,32 --repeat 5 --warmup 1 --module-trees --json results.json
```

To reproduce allocation counts before the change, run the same benchmark
executable source against `tree.rs` at `b862520` in an isolated source copy;
the matching, fixture and library interfaces are unchanged.
