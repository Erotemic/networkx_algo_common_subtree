# Installed weighted graph API baseline, 2026-11-14

Source: Python/PyO3 graph integration following `4fb9227`, before matching
optimization. Python 3.13.2, Rust 1.95.0, CMake Release, Linux x86-64 shared VM
(12 vCPUs, Intel i9-11900K). The CP313 wheel SHA256 is
`b2166fa8eb60cdb6d9fb611c34f1bc3b2807826efde406868fdfc2e340f6701f`.
Its installed extension path/hash and all repeated measurements are recorded
in [the JSON artifact](2026-11-14-unordered-python-apis.json).

Reproduce after installing a Release wheel, outside the source directory:

```bash
python /path/to/checkout/dev/bench_unordered_apis.py \
  --sizes 4,8,16,32 --repeat 5 --warmup 1 --json unordered-python-apis.json
```

This run used `PYTHONPATH=/tmp/common-subtree-graph-api-install` from `/tmp`.
There are 144 measurement rows: both families, four shapes, equal and
asymmetric sizes, the complete public Rust API and raw PyO3 calls, plus the
independent exhaustive Python public API for size four. Every public witness
is independently rescored outside the timed region; all objectives agree.
Inputs use unit vertex/edge weights and a 0.25 embedding skip penalty. Times
include witness reconstruction. Raw PyO3 excludes NetworkX conversion but
includes Python/Rust value conversion; it is not an internal Rust-only timer.

| 32/32 vertices | 2016 API / raw seconds | 2018 API / raw seconds |
| --- | ---: | ---: |
| Chain | 0.00458 / 0.00445 | 0.00755 / 0.00678 |
| Star | 0.29451 / 0.29701 | 0.35959 / 0.35665 |
| Balanced | 0.00381 / 0.00376 | 0.00698 / 0.00670 |
| Random | 0.00477 / 0.00478 | 0.00839 / 0.00811 |

Five-repeat medians show a major high-degree solver bottleneck. Binding and
graph-conversion overhead is a small part of these star timings. Across the
four-vertex workloads, public Rust is 3.50–20.29x faster than exhaustive
Python (median 6.13x); that comparison is against independent enumeration,
not a polynomial Python implementation. Noise sometimes makes the full API
appear slightly faster than raw calls. These shared-VM measurements establish
a baseline, not statistical scaling, paper complexity or memory/allocations.
Callback/scoring-mode comparisons, larger realistic workloads and production
optimized algorithms remain required follow-up work.
