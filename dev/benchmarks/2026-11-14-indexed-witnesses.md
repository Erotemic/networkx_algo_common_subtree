# Indexed witness and guided reconstruction measurements: 2026-11-14

Source semantics: `b1cd433`; this commit adds only the benchmark driver and
measurement artifacts. Rust 1.95.0 (`59807616e`, LLVM 22.1.2), default optimized
Cargo bench profile (opt-level 3, no LTO override), no added features or custom
RUSTFLAGS. Linux x86-64 KVM VM, kernel 6.8.0-147-generic, exposing 12 Intel Core
i9-11900K CPUs at 3.50 GHz. This shared VM was not isolated or frequency-pinned.
All algorithms are single threaded.

Each case/mode runs in its own process, with one warmup and five measured
executions. The table reports medians; all 150 raw samples are in
[the timing CSV](2026-11-14-indexed-witnesses.csv). `/usr/bin/time -v` records
process user/system CPU and peak RSS for each of the 30 processes in
[the resource CSV](2026-11-14-indexed-witness-resources.csv). These small sample
counts provide descriptive measurements, not confidence intervals or complexity
evidence.

`reference` calls the actual public backtracking indexed entry point; `guided`
calls the actual public shared-memo guided indexed entry point. Both full timers
include optimization, numbering, reconstruction and the internal cache's
destruction, and exclude input construction and returned witness destruction.
`witness` runs the actual guided helpers on both inputs after optimization and
numbering. Its timer includes feasibility queries, their shared cache updates,
and witness reconstruction; it excludes initial optimization/numbering and the
final cache's destruction. These phase measurements use a separate run, so
they should not be subtracted from full timings as an exact decomposition.
Process peak RSS includes setup, warmup, all five samples and destruction;
it is not a per-invocation live-heap or allocation count.

| Case | Edges L/R | Reference full ms | Guided full ms | Guided witness ms | Witness calls | Memo before → after | Guided process peak KiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| chain12 | 12/12 | 0.3394 | 0.3932 | 0.0378 | 50 | 169 → 169 | 2304 |
| chain24 | 24/24 | 8.0316 | 8.7672 | 0.6974 | 98 | 625 → 625 | 3456 |
| chain48 | 48/48 | 382.8808 | 400.3904 | 21.0225 | 194 | 2401 → 2401 | 12032 |
| star24 | 24/24 | 8.7415 | 9.3254 | 0.8202 | 98 | 625 → 625 | 3456 |
| chain_star24 | 24/24 | 10.6197 | 10.6855 | 0.0129 | 6 | 625 → 626 | 3200 |
| binary4 | 30/30 | 10.3624 | 11.4316 | 0.6860 | 122 | 961 → 961 | 4608 |
| binary5 | 62/62 | 395.7341 | 422.8220 | 23.2061 | 250 | 3969 → 3969 | 23168 |
| broom24 | 24/24 | 4.4343 | 4.9749 | 0.3645 | 98 | 625 → 625 | 3456 |
| caterpillar24 | 24/24 | 635.7037 | 650.7425 | 8.2475 | 98 | 5080 → 5080 | 13056 |
| unequal_chain_star | 12/24 | 1.3494 | 1.3559 | 0.0057 | 6 | 325 → 326 | 2560 |

The paired calls are bounded by `2*(left_edges+right_edges)+2`, as follows
from the compiled actual-helper theorem. Identical self cases hit that bound;
chain/star optima use only six witness calls. Their one added memo entry is an
actual feasibility query outside the original shape optimization table. Thus
the initial D-product bound alone is not a complete bound for the guided
wrapper's combined memo. Combined key-space and structural-copy proofs remain
open.

The new implementation is approximately 0–16% slower in these full-run medians;
these cases do not demonstrate a wall-clock improvement over backtracking.
For chain48, reference samples range from 339.0 to 439.4 ms and guided samples
from 360.0 to 444.7 ms, illustrating the VM variability. The linear witness-call
bound does not bound feasibility table scans or copies. The 24-edge caterpillar
has 5,080 actual memo entries versus 625 for chain24, and takes substantially
more time despite the same edge count. State count and structural representation
remain material costs. Allocation counts, larger scaling experiments, repeated
isolated runs and complete published running-time bounds are still pending.

Reproduce an individual mode with:

```bash
cargo bench --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml \
  --bench indexed_witnesses -- chain24 guided
```

The first argument can be any case in the table and the second is `reference`,
`guided` or `witness`. For resource measurements, build with `--no-run`, then
invoke the reported executable directly under `/usr/bin/time -v` with those two
arguments. This excludes Cargo and compilation from recorded process RSS.
