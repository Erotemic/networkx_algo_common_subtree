# Installed ordered API comparison, 2026-11-14

Release CP313 wheel, Python 3.13.2, Rust 1.95.0, shared Linux x86-64 VM (12
vCPUs, i9-11900K). Installed package under
`/tmp/common-subtree-rectangular-install`; wheel SHA256
`081bc202fef69d9c9b0e05de5fe35ed78e66ed9c6140dbb8bc203d69a3b42001`.
Source follows `2437418`, with benchmark shape/affinity options added.
The Cython tuple/f64 fixes are included. All runs were outside the checkout.

Each algorithm/mode uses the same 38 cases: two existing examples, four random
cases per size 4/8/12/24, plus chains, stars, balanced forests, asymmetric
inputs and chain-versus-star adversarial shapes at each size. Seven repeats,
two warmups, seed zero. Measurements time the public balanced-sequence APIs,
including Python/Rust conversion and witness construction. They do not
include the separate NetworkX-to-sequence graph conversion. All measured
backends are required to exist, and all scores agree. Different optimal
witnesses are allowed; independent witness/oracle validation is in the tests.

| Mode / algorithm | Median legacy Rust speedup over Python | Over Cython |
| --- | ---: | ---: |
| Equality embedding | 4.43x | 3.25x |
| Equality isomorphism | 1.97x | 1.55x |
| Fractional affinity embedding | 3.87x | 3.12x |
| Fractional affinity isomorphism | 2.08x | 1.55x |
| Unweighted embedding | 4.40x | 3.52x |
| Unweighted isomorphism | 1.79x | 1.41x |

These are medians of per-case runtime ratios, not a ratio of summed timings.
Legacy Rust is faster on every measured embedding case. Isomorphism varies:
Python/Cython can win on small uniform chains/stars; equality Cython/Rust
ratios range 0.23–2.85x. Shared-VM noise and microsecond-scale timings limit
precision; this does not justify a universal performance winner.

The unweighted verified Rust embedding is **6.99x slower than legacy Rust at
the median**, ranging **1.28–137x slower** across these cases. It is correct
under the existing source proof and independent tests, but its owned structural
cache/reconstruction is not yet a suitable performance default. Keep it
opt-in and optimize the production assurance boundary before changing `auto`.
Verified isomorphism original-index Python witnesses and verified weighted
affinities remain incomplete; no unsupported mode was sent to that backend.

Machine-readable rows:
[equality](2026-11-14-ordered-equality.json),
[fractional](2026-11-14-ordered-weighted.json),
[unweighted embedding](2026-11-14-ordered-unweighted-embedding.json),
[unweighted isomorphism](2026-11-14-ordered-unweighted-isomorphism.json).
Reproduce in an environment containing the installed Release wheel:

```bash
python /path/to/checkout/dev/bench_backend_speedups.py \
  --sizes 4,8,12,24 --cases 4 --repeat 7 --warmup 2 \
  --impls iter,iter-cython,iter-rust --node-affinity eq \
  --require-impls --strict-scores --json ordered-equality.json
# Repeat with --node-affinity weighted for the fractional label objective.
python /path/to/checkout/dev/bench_backend_speedups.py \
  --sizes 4,8,12,24 --cases 4 --repeat 7 --warmup 2 --functions embedding \
  --impls iter,iter-cython,iter-rust,verified-rust --node-affinity none \
  --require-impls --strict-scores --json ordered-unweighted-embedding.json
# For unweighted isomorphism use --functions isomorphism and omit verified-rust.
```

The fractional callback gives equal labels weight
`0.125 + (ord(a) % 5 + ord(b) % 3) / 8`, other pairs zero. These dyadic
weights avoid score-comparison ambiguity in the benchmark. Larger realistic
graph workloads, repeated independent process runs, allocation measurements
and the optimized verified production implementations remain follow-up work.
