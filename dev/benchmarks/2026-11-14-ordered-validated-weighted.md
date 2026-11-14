# Ordered input/scoring validation cost, 2026-11-14

Source follows `c6906f8`, with ordered boundary fixes. Release CP313 wheel
SHA256 `cee3f0d38a7f851ccc67f6ae99cacdf29a976720c8c9c9ec51e7e151e226f72f`,
installed at `/tmp/common-subtree-ordered-contract-install`. Same shared VM,
Python 3.13.2, Rust 1.95.0, shapes, seed, seven repeats and two warmups as
[the prior ordered comparison](2026-11-14-ordered-python-apis.md).

Native Rust validates interned typed-token IDs and extracted f64 affinities;
Cython validates its extracted doubles. Pure Python uses checked callbacks.
Malformed inputs, nonfinite/negative affinities and total overflow are now
rejected. Rust no longer hashes mapped callback values or silently substitutes
tokens for missing mapping entries. All 149 installed-wheel tests pass with
native backends required and zero skips.

Across the identical 38 cases per algorithm, median new/old runtime ratios
are 1.075 (Rust embedding), 1.039 (Rust isomorphism), 1.144/1.140 (Cython),
and 1.189/1.137 (Python). These are small-case timings on a shared VM, so
interpret the remaining overhead as a characterization, not a precise global
cost or scaling result. Production Rust remains faster at the median: 4.43x
over Python and 3.44x over Cython for embedding, 2.16x/1.57x for isomorphism.
All scores agree under the fractional dyadic affinity objective.

[Machine-readable rows](2026-11-14-ordered-validated-weighted.json).
Reproduction command, from outside the checkout in the installed environment:

```bash
python /path/to/checkout/dev/bench_backend_speedups.py \
  --sizes 4,8,12,24 --cases 4 --repeat 7 --warmup 2 \
  --impls iter,iter-cython,iter-rust --node-affinity weighted \
  --require-impls --strict-scores --json ordered-validated-weighted.json
```
