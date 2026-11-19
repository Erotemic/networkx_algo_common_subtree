# Exact matching: bypass assignment when no positive edge exists

The actual `verified_assignment_core::matching::max_weight_partial_matching`
now scans optional weights after the existing shape/dimension checks. If none
is positive, it returns the empty matching without constructing or solving the
square dummy assignment. This also improves the public exact deletion family,
which reuses that empty optimum for every right deletion. Positive instances
keep the existing solver and witness convention. No tree-backend default or
floating-point algorithm changed.

## Correctness and source correspondence

- **232 installed Python tests pass, zero skips**, from a fresh Rust+Cython
  Release wheel with native parity mandatory. Existing independent exhaustive
  injection objectives and original-index witness rescoring remain active.
- **19 exact-core and 50 graph Rust tests pass.** New cases include 4,096 empty
  rows, forbidden/nonpositive/extreme-integer matrices, a last-cell positive
  edge, and ragged input rejection. The large empty-column regression has a
  known empty optimum; it needs no combinatorial oracle or timing assertion.
- **3,728 main Lean jobs and both Lean example suites pass.** Pinned extraction
  `--check` reproduces the maintained semantics. `Rust/MatchingNonpositive`
  proves termination/index safety and the exact sign predicate of both actual
  scans, then proves the empty result maximum against every independently
  feasible partial matching. The unchanged public total-correctness contract
  in `MatchingEntrypoint` now includes this branch. Existing actual deletion
  family and sparse caller proofs survive the regenerated semantics.

Normal wheel SHA256:
`8c2ccb9cb574cc3925d7be7278625187e5b08f9752e659fdbd3e3cfca4a67ed1`.
Measured extension SHA256:
`1ac80aaec386c472b3ae16fb1f471864bc79d860ddb04fe7f1194fdab7c8c9ff`.
Python/PyO3 conversion remains tested, not proved. This milestone did not
repeat portable wheel validation; the previous portable artifact predates this
core change. IEEE-754 stays outside initial proof scope.

## One short before/after measurement

The installed-API runner adds nonpositive and zero-column cases to its existing
uniform, signed/forbidden, unused-right and tall cases. Each build runs exactly
**three samples, one warmup, sizes 4 and 8**: 12 inputs and 36 method rows.
No compiler/tests ran concurrently with either measurement. Input matrices,
all samples, binary hashes and environment are preserved in
[`before.json`](2026-11-14-exact-nonpositive-before.json) and
[`after.json`](2026-11-14-exact-nonpositive-after.json). The actual inputs and
all objective vectors agree across builds and methods; witnesses are rescored
independently outside the timing intervals.

| Public family input | Before median, µs | After median, µs | Before/after ratio |
| --- | ---: | ---: | ---: |
| Nonpositive 4×4 | 6.001 | 3.247 | 1.85× |
| Nonpositive 8×8 | 14.300 | 4.811 | 2.97× |
| Four zero-width rows | 2.654 | 1.913 | 1.39× |
| Eight zero-width rows | 4.786 | 2.062 | 2.32× |

Raw PyO3 family ratios on nonpositive inputs are 4.17×/7.13×; public wrapping
limits the tiny-call speedup. Positive-case public ratios span **0.78–1.06**,
so this run establishes no general speedup and cannot settle small regressions.
The additional sign scan short-circuits on the first positive edge; the main
square solver is unchanged. Keep the noisy samples rather than repeating this
microbenchmark to smooth them. A larger final campaign remains deferred.

The full one-augmentation exact family integration and optimized sparse queue
remain separate implementation/proof tasks. A direct substitution requires
constructing the repair routine's feasible/tight numeric starting state; this
early return neither assumes nor completes that integration.
