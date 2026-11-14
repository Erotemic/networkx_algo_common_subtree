# Complete uniform child-matchings

Source follows `dcd300e`; Python 3.13.2, Rust 1.95.0, shared Linux VM.
Measured prior normal wheel SHA256:
`8908ecada7d661f6238046e33260719f28df624064ce1dbdf15abdda73849086`.
Measured new normal wheel SHA256:
`1b280874f2867dd6b3e55a7cb5b098ac580810a6c0de5887ffa9800578f08dd0`.

The production matcher recognizes a complete matrix whose entries are the same
strictly positive value. A diagonal covering the smaller side is optimal.
Right deletions either reuse an unaffected witness, replace the deleted column
by the first unused original column, or remove its diagonal pair when the
right side is smaller. Every result retains original coordinates and sums
weights through the existing checked accumulation. It performs no Hungarian
augmentation in this case. Missing, unequal and nonpositive entries retain
the existing matching solver; ordinary single-row matching keeps its scan.

## Correctness and proof boundary

All **50 graph Rust tests** and **228 normal installed Python tests pass**,
with required compiled Rust/Cython backends. Permanent exhaustive partial-
injection/deletion checks cover both orientations. New complete-matrix cases
cover 1/3/5/32/64-sized sides, signed/zero/tiny/large values, original indices,
all deletions and total overflow. Nine public star tests span both graph
families, infinite penalties and all root policies, attaining independent
vertex/edge reward upper bounds and passing both witness validators.

`Shared/UniformMatching.lean` proves cardinality scoring and optimality of a
concrete diagonal over exact ordered-ring weights. The full Lean build passes
3,714 jobs. This is mathematical justification, not a source-refinement or
runtime theorem for the f64 implementation. IEEE-754 correctness remains
outside the initial proof scope. The preceding ABI3 artifact passes 219 tests
on five runtimes; this update's portable artifact is checked after its commit.

## Measurements already collected

The primary before/after runs contain 204 rows each, using sizes 64/128/256/512,
six shapes, asymmetric sizes and three module pairs. Seven samples follow two
warmups. Installed API/raw scores agree, and public witnesses are independently
rescored. The native family benchmark retains seven samples per case.

| Workload | Before | After | Speedup |
| --- | ---: | ---: | ---: |
| Native uniform 32×32, full deletion family | 0.4465 ms | 0.01909 ms | 23.4× |
| 2016 installed star512 | 282.4 ms | 85.53 ms | 3.30× |
| 2018 installed star512 | 314.6 ms | 80.69 ms | 3.90× |
| 2016 installed double-star512 | 460.4 ms | 137.0 ms | 3.36× |
| 2018 installed double-star512 | 458.6 ms | 118.1 ms | 3.88× |

Primary API median speedups across cases are 1.12×/1.53× for 2016/2018.
Some controls are noisy: chain512 ratios are 0.76×/0.92×, and native
signed-optional32 family time changes 0.439→0.500 ms. These runs establish a
useful uniform-case optimization, not precise universal speedup estimates.
The general complexity/solver remains unchanged.

An additional reverse-order exploratory run was collected. It overlapped a Lean
validation process, so its raw files are retained but excluded from these
performance claims. No further long runs are needed before this commit.
Per the author's updated policy, development defaults now use three samples
and one warmup; use small representative cases to catch material regressions,
then perform the comprehensive campaign after implementation commits.

Artifacts:

- [Before APIs](2026-11-14-uniform-matching-before.json),
  [after APIs](2026-11-14-uniform-matching-after.json).
- [Before native](2026-11-14-uniform-matching-before-native.json),
  [after native](2026-11-14-uniform-matching-after-native.json).
- Exploratory controls, excluded from claims:
  [before](2026-11-14-uniform-matching-before-reverse.json),
  [after](2026-11-14-uniform-matching-after-reverse.json).

A short development check after installing a Release wheel can use:

```bash
python /path/to/dev/bench_unordered_apis.py --sizes 16,64 \
  --shapes star,random,chain --repeat 3 --warmup 1 --oracle-max-size 0 \
  --json /tmp/uniform-check.json
```
