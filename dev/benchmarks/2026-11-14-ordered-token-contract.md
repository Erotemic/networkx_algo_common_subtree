# Hashable token ties and Python Unicode, 2026-11-14

Source follows `dcd83ea`. Independent examples exposed Python/Cython embedding
comparing opaque token objects on equal scores, and legacy Rust requiring UTF-8
when returning Python string witnesses. Both violate the supported token types.
The iterative embedding backends now compare only objective values and retain
the first equal candidate. Rust joins original Python Unicode tokens after the
DP, preserving lone surrogates as well as ordinary Unicode. Optimal tied
witnesses can change; fixed-backend/input determinism is retained.

Tests independently enumerate common subsets of reversed opaque token pairs,
check the optimum and feasibility without any token ordering, and repeat the
call to check determinism. Unicode roundtrips cover Latin characters, emoji
and lone surrogate pairs in embedding and general/rooted isomorphism, with
the unweighted verified embedding participating where supported. All **161
tests** pass in the installed normal wheel with compiled Cython/Rust required,
and in the identical ABI3 wheel on each CPython 3.10–3.14, **zero skips**.
Strict ABI auditing remains clean. The Boolean-core proof is unchanged;
Python/FFI token reconstruction remains a tested boundary.

Normal wheel SHA256:
`e00bdb489d055e1502cca8e77c80dbe08356ade3731b947fe2f81bf1abce393c`.
ABI3 wheel SHA256:
`2155540b02fabeef178c560ea078b6462374c085a902ed067086386944961700`.
[Packaging/runtime/audit evidence](../packaging/2026-11-14-abi3.json).

The same 38 cases per algorithm, seven repeats, two warmups and fixed seed run
before/after the changes on the installed CP313 wheels. All backend scores
agree. Median per-case before/after runtime ratios are:

| Mode | Python embedding | Cython embedding | Rust embedding | Rust isomorphism |
| --- | ---: | ---: | ---: | ---: |
| Equality | 1.048x | 1.093x | 0.988x | 0.985x |
| Fractional | 1.032x | 1.060x | 0.982x | 0.985x |

Objective-only ties slightly improve the measured iterative Python/Cython
embedding paths. Complete-Unicode Rust reconstruction costs about 1–2% in
these small cases; shared-VM noise limits precision. Python/Cython isomorphism
controls are within about 1% of baseline. No general speedup or scaling claim
is inferred. Original-node graph conversion is outside this balanced-API timer.

Raw rows: [before equality](2026-11-14-token-before-equality.json),
[after equality](2026-11-14-token-after-equality.json),
[before fractional](2026-11-14-token-before-weighted.json),
[after fractional](2026-11-14-token-after-weighted.json).
Run the same command in each installed-wheel environment from outside the
checkout, changing `--node-affinity eq` to `weighted` for the second mode:

```bash
python /path/to/checkout/dev/bench_backend_speedups.py \
  --sizes 4,8,12,24 --cases 4 --repeat 7 --warmup 2 \
  --impls iter,iter-cython,iter-rust --node-affinity eq \
  --require-impls --strict-scores --json token-results.json
```
