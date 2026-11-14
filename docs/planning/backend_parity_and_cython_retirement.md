# Backend parity, benchmark evidence, and Cython retirement criteria

Status: overlay incorporated 2026-11-14; strict compiled parity and installed-wheel
validation pass. Comparative measurements remain pending.

## Goal

Make the optimized, verified Rust ordered solvers the production default once
all public features they replace have independent correctness evidence,
competitive measured runtime, and working wheel distribution. Retain Cython
as an explicitly selectable comparison implementation during the migration.

**Present behavior:** `impl="auto"` already selects legacy Rust first, then
Cython, then Python. The Aeneas/Lean-verified ordered embedding is explicitly
selected with `impl="verified-rust"`, and currently requires
`node_affinity=None`. The verified ordered-isomorphism core is not yet
available through a dedicated public Python backend. Consequently, making
`verified-rust` the default is a distinct future change, not a synonym for
preferentially using legacy `iter-rust`.

## Evidence tiers

1. **Independent oracle:** for small inputs enumerate all matched-pair deletions
   without calling the dynamic-programming recurrence. Compare optimum scores
   for ordered embedding and check returned witnesses belong to the deletion
   closures of the original inputs. `tests/test_backend_differential.py` covers
   exhaustive one-label Dyck words through four edges and seeded multicolor
   equality-affinity cases. For isomorphism, the current differential tests
   check cross-backend scores and necessary witness properties; an independent
   isomorphism oracle remains to be added.
2. **Differential checks:** test Python, Cython, legacy Rust, and verified Rust
   with exactly the same inputs and compatible affinity semantics. Different
   optimum witnesses can be valid; do not require identical tie choices unless
   the public API explicitly specifies them. Test invalid inputs, empty inputs,
   token-to-node mappings, integer and fractional affinities, ties, and
   numerical boundaries separately. Cython is not a correctness oracle: repair
   any backend whose result conflicts with the independent specification.
3. **Formal verification:** a Lean theorem about the Rust source establishes
   precisely its stated domain and assumptions. The public Python adapter,
   conversions, callbacks, error behavior, and packaging must also be checked.
4. **Performance:** measure production-facing Python calls and native-core
   solvers separately, on the same computer and built distributions. Record
   median and variation from multiple warmed runs, fixture sizes/shapes,
   affinity modes, scores, allocations/memory when available, exact toolchain,
   and source revision. Include deep chains, wide stars, balanced trees,
   asymmetrical sizes, labeled shapes, and workloads similar to actual usage.

## Executable checks

Install a development wheel with both native backends present, then run:

```bash
COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS=1 \
python -m pytest -q tests/test_backend_differential.py
```

That environment variable converts missing Cython, legacy Rust, and (for
unweighted embedding) verified Rust from implicit absence into an explicit
failure. A CI wheel job with both native backends should run this test.

For *unweighted embedding*, compare legacy and verified Rust against Cython:

```bash
python dev/bench_backend_speedups.py \
  --functions embedding \
  --node-affinity none \
  --impls verified-rust,iter-rust,iter-cython,iter \
  --reference iter-cython \
  --sizes 4,8,12,16,24,32 \
  --cases 12 --warmup 2 --repeat 7 \
  --require-impls --strict-scores \
  --csv dev/benchmarks/ordered-unweighted-backend-parity.csv
```

For the affinity-equality API, benchmark *embedding and isomorphism* (the
current verified backend is unavailable for this mode):

```bash
python dev/bench_backend_speedups.py \
  --node-affinity eq \
  --impls iter-rust,iter-cython,iter \
  --reference iter-cython \
  --sizes 4,8,12,16,24,32 \
  --cases 12 --warmup 2 --repeat 7 \
  --require-impls --strict-scores \
  --csv dev/benchmarks/ordered-equality-backend-parity.csv
```

The benchmark helper enforces requested backend availability and score
agreement when these flags are used. It is a benchmarking tool, **not** the
witness oracle. Do not treat the output from a run missing the compiled
extensions as a native-backend comparison.

## Gate for changing defaults

- The verified Rust core is exposed for embedding and isomorphism, with
  independently specified implementations of every intended Cython extension
  that the default API supports (including node-affinity scoring).
- All currently supported input modes pass oracle/differential tests, including
  witnesses and malformed inputs; no silent CI skips of required backends.
- Public Python conversion semantics have explicit tests; the verified Rust
  theorem's scope is reported accurately.
- Comparative benchmarks have been run and committed for representative sizes
  and shapes. Investigate material slowdowns and memory regressions rather
  than accepting them because the backend is verified.
- ABI3 wheel policy is validated, or the remaining per-interpreter packaging
  requirement is explicitly accepted. CI installs and tests wheels from clean
  environments across supported platforms.
- Change `auto` to prefer the fully verified implementation **only for modes
  whose contracts are covered**. Other modes continue to select the best
  supported backend. Retain explicit `iter-cython` for comparison during the
  transition; deprecate shipping it by default only after the above evidence.

## Status of measured performance

The repository includes `dev/bench_backend_speedups.py` but no committed
same-input Cython/legacy Rust/verified Rust comparative results as of the
2026-11-14 snapshot. Existing `dev/benchmarks/2026-11-14-ordered-memo.md`
and graph-reference benchmark reports describe *different* native workloads;
they cannot yield a Cython-vs-Rust speed ratio.
