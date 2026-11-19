# Backend parity, benchmark evidence, and Cython retirement criteria

## Current dual-backend delivery policy

User clarification, 2026-11-18: formally verified algorithms must be exposed in
Python and benchmarked against relevant non-verified implementations. Retain
the optimized, independently tested implementation as a selectable backend
even if the verified implementation is slower. A verified release with a
documented speed penalty is useful; improving that penalty remains a separate
performance target. Retiring a backend is not required merely because another
backend has stronger proof coverage.

Document assurance, supported scoring/root/input domains and measured speed for
each backend. Explicit verified selection must not silently invoke an unverified
fallback. `auto` may choose an applicable optimized backend and must not be
described as a formal guarantee. Preserve current dispatch until a separately
implemented and tested selection change. Installed-API benchmarks must include
conversion, computation and witness reconstruction, require the intended native
paths, and compare equal domains on repeated warmed inputs. Validate results
against independent oracles/rescorers, allowing distinct optimal tie witnesses.

The older Cython-retirement proposal below is conditional future work; it does
not override this policy or authorize removal of a useful tested fast backend.

Status: overlay incorporated 2026-11-14; strict compiled parity, installed-wheel
validation and comparative measurements pass. Remaining default-backend gates
are production source coverage, intended scoring extensions and performance.

## Goal

Make the optimized, verified Rust ordered solvers the production default once
all public features they replace have independent correctness evidence,
competitive measured runtime, and working wheel distribution. Retain Cython
as an explicitly selectable comparison implementation during the migration.

**Present behavior:** `impl="auto"` already selects legacy Rust first, then
Cython, then Python. The Aeneas/Lean-verified ordered embedding is explicitly
selected with `impl="verified-rust"`, and currently requires
`node_affinity=None`. The structural ordered-isomorphism reference is exposed
as `impl="reference-rust"`, also unweighted; its indexed readback refinement
and complete token entry point now have source-correctness proofs, while
Python/PyO3 conversion is tested integration. Its exponential performance keeps
it outside `auto`.
Consequently, making
`verified-rust` the default is a distinct future change, not a synonym for
preferentially using legacy `iter-rust`.

## Evidence tiers

1. **Independent oracle:** for small inputs enumerate all matched-pair deletions
   without calling the dynamic-programming recurrence. Compare optimum scores
   for ordered embedding and check returned witnesses belong to the deletion
   closures of the original inputs. `tests/test_backend_differential.py` covers
   exhaustive one-label Dyck words through four edges and seeded multicolor
   equality-affinity cases. Independent parent-preserving subset enumeration
   now checks isomorphism objectives and forest witnesses, including rooted
   and fractional original-index scoring modes.
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
  --sizes 4,8 \
  --cases 3 --warmup 1 --repeat 3 \
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
  --sizes 4,8 \
  --cases 3 --warmup 1 --repeat 3 \
  --require-impls --strict-scores \
  --csv dev/benchmarks/ordered-equality-backend-parity.csv
```

The benchmark helper enforces requested backend availability and score
agreement when these flags are used. It is a benchmarking tool, **not** the
witness oracle. Do not treat the output from a run missing the compiled
extensions as a native-backend comparison.

These are short development checks. Defer the larger, repeated benchmark
campaign until implementation milestones are committed and the final campaign
is ready; small-run variance alone is not a reason to keep repeating runs.

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

Committed same-input installed-API comparisons cover Python, Cython, legacy
Rust and the supported verified/reference Rust modes:

- [Ordered API comparisons](../../dev/benchmarks/2026-11-14-ordered-python-apis.md)
  include equality, unweighted and fractional-affinity modes. The verified
  embedding is 6.99× slower than legacy Rust at median, so it stays opt-in.
- [Rooted weighted isomorphism](../../dev/benchmarks/2026-11-14-ordered-rooted-weighted.md)
  measures all supported production backends under the same rooted contract.
- [Structural isomorphism reference](../../dev/benchmarks/2026-11-14-ordered-isomorphism-reference.md)
  records its public Python coverage and substantial exponential slowdown.
- [Current capabilities](capabilities.md) distinguish mathematical, source,
  conversion, performance and packaging evidence. Cython remains available;
  neither its retirement nor a verified-default transition has occurred.
