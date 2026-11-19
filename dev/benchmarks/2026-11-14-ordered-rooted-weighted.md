# Root-preserving ordered isomorphism API, 2026-11-14

The existing level state is now accessible as `rooted=True` in both public
ordered isomorphism APIs. It preserves the implicit parent of a forest and
does not promote skipped descendants into its root level. On connected graph
inputs, every nonempty witness retains both original roots. General mode,
which may select descendant roots, remains the default. Affinities and original
vertex/token mappings work in both modes. The existing DP still computes both
states; no dedicated root-only runtime optimization is claimed.

Independent validation: 529 single-label pairs through four balanced pairs,
80 fractional-affinity cases with unique original indices, a labeled case
separating the two contracts, and graph root-retention/independent rescoring
with character and integer encodings. The source and fresh installed normal
wheel pass **153 tests, zero skips** with Cython/Rust mandatory. The identical
ABI3 wheel passes 153 tests on each CPython 3.10–3.14, and strict symbol
auditing reports zero violations/mismatches. Wheel hashes/runtime evidence are
appended to [the packaging artifact](../packaging/2026-11-14-abi3.json).

Installed Release CP313 wheel SHA256:
`981eb6d0d0ec85f32d89fc921ea00fdc269b5b554d8a090102121a0005251bee`.
ABI3 wheel SHA256:
`562c5166c6e565e52b2d747b573845bb828f187b01ff0e405211bc5ee988d1a1`.
Same shared VM, Python 3.13.2, Rust 1.95.0, 38 shapes/examples, seven repeats
and two warmups as the existing ordered benchmarks. All three backend scores
agree. Rust's median speedup is **2.16x over Python** and **1.57x over Cython**;
small uniform shapes can favor Python/Cython. These are medians of per-case
ratios, not scaling bounds. The run includes balanced-sequence conversion and
witness construction, excluding separate NetworkX conversion.

[Machine-readable rooted-mode rows](2026-11-14-ordered-rooted-weighted.json).
The `rooted` field separates this mathematical contract from general-mode
measurements. Reproduce outside the checkout with the installed wheel:

```bash
python /path/to/checkout/dev/bench_backend_speedups.py \
  --functions isomorphism --rooted-isomorphism --sizes 4,8,12,24 --cases 4 \
  --repeat 7 --warmup 2 --impls iter,iter-cython,iter-rust \
  --node-affinity weighted --require-impls --strict-scores --json rooted.json
```

The independent unweighted root-pruning specification and structural Rust
reference already have Lean proofs. This new weighted legacy production mode,
its Python conversion and original-index witnesses remain independently tested
boundaries requiring production source refinement and runtime proofs before
the final verified release.
