# Original-vertex access to the structural isomorphism reference

Source follows `7470fa1`. Python 3.13.2, Rust 1.95.0, shared Linux x86-64 VM.
The measured normal wheel SHA256 is
`9bac4218723918eab7317355894baedfaf6fb0c2f21ea46f9bcac5489f65e052`.
A subsequent shared token-readback helper move preserves behavior; final tested
normal/ABI3 hashes and runtime results are in the packaging ledger.

Both balanced-sequence and NetworkX ordered isomorphism APIs now accept
`impl="reference-rust", node_affinity=None`, including `rooted=True`.
The structural optimum comes from the existing source-proved
`rooted_common_isomorphism` / `largest_common_isomorphism` Rust reference.
New native reconstruction retains original preorder pair identities, removes
whole child subtrees and selects one common original parent. It never promotes
grandchildren into missing ancestors. Parsing and emission return original
token positions, which the thin Python wrapper reads with original containers
and NetworkX vertices. Typed token kinds are checked before type erasure.

This is deliberately an explicit **small-input exponential reference**. It is
listed only with `include_restricted=True`, rejects weighted/equality modes,
and never replaces optimized Rust in `auto`. The new indexed reconstruction
and token composition are extracted and independently tested, **not source
proved**. The existing structural theorem does not prove this new boundary.

## Correctness and preserved proofs

- **219 installed Python tests pass, zero skips**, with native Cython/Rust
  required. The identical final Rust-only CP310 ABI3 wheel passes 219 on each
  CPython 3.10–3.14; strict ABI auditing is clean. CI requires the new entry
  point and executes the exhaustive cases, including in its portable profile.
  The later source-only `d858a55` portable rebuild passes 228 tests on its
  glibc 2.28 floor and all five CPython runtimes, including this reference API.
- Independent adjacency/parent subset enumeration checks both root policies
  over **1,058 exhaustive pairs** through four pairs per input. Another **160
  unique-token cases** validate exact original-index feasibility, topology,
  optimum and score; different optimal witnesses are permitted.
- API tests retain string/list/tuple output, lone surrogates, original mixed
  NetworkX vertex objects, explicit discovery, empty inputs, malformed typed
  tokens on either side and rejection of unsupported affinities.
- **10 ordered-core Rust tests pass**, including original-position and
  root-policy discriminators, all 38,809 six-edge structural isomorphism pairs,
  existing contraction tests and independent stack-parser checks.
- Pinned Charon/Aeneas regeneration and `--check` succeed without editing
  generated code. The complete **3,713-job Lean build** and both Lean example
  suites pass. No new source-correctness theorem is claimed for reconstruction.
  IEEE-754 remains deliberately outside the initial proof scope.

## Repeated installed API timings

Both modes use the same 36 small cases: sizes 2/4/6/8, four random cases per
size, plus chains, stars, balanced/asymmetric inputs and chain-versus-star.
Each backend receives identical inputs, with seven timed calls after two
warmups. All scores agree. Fixed larger paper examples are omitted explicitly
by `--skip-examples`, preventing accidental exponential work outside this run.
Every sample is retained in the two 144-row JSON artifacts.

| Mode | Median reference / optimized Rust | Eight-pair star reference | Optimized Rust | Star slowdown |
| --- | ---: | ---: | ---: | ---: |
| General | 0.825 | 32.213 ms | 0.05157 ms | 624.6× |
| Root preserving | 0.475 | 5.822 ms | 0.04704 ms | 123.8× |

Small cases benefit from the narrow native token boundary; this does not
compensate for exponential growth. The general per-case ratios range
0.599–624.6. Keep optimized Rust as the default. These measurements cover the
balanced public API, including conversion and witnesses; NetworkX conversion
and process memory are not separately measured here.

[General samples](2026-11-14-ordered-isomorphism-reference.json),
[root-preserving samples](2026-11-14-ordered-isomorphism-reference-rooted.json).
Reproduce outside the checkout after installing a Release wheel:

```bash
python /path/to/dev/bench_backend_speedups.py --skip-examples \
  --sizes 2,4,6,8 --cases 4 --repeat 7 --warmup 2 --functions isomorphism \
  --impls iter,iter-cython,iter-rust,reference-rust --node-affinity none \
  --require-impls --strict-scores --json /tmp/isomorphism-reference.json
# Add --rooted-isomorphism for the root-preserving objective.
```

Remaining work includes a source proof of indexed readback and a production
optimized isomorphism refinement. Weighted/affinity source coverage is distinct
from the proved unweighted structural reference.
