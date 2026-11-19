# Production ordered isomorphism: choices and separate level/root search

The optimized Rust ordered-isomorphism backend now memoizes scores and choice
IDs, rather than full reconstructed token vectors. Candidate comparisons and
cache hits copy only those small records. Winning matched-pair choices point
to already-built head/tail choices; skipping a subtree reuses a choice ID.
The output is materialized once, using an explicit stack and original token
indices. This removes repeated witness cloning/concatenation across DP states.

Root-preserving calls compute only the level recurrence. General calls share
the memoized level computation and separately evaluate the descendant-root
recurrence. The recurrences preserve the previous strict-improvement ordering:
right-tail then left-tail for level skips, and left head/tail then right
head/tail for descendant roots. The level witness wins ties against descendant
roots. Affinity score addition order and zero-affinity exclusion are retained.

Both Python isomorphism interfaces, all existing affinities, original vertex
mapping and backend selection remain available. `auto` still selects optimized
legacy Rust when installed. Embedding and the structural `reference-rust`
isomorphism backend are unchanged.

## Validation and assurance boundary

- A fresh normal Rust+Cython Release wheel passes **234 tests, zero skips**,
  with native parity mandatory. The existing independent subset oracles cover
  both root contracts, fractional original-node affinities, witness feasibility,
  exact rescoring, malformed inputs, Unicode/opaque tokens and numerical cases.
  New tie regressions check the original-token witness order in both modes.
- **13 ordered-core Rust tests** pass. The new integer reconstruction helper
  checks head/tail/token order, selected-root readback, invalid/cyclic/forward
  references and a 4,096-deep witness without recursive reconstruction.
- All **3,728 main Lean jobs** and both Lean example suites pass. Pinned
  Charon/Aeneas regeneration `--check` passes. Existing mathematical recurrence
  and source-reference proofs are preserved.

The production helper is
`verified_ordered_core::isomorphism_choices::reconstruct_isomorphism_choices`.
It is actually used by PyO3 and included in the maintained extraction; its
full source refinement remains open. The weighted production score DP,
memo/choice correspondence, reconstruction feasibility and time/space proofs
also remain open. This milestone is a tested production optimization, not a
new verified-backend claim. IEEE-754 correctness stays outside initial scope.
No portable wheel validation was repeated for this change.

Normal wheel SHA256:
`283315a15a19876395a3843af5606e4a25df0cc37f6855b556b615f9479f9a52`.
Measured extension SHA256:
`cb2731e964c4c2b8d36259b51d4f0b76bda7e72a45dfecafdc54b415d6c19753`.

## Short installed-API measurements

Before is commit `0631703`; after is the implementation in this commit.
Each mode uses ten identical inputs: sizes **8/16**, one seeded random pair
per size, chains, stars, balanced and asymmetric trees. Each API/backend uses
**three timed samples and one warmup**. Equality and fractional affinities,
general/root-preserving contracts, and Python/Cython/Rust are all measured.
Every cross-backend and before/after objective agrees. No compiler or test
suite ran concurrently with measurements. These are short development results;
the comprehensive final campaign remains deferred.

| Affinity / contract | Before Rust / after Rust, median | After Python / Rust, median | After Cython / Rust, median |
| --- | ---: | ---: | ---: |
| Equality, general | 2.44× | 4.48× | 3.65× |
| Equality, rooted | 3.88× | 7.70× | 6.08× |
| Fractional, general | 2.42× | 4.83× | 3.66× |
| Fractional, rooted | 3.35× | 6.91× | 5.53× |

Ratios are medians of per-case ratios. Per-case Rust before/after ratios span
1.55–8.63× across these four suites. Small-input variance is retained; these
measurements do not establish a universal speedup or the paper complexity bound.
The eight `2026-11-14-ordered-iso-choices-{before,after}-{eq,weighted}-{general,rooted}.json`
files store every backend's samples, scores and errors.
[Environment and binary/source hashes](2026-11-14-ordered-iso-choices-environment.json)
identify the actual installed builds and contain the raw memory observations.

A separate single-call observation of unweighted general isomorphism on two
128-pair stars returns score 128 and two 256-token outputs in both builds.
Fresh-process GNU `time -v` peak RSS changes **71,292 → 43,604 KiB**, about
**39% lower**. It includes Python/import overhead and is one process per build,
not an allocation count or a statistical memory bound. This observation is
separate from the small repeated timing suites.

Reproduce each timing mode outside the checkout, changing affinity/root flags:

```bash
python /path/to/checkout/dev/bench_backend_speedups.py \
  --functions isomorphism --sizes 8,16 --cases 1 \
  --shapes random,chain,star,balanced,asymmetric --skip-examples \
  --repeat 3 --warmup 1 --node-affinity weighted --rooted-isomorphism \
  --impls iter-rust,iter-cython,iter --reference iter-cython \
  --require-impls --strict-scores --json result.json
```
