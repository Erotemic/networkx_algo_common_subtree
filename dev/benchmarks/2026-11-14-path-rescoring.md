# Validate supplied path witnesses without enumerating all mapped pairs

Graph baseline: `dcab8f3`. Python 3.13.2, Rust 1.95.0, shared Linux VM.
Normal wheel SHA256:
`799110cb4103db9d837b8a6358356865599d4770cb513fd996c5c130812b1097`.
The native extension hashes before/after agree exactly: this milestone changes
Python validation, not either Rust solver.

Public result-object rescoring now directly validates the supplied original
paths. It checks injective mappings, actual original edges, simple paths,
aligned endpoints, absent mapped interior vertices, pairwise disjoint interiors,
distinct skeleton edges, connectedness and the tree edge count. Both path
families therefore realize the same common tree. Node/edge compatibility,
signed weights, direct-only edge rewards and skipped-vertex penalties are
rescored independently of the optimization recurrence and claimed result score.
Node/edge summation order remains the reference's canonical order, even if
callers reorder or reverse their aligned paths.

Validation costs O(n+m+path_length+k*log(k)) for k mapped pairs with scalar
weights, using dictionaries/sets with their usual expected lookup costs.
Arbitrary callbacks still add full scoring-table preparation. Bare node-pair
iterables retain the separate, slow reference skeleton/path validator; this
also supplies an independent cross-check for small examples.

## Correctness and builds

**176 tests pass, zero skips**, from a fresh normal installed wheel with
compiled parity required. Small signed callback cases compare supplied-path
validation with the separate bare-pair reference validator as well as exhaustive
optimal objectives. New malformed cases reject duplicate coordinates, unknown
vertices, missing/repeated/jumping paths, mapped interiors, endpoint mismatches,
forbidden scores, overflow and unselected branch overlap on either input.
Path reordering/reversal and independent rescoring of a false claimed weight
are accepted correctly. Both existing Python/Rust backend witnesses pass.

The identical ABI3 wheel passes 176 tests on each CPython 3.10–3.14 and strict
ABI auditing is clean. Strict Sphinx HTML generation succeeds. The last native
44-test graph result remains applicable because native code is unchanged.
No Lean refinement or complexity proof is added by this Python validator.

## Rescoring performance

The benchmark's new `--time-rescoring` records validation samples separately
from installed solver timings. [Before](2026-11-14-rescoring-before.json) and
[after](2026-11-14-rescoring-after.json) each contain 72 public/raw rows with
five samples after one warmup. On equal 64-node inputs:

| Objective / shape | Rescore before seconds | After seconds | Speedup |
| --- | ---: | ---: | ---: |
| 2016 chain | 0.000761 | 0.000426 | 1.79× |
| 2016 star | 0.001088 | 0.000428 | 2.54× |
| 2016 balanced | 0.000756 | 0.000406 | 1.86× |
| 2018 chain | 0.168117 | 0.000785 | 214.18× |
| 2018 star | 0.028067 | 0.000403 | 69.59× |
| 2018 balanced | 0.147770 | 0.000432 | 342.20× |

The previous validator enumerated every mapped pair, performing a fresh tree
path search with repeated whole-edge scans for each. It prevented practical
512-node scaling runs even though solver timing had already finished.

## Completed 2018 scaling

[96 installed public/raw rows](2026-11-14-embedding-scaling.json) now complete
through 512 vertices, seven samples after two warmups, all objectives agreeing
and public witnesses independently validated. Public medians, seconds:

| Equal sizes | Chain solver | Star solver | Balanced solver | Random solver | Double-star solver | Chain/star solver |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | 0.002195 | 0.002913 | 0.001639 | 0.001770 | 0.001958 | 0.001902 |
| 128 | 0.008309 | 0.021897 | 0.006996 | 0.007554 | 0.012757 | 0.009772 |
| 256 | 0.034532 | 0.158042 | 0.024409 | 0.026018 | 0.084548 | 0.029306 |
| 512 | 0.124866 | 1.182025 | 0.109467 | 0.116884 | 0.624800 | 0.129141 |

At 512 nodes, validation takes 4.98 ms (chain), 4.69 ms (star), 5.03 ms
(balanced), 2.93 ms (random), 4.72 ms (double-star), and 0.99 ms (chain/star).
Whole-process RSS is 131 MB, including Python, fixtures and all workloads.
Identical-shape uniform cases attain the elementary injection upper bound
2*n−1; chain/star attains the three-vertex path bound 5. Random large optima
have feasibility/rescoring and native/public agreement, not exhaustive optimality
certificates. Quadratic bounded-degree and faster-growing high-degree timings
are consistent with the operation argument but do not prove it. Root-level
matching-family work remains a measured opportunity on large stars.

```bash
# Outside the checkout, using the chosen installed Release wheel:
python /path/to/checkout/dev/bench_unordered_apis.py \
  --sizes 16,32,64 --shapes chain,star,balanced --oracle-max-size 0 \
  --time-rescoring --repeat 5 --warmup 1 --json validation.json
python /path/to/checkout/dev/bench_unordered_apis.py --algorithm embedding \
  --sizes 64,128,256,512 --time-rescoring --repeat 7 --warmup 2 --json scaling.json
```
