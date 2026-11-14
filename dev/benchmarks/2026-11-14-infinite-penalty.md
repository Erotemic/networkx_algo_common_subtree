# Positive-infinity distance penalties

Source follows `dfa3f43`; Python 3.13.2, Rust 1.95.0, shared Linux VM.
Normal wheel SHA256:
`2383d25ae40ad4ca35878e44dd141e3993ba7264f634cb2c455ed22fd1e89840`.
ABI3 wheel SHA256:
`2911e352c1ad659579788d352bf4585be437859dcaf69deb4191ca3243808292`.

Definition 4 in the [2018 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol117-mfcs2018/LIPIcs.MFCS.2018.54/LIPIcs.MFCS.2018.54.pdf)
allows positive infinity as the distance penalty. Every skipped vertex then
makes a candidate infeasible. The public 2018 solver and independent rescorer
accept `skip_vertex_penalty=float("inf")`, for unrooted, fixed-ambient-root
and root-to-root objectives. Node/edge scores remain finite. NaN, negative
infinity, negative and nonnumeric penalties are rejected.

Rust delegates infinity to the optimized isomorphism solver with the same root
policy; it never multiplies infinity by zero or enters the finite-penalty skip
schedule. The Python oracle continues enumerating selected subsets, skeletons
and bijections independently. It rejects skipped vertices before summing
candidate weights. The independent rooted oracle now also checks its root
predicate before scoring infeasible candidates.

## Correctness and build evidence

- **48 graph Rust tests pass**. Native infinity tests cover each root policy,
  signed/zero scores, forbidden roots and very large finite node weights.
- **209 installed Python tests pass, zero skips**, with Rust and Cython
  parity required in the normal wheel. The same 209 tests pass on each
  CPython 3.10–3.14 using the identical Rust-only CP310 ABI3 wheel. Strict
  ABI auditing reports no violations or version mismatch. Sphinx HTML
  builds with warnings treated as errors.
- **144 new exhaustive objective comparisons**: 24 seeded signed/forbidden
  callback instances per backend and root policy. Infinity's optimum agrees
  with the separately enumerated isomorphism objective. Every returned
  original-vertex witness is independently rescored as both isomorphism and
  embedding, through structured paths and bare node pairs. All paths are
  single edges on each side; tied witnesses need not be identical.
- A discriminating skipped-path example scores 1.75 at penalty 0.25 and 1
  at infinity, even when the direct edge pair is forbidden. Both validators
  reject its long-path witness at infinity. With node weight `1e308`, the
  valid singleton remains usable: an infeasible two-endpoint candidate cannot
  trigger an accumulation overflow in the exhaustive oracle.
- Empty/nonempty behavior and invalid penalty errors are covered at the
  public API; infinity and invalid floating penalties are checked at raw PyO3.

A source-only rebuild of `5d7fabd` through the pinned manylinux profile also
passes 209 tests on glibc 2.28 and on each CPython 3.10–3.14, with a clean ABI
audit. Its wheel SHA256 is
`e8312ad74f9f718ef28c6f90cbc44104b76697e88bb80c16853a564a7dc46865`.
Source archive and native payload hashes are in the packaging ledger. Existing mathematical `WithTop` specifications are unchanged.
No new Lean production-refinement or complexity theorem is claimed. IEEE-754
correctness is deliberately outside the initial proof scope; numerical runtime
regressions remain tested.

## Repeated installed-API measurements

Each root policy has 228 rows: sizes 4/8/16/32, six shapes, equal/asymmetric
sizes, three module-sized pairs, installed APIs/raw PyO3, and exhaustive Python
for sizes at most four. Seven measured calls follow two warmups. Benchmarks run
serially after compilation/tests, with independent public witness validation.
Configuration stores the infinite penalty as a JSON string, preserving strict
JSON compatibility. Every API/raw/oracle score agrees within each objective,
and infinity scores equal the corresponding isomorphism scores on all cases.

| Root policy | Median infinity API / isomorphism API | Median infinity raw / isomorphism raw |
| --- | ---: | ---: |
| Unrooted | 0.973 | 0.995 |
| Fixed ambient roots | 0.982 | 0.992 |
| Root-to-root | 0.980 | 0.989 |

These ratios characterize equivalent implementations; they are not evidence
of an optimization. Small-call noise is substantial: individual API ratios
range 0.467–1.897. Unrooted module infinity medians are 3.14, 3.30 and 5.54 ms.
All samples and environment/binary hashes are retained in:

- [Unrooted](2026-11-14-infinite-penalty-unrooted.json).
- [Ambient rooted](2026-11-14-infinite-penalty-rooted.json).
- [Root-to-root](2026-11-14-infinite-penalty-root-to-root.json).

Reproduce outside the checkout after installing a Release wheel:

```bash
python /path/to/dev/bench_unordered_apis.py \
  --skip-vertex-penalty inf --root-mode unrooted --repeat 7 --warmup 2 \
  --module-trees --json /tmp/infinite-unrooted.json
```
