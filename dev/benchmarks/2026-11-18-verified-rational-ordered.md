# Verified exact rational ordered Python delivery

The explicit `verified-lean` backend now exposes the compiled, proved memoized
ordered subtree-isomorphism algorithm through balanced-sequence and NetworkX
APIs, for both root policies. Exact `int`/`Fraction` affinities return an exact
`Fraction` score, with original-input witnesses. The optimized float backends
remain available; `auto` is unchanged.

## Checked algorithm and boundary

`proofs/SubtreeProofs/Paper2004/RationalOrderedSolver.lean` defines the actual
hash-memoized algorithm. `Cache.sound` is constructed and preserved inside the
implementation; the public endpoint assumes neither a sound user cache nor
correct child scores. `solve_eq` proves equality to the independent original-
identity `AffinityDP.level`/`anywhere` recurrences. `solveResult_correct` proves
feasibility, global optimality, exact score and original preorder;
`solve_unique_endpoints` proves uniqueness from unique input identities.
The cache uses full forest keys with lawful equality, so hash collisions do
not merge different queries. Proof fields are erased by the Lean compiler.
No arithmetic abstraction replacing floats is needed for this implementation.

`VerifiedOrderedMain.lean` calls that very function and transports exact
numerator/denominator strings. Python conversion and process/JSON I/O are tested
boundaries. Standard Lean compilation/runtime and its exact arithmetic and
hash-map implementations are the execution trust boundary. The existing fast
Rust score/state/memo refinement is still open. No running-time proof is claimed.

This is a delivery route alongside the Rust-first O01--O04 plan: the user asked
for the full verified rational algorithm from Python and accepts a speed hit.
Direct Lean compilation delivers that useful milestone without waiting for the
separate optimized Rust proof campaign. Weighted ordered embedding is a distinct
future task and is not covered by this isomorphism theorem.

## Validation

- Full library: **4,366 jobs**, successful.
- Native executable: **6,272 jobs**, successful, including the initial native
  dependency compilation. Pinned Lean 4.35.0 and existing Mathlib pins unchanged.
- Six Lean examples, including root-policy difference, exact fractions, zero
  rejection, original endpoint uniqueness and a `2^200+1` score. Concrete
  examples use the universal refinement theorem and kernel reduction; actual
  native cached execution is also covered by the installed Python tests.
- Focused shared-tool audit: **43 declarations / 12 theorem declarations**,
  only `propext`, `Classical.choice`, `Quot.sound`; no additional axioms.
- Two endpoint statement seeds: **109 records / 400 edges**, no unknowns.
- Fresh installed normal Rust+Cython+Lean wheel: **243 tests, zero skips**,
  with both `COMMON_SUBTREE_REQUIRE_LEAN=1` and
  `COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS=1`. Imported package and binaries were
  under `/var/tmp/subtree-rational-installed`, outside the checkout.
- The rational suite covers 98 weighted input/root-policy combinations against
  an independent original-parent subset oracle, exact rescoring, non-dyadic
  fractions, `2^200` weights and `10^-60` near ties, malformed inputs even
  against empty, typed/lone-surrogate tokens, original NetworkX nodes, unsupported
  floats, missing executable, worker restart, concurrent threads and fork reuse.

Artifact: `networkx_algo_common_subtree-0.2.3-cp313-cp313-linux_x86_64.whl`,
40,694,679 bytes, SHA-256
`dd17a6eddb414a53e7a1352d2e255ea3092776971a33920eeb0b497f64f4ff49`.
Built in `/var/tmp/subtree-rational-wheel-build` on ext4, including its real
`cargo-target`; all seven maintained cache mounts were checked ext4 before
building. Cargo/Rustup homes are local. Runtime `ldd` lists ordinary system
libraries, with no Lean installation or Mathlib checkout required.
The source-built optional executable is approximately 142 MiB uncompressed;
binary/dependency size is a future packaging improvement.

## Installed-API performance

[Raw samples and binary/environment identities](2026-11-18-verified-rational-ordered.json)
come from `dev/bench_verified_rational.py`, run outside the checkout after the
final wheel installation, with no concurrent build/test process. Each of 18
cases (8/16/32 vertices × star/chain/balanced × rooted/general) warms each explicit
backend once and records three complete public NetworkX calls. All returned
witnesses are independently rescored on original nodes/edges. Every backend's
objective agrees in each case. Inputs use positive dyadic rational weights:
these small scores/intermediate sums are also exactly representable in f64,
while the Lean backend executes general rational arithmetic.

| Comparison | Median per-case Lean/reference latency ratio | Range |
| --- | ---: | ---: |
| optimized `iter-rust` | 7.60× | 4.56--26.02× |
| `iter-cython` | 4.16× | 1.63--12.28× |
| Python `iter` | 3.86× | 1.50--16.21× |

Median of the 18 Lean case medians is 9.36 ms (range 1.81--96.89 ms).
The first native-worker call is separately 124.7 ms; warmed samples include
conversion, eager affinity extraction, IPC, exact solving and reconstruction.
The persistent native worker's Linux high-water RSS after the workload is
82,012 KiB (single observation, not a memory bound). Machine: Linux x86_64,
glibc 2.39, CPython 3.13.13. Samples are a short development comparison.
This release delivers exact correctness with a measured performance penalty;
competitive optimized Rust proof/performance work remains explicit.

## Reproduce

Use the root cache setup and optional wheel build in
[`proofs/VERIFICATION.md`](../../proofs/VERIFICATION.md). From `proofs/`:

```bash
lake build
lake build verified_ordered
lake env lean Tests/RationalOrderedSolver.lean
```

Outside the checkout, with the fresh wheel installed and the test dependencies:

```bash
COMMON_SUBTREE_REQUIRE_LEAN=1 COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS=1 \
  python -m pytest -q /path/to/checkout/tests
python /path/to/checkout/dev/bench_verified_rational.py --output result.json
```

Local logs are `/var/tmp/subtree-rational-{library,native-build,lean-tests,wheel,installed-tests,benchmark}.log`,
with elaborated audit/statement exports at `/var/tmp/subtree-rational-axioms.jsonl`
and `/var/tmp/subtree-rational-statements.json`. No reliable per-task token
counter was available; no actual token count is asserted.
