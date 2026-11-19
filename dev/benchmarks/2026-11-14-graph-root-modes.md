# Public ambient-root and root-to-root graph objectives

Source follows `4039e2d`; Python 3.13.2, Rust 1.95.0, shared Linux VM.
Normal wheel SHA256:
`f57724f4ff943e90a65770cb88596e38ed9a5dcce391795e7ecd15c10c2e66ea`.

Both public Droschinsky APIs and independent rescorers now accept
`roots=(left_vertex, right_vertex)` and `root_to_root=True`. Omitting roots
retains the unrooted objective. Ambient roots require a selected common highest
pair ancestral to every selected vertex in both orientations; that pair may
lie below either supplied root. Root-to-root additionally requires the actual
supplied pair. The optional empty optimum remains available; `allow_empty=False`
requests a nonempty witness and retains negative optima.

Rust exposes the same policies as `RootConstraint` and reuses the existing
matching/choice tables. Rooted 2018 selects mapped states in the supplied
orientations and excludes the unrooted skipped-highest join. Skips below a
retained common root remain valid. The global left root computes one required
right view per vertex, preserving the earlier root-only optimization. Forced
root selection uses singleton ranges rather than scanning every top pair.
Root values are validated and converted to original indices at the thin Python
boundary; scoring and matching remain native, with the GIL released.

## Independent correctness

All **47 graph Rust tests** and **199 installed Python tests pass**, with
compiled parity mandatory in the normal wheel. The identical Rust-only ABI3
wheel passes 199 tests on each CPython 3.10–3.14; strict ABI auditing is clean.
Strict Sphinx HTML generation passes. The portable manylinux profile also passes 199 tests on glibc 2.28 and on each
CPython 3.10–3.14 after a source-only rebuild at `e272d36`; the packaging ledger
records its separate source/wheel hashes.

Independent subset/bijection/path enumeration now filters by the source root
predicate, using actual root-to-vertex paths rather than DP states. Thirty-two
signed/forbidden callback instances supply **128 rooted objective comparisons**
across both families and both rooted policies. Witnesses are separately checked
through NetworkX paths and the public interval/path validators. Existing high-
degree cases now force both deletion-repair orientations under all three policies,
attaining independent node/edge upper bounds. Raw PyO3 and public invalid-root
errors, original tuple/string vertices, empty/negative outcomes and deterministic
witnesses are covered.

Concrete discriminators:

* Identical uniquely labeled paths with opposite supplied roots have unrooted
  optimum 5, ambient-rooted optimum 1, and an infeasible forced root pair.
* A forbidden highest star vertex can connect two leaves in an unrooted path
  with score 1.75; fixing that vertex as ambient root restricts the optimum
  to 1. Rooting at a retained leaf still allows the penalized path.
* A forced root of weight −5 and child of weight 1 give nonempty score −4 with
  zero edge reward, and score 2 with edge reward 6. Negative mapped roots are
  retained when required and can benefit from their descendants.

Existing Lean independent rooted specifications/recurrences supply the
mathematical contracts. This exposure adds **no new Lean actual-source, witness
or complexity theorem** for the production f64 implementation or Python boundary.

## Installed measurements

Five-repeat [ambient-rooted](2026-11-14-graph-rooted-apis.json) and
[root-to-root](2026-11-14-graph-root-to-root-apis.json) runs each retain 228
public/raw/oracle rows after one warmup. Roots are the first original vertex
on each side. Every public witness is independently rescored with its root
constraints and every available backend agrees on objective values.

| Module workload | 2016 ambient / forced seconds | 2018 ambient / forced seconds |
| --- | ---: | ---: |
| Identical 166/166 | 0.002478 / 0.002290 | 0.003419 / 0.003587 |
| Wrapped 166/214 | 0.002383 / 0.002273 | 0.004326 / 0.004362 |
| ResNet50/101 166/319 | 0.004622 / 0.004910 | 0.006925 / 0.006022 |

[Ambient callbacks](2026-11-14-rooted-callbacks.json) and
[forced-root callbacks](2026-11-14-root-to-root-callbacks.json) add 44 rows
each. On 166/319 vertices, public 2016 costs 0.024161/0.023971 s and 2018
0.030403/0.026713 s; these include callback-table construction. Raw costs are
retained separately in the artifacts. Different rooted policies are different
objectives, so these columns do not establish interchangeable-backend speedups.

Seven-repeat unrooted [before](2026-11-14-root-options-before.json) and
[after](2026-11-14-root-options-after.json), two warmups, each contain 228 rows.
All objectives agree. Median new/old public runtime ratios are **1.006 (2016)**
and **0.999 (2018)**; raw ratios are **0.999/0.997**. An unnecessary degree scan
and unused unrooted keyword conversion were removed before this final run.
Individual small-case timings remain noisy on the shared VM; full samples are
retained rather than asserting a universal zero-overhead guarantee.

```bash
# Outside the checkout, using the installed Release wheel:
python /path/to/checkout/dev/bench_unordered_apis.py \
  --root-mode rooted --module-trees --repeat 5 --warmup 1 --json rooted.json
python /path/to/checkout/dev/bench_unordered_apis.py \
  --root-mode root-to-root --module-trees --repeat 5 --warmup 1 --json forced.json
python /path/to/checkout/dev/bench_unordered_apis.py --weights callbacks \
  --root-mode rooted --sizes 8,32 --shapes chain,star --module-trees --json callbacks.json
```
