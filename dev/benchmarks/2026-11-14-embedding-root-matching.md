# Skip unused global-root matching families

Graph baseline: `e94defc`, Python 3.13.2, Rust 1.95.0, shared Linux VM.
Normal wheel SHA256:
`fa01910c00280c85add6ac9c74df788b22d988c5e98fea1485dd971567a2b41b`.

The global left root has no higher caller. The retained-highest case reads
only its whole-right mapped states; the skipped-highest case reads only its
children's continuations. Therefore this root now uses one ordinary matching
per right vertex and omits its unused deletion families and skip messages.
Nonroot states still compute all related views. The skipped-highest distinct-
branch path case remains included, including when this root is forbidden.

All **44 native graph** and **176 installed Python tests** pass, with compiled
parity mandatory. Independent exhaustive objectives and path validation include
the forbidden-root path case and both actual parent-deletion repair orientations.
The identical ABI3 wheel passes 176 tests on each CPython 3.10–3.14 and strict
ABI auditing is clean. No new Lean source or complexity claim is added.

[All 96 public/raw rows](2026-11-14-embedding-root-matching.json) have seven
samples after two warmups, compared with
[the preceding scaling run](2026-11-14-embedding-scaling.json). Every objective
agrees, and public witnesses are independently rescored (timed separately).
Equal-size public medians:

| Workload | Before seconds | After seconds | Speedup |
| --- | ---: | ---: | ---: |
| Star128 | 0.021897 | 0.004875 | 4.49× |
| Double-star128 | 0.012757 | 0.008092 | 1.58× |
| Chain/star128 | 0.009772 | 0.007780 | 1.26× |
| Star512 | 1.182025 | 0.231948 | 5.10× |
| Double-star512 | 0.624800 | 0.369595 | 1.69× |
| Chain/star512 | 0.129141 | 0.121765 | 1.06× |
| Balanced512 | 0.109467 | 0.103476 | 1.06× |
| Random512 | 0.116884 | 0.111386 | 1.05× |
| Chain512 | 0.124866 | 0.133980 | 0.93× |

The small chain regression is retained, alongside all samples and shared-VM
metadata. The intended effect is concentrated at high-degree roots; no universal
speedup or new asymptotic bound is claimed. Remaining work includes portable
wheel validation, verified ordered-isomorphism index exposure, applicable
bounded-integer improvements and the full production assurance obligations.

```bash
# Outside the checkout, using the chosen installed Release wheel:
python /path/to/checkout/dev/bench_unordered_apis.py --algorithm embedding \
  --sizes 64,128,256,512 --time-rescoring --repeat 7 --warmup 2 --json scaling.json
```
