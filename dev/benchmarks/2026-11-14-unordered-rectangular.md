# Rectangular matching optimization, 2026-11-14

Compared with [the installed API baseline](2026-11-14-unordered-python-apis.md),
this change removes the (left+right)-square dummy assignment and its temporary
profit/cost matrices. Hungarian augmentation assigns the smaller side into
the larger side, reads negated positive profits on demand, and reuses linear
scratch buffers. One-row/column subproblems use a scan. Forbidden/nonpositive
assignments are discarded: every partial matching extends to an injection
without decreasing profit, and every injection decodes to a feasible partial
matching. Direct negation also avoids losing tiny profits to a max-profit
shift; a mixed-scale witness regression is retained.

The matching arithmetic-operation bound becomes O(min(a,b)^2 max(a,b)), with
linear auxiliary space. This is not the specialized 2016 all-deletion matching
algorithm, the optimized 2018 schedule, or a Lean source proof of this f64 code.
Existing exact-integer source-proved matching is unchanged.

Same workload, command, machine, five repeats and one warmup as the baseline.
Source follows `b485132`; Release wheel SHA256:
`081bc202fef69d9c9b0e05de5fe35ed78e66ed9c6140dbb8bc203d69a3b42001`.
[JSON measurements and binary hash](2026-11-14-unordered-rectangular.json)
include all 144 rows, raw timings and installed module paths. Shared-VM noise
limits precision, especially on small cases. Public witnesses were independently
rescored and scores agree across the Rust/raw/Python measurements.

| 32/32 vertices | 2016 API seconds / speedup | 2018 API seconds / speedup |
| --- | ---: | ---: |
| Chain | 0.002662 / 1.72x | 0.005421 / 1.39x |
| Star | 0.110089 / 2.68x | 0.163479 / 2.20x |
| Balanced | 0.003220 / 1.18x | 0.005681 / 1.23x |
| Random | 0.003027 / 1.57x | 0.006309 / 1.33x |

Validation: all **41 Rust graph-crate tests** pass, including 31,250 exhaustive
2x3/3x2 matrices with signed/zero/optional/fractional entries and independent
partial-injection optimization. The fresh installed wheel passes **139 tests,
zero skips**, requiring compiled backends. An additional 32 tree-pair cases
per graph family compare arbitrary signed/forbidden callback tables to
independent exhaustive objectives and rescore original-node/path witnesses.
High-degree performance still needs the paper's specialized machinery; no
optimized-paper complexity or allocation measurement is claimed.
