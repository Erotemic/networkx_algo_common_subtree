# Installed exact integer matching families

The new public `max_weight_partial_matching_deletions` calls the existing
source-proved `verified_assignment_core::deletion::max_weight_matching_deletions`.
`PartialMatchingFamily.original` is the original optimum;
`without_right[j]` excludes original right vertex `j`, retaining original pair
indices. Signed i64/forbidden inputs and checked i128 totals follow the existing
single-instance API. Python integers are never routed through floating point.

This is the existing reference family: unaffected witnesses are reused and
matched deletions are fully solved again. The newly proved sparse repair caller
is not integrated here. No production default or tree algorithm changes.

## Correctness and installation

A fresh Rust+Cython Release wheel passes **231 tests, zero skips**, with compiled
backends mandatory. The new family tests independently enumerate **295** small
optional signed matrices and **859** original/deleted partial-injection optima,
then validate original indices, feasibility and independent witness rescoring.
Seeded rectangular/tie cases, deterministic behavior, empty sides, all-forbidden
instances, malformed inputs and i64/i128 boundaries also pass. Different optimal
witnesses are accepted. CI now requires all **nine** PyO3 entries before testing.

Normal wheel SHA256: `df977ab0f00db1843539253d902956d55685439997c33a8cd2bd94936f334543`.
Measured extension SHA256: `66287efaa186f9d6df921738ffa03d37456165ad9e2f8408b84e1954c46ca7a9`.
Sphinx HTML passes the existing warnings-as-errors build (`sphinx -W`). The Rust
family already has `MatchingDeletionEntrypoint.max_weight_matching_deletions_total_spec`;
Python/PyO3 conversion and packaging are tested boundaries. No core algorithm
or main proof dependency changed. IEEE-754 is outside initial proof scope.

## Short development measurement

`dev/bench_matching_apis.py` measures the installed family API, raw PyO3 family,
and a loop of installed single-instance calls on masked matrices. Eight fixed
cases at sizes 4/8 cover uniform, signed/forbidden, unused-right and tall inputs.
The JSON contains actual inputs, all samples, scores, binary hash and environment.
Every returned witness is independently rescored outside the timing interval,
and original/deletion objective vectors agree across all three methods.

With **three samples and one warmup**, public family versus single-call-loop
ratios range **0.81–2.62**, median **1.43**.
Unused-right 4/8 and 8/16 cases measure **2.62×** and **2.14×**;
one tiny tall case is slower. These are noisy development measurements, not a
universal speedup or a paper complexity result. No compilation or tests ran
concurrently. The comprehensive campaign remains deferred until the end.

The previous portable ABI3 artifact predates this entry point. A source-only
portable rebuild follows the implementation commit; its results belong in the
packaging ledger rather than being inferred from the older wheel.
