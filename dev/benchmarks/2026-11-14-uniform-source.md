# Production uniform-index source proof

Baseline implementation: `306177e`, measured normal wheel
`1b280874f2867dd6b3e55a7cb5b098ac580810a6c0de5887ffa9800578f08dd0`.
New normal wheel SHA256: `446b0cdb1b8867b0c9af0026e64a63a8757ad50b5330890d3be813815230a590`.

Both installed graph algorithms now use the same integer-only uniform index
constructor in `verified_assignment_core::uniform_pairs`. It reserves the known
maximum output size once. The production caller skips filtering/sorting already
ordered uniform pairs, shares the base on unmatched deletions, and retains its
previous floating-point score summation order and finite-result checks.
Nonuniform Hungarian matching and single-row scans retain their algorithms.
No public API or default-backend contract changes.

## Correctness evidence

All **50 graph Rust**, **17 exact-core Rust** and **228 installed Python tests**
pass. Compiled Rust/Cython backends are mandatory. The existing exhaustive
injection/deletion and graph/path oracles still execute; new native tests cover
all rectangular dimensions through 16, every original deletion, out-of-range
no-op deletions, deterministic ordered output and tiny outputs at `usize::MAX`
dimensions. Original right indices remain uncompressed.

Pinned Charon/Aeneas regeneration supplies the actual production helper's
semantics. `Rust.UniformPairs.indices_spec`, `source_base_maximum`,
`source_deleted_maximum`, `source_index_bounds` and `source_pair_cells` prove
termination, checked loop increments/vector-length safety in the extraction
model, original-index feasibility, independent exact ordered-ring optimality,
row uniqueness and live entry count. The full main Lean build passes
**3,717 jobs**, preserving existing exact-source proofs.

This is a source proof of the production integer index constructor. Uniform
float recognition, score accumulation, general Hungarian families, graph DP,
FFI, allocator capacity/OOM behavior and runtime correspondence are not proved
by these theorems. IEEE-754 correctness is deliberately outside initial scope.
The previous ABI3 portable wheel remains evidence for its recorded source;
this source update was validated in a fresh normal Rust+Cython wheel.

## Short development performance check

The before/after JSON files record identical workloads, binary hashes and all
samples: 16/64-node stars, random trees and chains, including asymmetric pairs;
both graph algorithms; installed API and raw PyO3 calls. Three samples and one
warmup produce **48 rows per build**. Public witnesses are independently
rescored and objectives agree across corresponding builds/backends. No compiler
or test suite ran during measurement.

Installed-API before/after median ratios range from 0.79 to
1.42, with median 1.03. These short,
sub-millisecond/millisecond workloads are noisy; they support a development
regression check, not a statistically established speedup or universal bound.
Both runs together took under one second. The comprehensive benchmark campaign
remains deferred until after implementation commits, per author instruction.
