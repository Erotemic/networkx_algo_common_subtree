# Changelog

## 0.3.0 — release candidate

- Expose fast weighted unordered subtree isomorphism (Droschinsky 2016) and
  distance-penalized tree embedding (2018) through public NetworkX/PyO3 APIs.
  Results include original-node mappings and aligned paths, with independent
  witness rescorers. Both solvers support labels, signed weights, optional
  nonempty objectives, ambient roots and forced root pairs.
- Use the corrected 2018 path objective: edge rewards/compatibility apply only
  when both matched paths are single edges. Positive-infinite skip penalties
  forbid skipped vertices.
- Improve the native graph schedules, matching-family reuse, state lookups and
  ordered-isomorphism score/choice reconstruction. Fast Rust stays the default
  when installed; existing Cython and Python implementations remain available.
- Add exact signed-integer assignment, partial matching and right-deletion
  matching-family Python APIs, with dual certificates where applicable.
- Add opt-in verified ordered references and the compiled Lean exact rational
  ordered-isomorphism backend. The README distinguishes actual source proofs,
  mathematical results and empirically validated optimized implementations.
- Migrate package builds to scikit-build-core/CMake, include Rust in standard
  wheels, and provide a Rust-only CP310 ABI3 Linux wheel usable on newer CPython
  runtimes. Lean and development submodules are not ordinary runtime dependencies.
- Require Rust for ordinary source builds, so missing Cargo cannot silently
  turn unordered calls into the exhaustive Python reference. Explicit
  `DISABLE_RUST_EXTENSIONS=1` builds remain supported.
- Require Python 3.10 or newer (0.2.2 supported Python 3.8/3.9). Pure Python
  references and the installed backend discovery helpers remain available.
- Require NetworkX 2.8.8 or newer; NetworkX 2.7 can fail to import in a fresh
  Python 3.10 process without optional scientific packages installed.
- Replace duplicated/outdated release CI with distribution builds, installed
  endpoint checks, source-archive rebuilds and an explicit publication workflow.

Formal verification work remains ongoing. The optimized floating graph and
ordered kernels are independently tested; this release does not claim that
their complete production implementations or running times are Lean verified.

## [Version 0.2.2] - Released 2025-03-06

### Changed
* Minimum Python is now 3.8
* Added 3.13 support


## [Version 0.2.1] - Released 2024-04-28

### Changed
* Add 3.12 support
* arm64 and x86 osx wheels now built
* signed wheels and timestamps are now hosted on github


## [Version 0.2.0] - Released 2022-09-16

### Fixed
* Minor bugs

### Changed
* Remove 3.6 support
* Add 3.11 support


## [Version 0.1.0] -

### Added
* Initial version
