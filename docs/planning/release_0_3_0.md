# Release 0.3.0

The user selected 0.3.0 on 2026-11-19 and prioritized package usability and fast,
empirically validated algorithms. Defer further formal backend optimization,
optimized Rust refinement and time/space proofs. Keep verification scope clear
in the README; no full-verification claim is required for this software release.

The public unordered endpoints already exist in Python and Rust:
`maximum_common_subtree_isomorphism` (2016) and
`largest_weight_common_subtree_embedding_with_distance_penalty` (2018).
They have independent witness rescorers and small-input oracles. Existing
ordered and exact matching endpoints stay available.

Release gates:

1. Clear README with installation, algorithm selection and executable examples;
   consistent public API documentation, 0.3.0 metadata and changelog.
2. Standard distributions include fast Rust. Explicit pure Python builds remain
   possible; missing Cargo must not silently remove fast unordered endpoints.
3. Build an sdist, rebuild its native wheel outside the checkout, check metadata/
   README rendering and require installed compiled endpoints and behavior.
4. Build/audit a portable CP310 ABI3 Linux wheel; exercise supported runtimes.
   Keep normal Rust+Cython platform wheels in package CI.
5. Run affected native Rust tests, installed Python oracles/differential tests,
   public examples, and short unordered installed-API performance checks.
6. Fix duplicate workflow jobs and obsolete setup.py publication calls. Package
   release readiness depends on package tests, not the independent proof campaign.
7. Record exact local evidence and unresolved remote/platform checks, prepare
   artifacts and checksums, and leave actual tag/publication as an explicit
   maintainer action on the concrete tested candidate.

## Completed local candidate

The README, 0.3.0 metadata, preserved changelog history and public algorithm
documentation are updated. The examples cover ordered and both unordered
families, labels/weights, original-node witnesses and exact integer matching.
The optimized kernels' incomplete formal verification is explicit. No Lean
or maintained Rust algorithm source was changed in this release preparation.

| Check | Executed result |
| --- | --- |
| Filtered source archive | Rebuilt native, portable ABI3 and musllinux wheels; no development submodule, caches or encrypted CI credentials |
| Native CP313 Rust+Cython wheel | 234 tests pass, 10 optional Lean skips; all nine Rust endpoints and both Cython modules required |
| Same portable ABI3 wheel on CPython 3.10–3.14 | 234 pass / 10 optional Lean skips on each runtime; minimum NetworkX 2.8.8 tested on 3.10 |
| glibc 2.28 / CP310 container | 234 pass / 10 optional Lean skips |
| musllinux 1.2 / CP313 container | 234 pass / 10 optional Lean skips; Rust/Cython required |
| Native Rust crates | 50 graph + 13 ordered + 19 assignment tests pass |
| Examples | All four README Python blocks pass, including Python 3.10 with minimum NetworkX |
| Artifact checks | Four distributions pass strict Twine, metadata/payload/source and SHA256SUMS checks; strict ABI3 audit has zero mismatches/violations |
| Build failure policy | Missing Cargo fails default configuration; explicitly disabling both native builds configures successfully |
| Workflows / Python lint | actionlint 1.7.12, unique YAML job keys and fatal flake8 checks pass |

The ten skips require the intentionally unbundled compiled Lean executable.
The independent rational CI still requires it. This is not a new proof audit;
existing proof evidence and assurance boundaries remain unchanged.

Fresh-install testing found NetworkX 2.7 fails plain import on a clean Python
3.10 process without optional scientific packages. The supported floor is
now **2.8.8**, and the CI runtime matrix tests that minimum. Musllinux requires
`-C target-feature=-crt-static` to produce the Rust shared extension; that
targeted wheel build and installed suite now pass.

Three installed unordered benchmark runs each record 112 rows: scalar and
callback weights on normal wheels, and callbacks on the portable wheel.
Sizes 4/32/64 include paths, stars, balanced trees, mixed shapes and asymmetric
pairs. Public witnesses are independently rescored, with exhaustive reference
comparison up to four vertices. For cases where both trees have at least 32
vertices, median native public latency is about **1.2 ms** with scalar weights
and **4.0 ms** with callbacks for each family. Paired callback portable/native
median ratios are **0.988** (2016) and **0.994** (2018). These are short shared-VM
measurements, not universal speed guarantees. The benchmarked Rust library
hashes match the final candidate libraries.

Exact artifact/source identities, commands, runtime versions, logs and benchmark
references are in the [release evidence](../../dev/packaging/2026-11-19-release-0.3.0.json).
The VM-local candidate directory is
`/var/tmp/subtree-release-0.3.0-candidate/`; an identical copy is saved in
the ignored workspace directory `dist/0.3.0/` for review, with:

- source archive;
- CP313 Rust+Cython manylinux_2_34 x86_64 wheel;
- CP310 Rust-only ABI3 manylinux_2_28 x86_64 wheel;
- CP313 Rust+Cython musllinux_1_2 x86_64 wheel;
- `SHA256SUMS`.

The native host's glibc 2.34 requirement is honestly repaired/labeled. The
portable artifact is built and tested at the actual glibc 2.28 floor.
The local source snapshot precedes final evidence/docs/workflow edits; the
ledger verifies maintained runtime, Rust, build metadata and README identity.
Remote CI builds distributions from the final committed release.

## CI ownership correction

The user's follow-up identified the handwritten workflow replacement as a
mistake. `tests.yml`, `checks.yml` and `release.yml` are now regenerated from
xcookie, with source configuration/hooks in `pyproject.toml`. The custom
`publish.yml` and mandatory artifact-promotion/tag-before-publication policy
are removed. The separate project-owned `verification.yml` is unchanged.

Generator fixes in adjacent `../xcookie` commit **0de04bc** address malformed
Windows conditions, empty environment blocks and the obsolete GitHub release
action reference. Its affected regression suites pass 116 tests. Package source
type checking is restored with optional native stubs and small Python typing/
reference-witness checks; no Lean/Rust algorithm source changed.

The user reported an Intel macOS repair error (wheel claims 10.9; Rust requires
10.12). Project cibuildwheel configuration now requests **10.12**; newer Python
and ARM floors are enforced by cibuildwheel. This is a configuration fix,
not a claim of local macOS execution. Fresh source/wheel/hook and installed
checks are recorded in [the correction evidence](../../dev/packaging/2026-11-19-xcookie-ci.json).
Updated review artifacts are in `dist/0.3.0-xcookie-fix/`.

## Remaining release steps

The broad Lean research audit is now manual (`run_full_lean=true`) after the
user reported CI termination with exit 143. The dedicated exact-rational Lean
wheel still builds and runs installed tests automatically and is uploaded as
`verified-lean-wheel-linux`. Its own proof dependencies are checked by building
`verified_ordered`. Source-proved Rust cores, package behavior and ABI3 checks
also remain automatic; standard PyPI wheel contents are unchanged.

Run generated `BinPyCI`/`SourceChecks` and the relevant project checks on the
reviewed commit, including a remote Intel macOS rerun. The earlier local
Linux evidence does not substitute for macOS/Windows execution.

After merge/review and green CI on `main`, push `main:release`. The generated
release workflow rebuilds and publishes to PyPI, then creates/verifies the
version tag and GitHub release. It retains the existing token/encrypted-GPG
configuration. Local checksums remain optional review aids. Follow
[the maintainer instructions](../releasing.md).
**No push, tag or publication has been performed locally.** Further proof and
performance research remain deferred.
