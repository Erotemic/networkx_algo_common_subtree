# Package builds and optional stable-ABI wheels

The default source build includes Rust/PyO3 and both Cython extensions:

```bash
python -m pip wheel . --no-deps -w dist \
  -Ccmake.define.BUILD_CYTHON_EXTENSIONS=ON \
  -Ccmake.define.REQUIRE_RUST_EXTENSIONS=ON
```

An opt-in Rust-only `cp310-abi3` wheel supports the same public Rust algorithm
families and scoring modes. It requires scikit-build-core >=1.0 and a CPython
build interpreter >=3.10:

```bash
python -m pip wheel . --no-deps -w dist \
  -Cwheel.py-api=cp310 \
  -Ccmake.define.BUILD_CYTHON_EXTENSIONS=OFF \
  -Ccmake.define.REQUIRE_RUST_EXTENSIONS=ON
python -m pip install abi3audit
abi3audit --strict --summary dist/*-cp310-abi3-*.whl
```

CMake consumes scikit-build-core's stable-ABI settings, enables the actual
PyO3 `abi3-py310` Cargo feature and installs `_rust.abi3.so` (`_rust.pyd` on
Windows). Rust-only builds require the Python interpreter, with no CMake C/C++
development-module target; PyO3 configures Rust's Python ABI and linking.
The stable wheel setting does not merely rename the artifact. Configuration
rejects other stable floors, missing Rust, or enabled version-specific Cython
targets. Normal builds continue to include Cython for parity and regression
testing. The historical ABI3 branch was not merged.

References: [PyO3 0.22.6 stable-ABI build requirements](https://pyo3.rs/v0.22.6/building-and-distribution.html#py_limited_apiabi3),
[scikit-build-core stable-ABI settings](https://scikit-build-core.readthedocs.io/en/latest/guide/cmakelists.html#limited-api-stable-abi),
and [Cython's separate Limited API mode](https://docs.cython.org/en/latest/src/userguide/limited_api.html).
The existing Cython targets use the full version-specific API; their Limited
API mode has not been validated for this project. No Cython native library is
included in the stable-ABI artifact.

## Portable Linux stable-ABI wheel

The separate [cibuildwheel profile](../dev/abi3-cibuildwheel.toml) builds one
Rust-only **CP310 ABI3 manylinux_2_28 x86_64** artifact. Docker is required:

```bash
python -m pip install cibuildwheel==4.3.5
export SOURCE_DATE_EPOCH="$(git log -1 --format=%ct)"
python -m cibuildwheel --platform linux \
  --config-file dev/abi3-cibuildwheel.toml --output-dir dist/abi3
```

The profile pins the official PyPA image by digest and Rust 1.95.0. It enables
the actual PyO3 limited API, repairs/checks the Linux symbol policy, audits the
stable ABI, requires all seven Rust entry points and Cython absence, and runs
the full test directory inside the manylinux container. CI uses this profile,
then tests the identical artifact on CPython 3.10–3.14. The normal Cython matrix
stays available for strict compiled parity.

Executed source-only evidence at `5e42f17`: 470 tracked files, no prebuilt
libraries, **176 tests on glibc 2.28 / CPython 3.10.22**, plus **176 tests,
zero skips on each CPython 3.10–3.14** using the same artifact. `auditwheel`
confirms the actual required floor is glibc 2.28; `abi3audit --strict` reports
zero violations/mismatches and a Python 3.10 baseline. Exactly one native
library is included. Two fresh container builds with the same source timestamp
produce a byte-identical complete wheel, SHA256:

`1e9c859e8063a16e5146d6a09f43592cd2fc421485ba13ff94201f81f1465362`

[Machine-readable source, tool, audit and runtime evidence](../dev/packaging/2026-11-14-manylinux.json).
Observed build dependencies are recorded there; this establishes repeatability
for that source/tool environment, not arbitrary future dependency versions or
other platforms. The timestamp is automatically forwarded by cibuildwheel.
[Official image/platform policy](https://github.com/pypa/manylinux),
[ABI3 auditing](https://cibuildwheel.pypa.io/en/stable/faq/#building-cpython-abi3-wheels-limited-api),
[timestamp forwarding](https://cibuildwheel.pypa.io/en/stable/options/#environment-pass).

Five-repeat installed graph measurements compare
[the native CPython wheel](../dev/benchmarks/2026-11-14-native-wheel-graph.json)
with [the portable wheel](../dev/benchmarks/2026-11-14-manylinux-wheel-graph.json),
228 rows each. All objectives agree and public witnesses are independently
rescored. Median portable/native public runtime ratios are **1.029** (2016)
and **1.012** (2018); raw binding ratios are **1.013** and **1.009**. Shared-VM
noise affects individual rows. The artifact's native code is partially verified;
portable packaging adds no mathematical or Rust refinement claim.

The rooted graph API update is also validated from a source-only archive of
`e272d36`: **199 tests, zero skips**, on the glibc floor and each CPython
3.10–3.14, with Linux repair and strict ABI auditing clean. Its wheel SHA256 is
`77c449c1c6683b54c8db0bf8ad4f28cac0c135293e01b509971d624000b2d18f`.
The `rooted_graph_api_update` ledger entry records this later source/artifact;
the byte-reproducibility experiment above remains its separate 176-test baseline.

## Executed Linux validation, 2026-11-14

The genuine stable wheel contains exactly one native library. `abi3audit
--strict` reports a computed/minimum ABI of **3.10**, **zero violations** and
**zero version mismatches**. The same package/binary payload passes **149 tests,
zero skips on each CPython 3.10, 3.11, 3.12, 3.13 and 3.14**, with all seven
Rust entry points required and Cython explicitly absent. These runs execute
the independent objective/witness oracles, integer boundaries and error cases.
[Machine-readable evidence](../dev/packaging/2026-11-14-abi3.json) includes wheel
and extension hashes, runtime/library versions, required entry points and the
raw ABI audit. CI now builds/audits one wheel and tests it across the same
runtime matrix; the existing separate job requires Rust **and Cython** parity.
Remote execution of the new CI configuration remains pending.

Subsequent root-preserving isomorphism and token/Unicode updates pass **161
tests, zero skips** in the normal wheel and on each ABI3 runtime. Their wheel,
binary and audit records are appended under `rooted_api_update` and
`token_api_update` in the evidence file; the initial measurements above remain
recorded as the original packaging baseline.

A source-only archive of `3d68c00` matches all 423 tracked paths and contains
no shared libraries. Building an sdist from it, then building both wheel modes
from the unpacked sdist, succeeds without checkout build artifacts. The normal
wheel passes 149 tests with Rust/Cython mandatory; the stable wheel passes 149
on Python 3.10 and strict ABI auditing. Its Rust binary is byte-identical to
the checkout build. Source/wheel hashes are in the same evidence file. This
establishes a source-build path; bit-for-bit reproducibility of complete wheel
archives across build environments remains a separate release requirement.

Installed Python 3.13 API timings use the existing repeated workload suites:
[ordered fractional affinities](../dev/benchmarks/2026-11-14-abi3-ordered-weighted.json)
and [unordered graph APIs](../dev/benchmarks/2026-11-14-abi3-unordered.json).
Median ABI3/version-specific runtime ratios are 1.006/1.049 for ordered
embedding/isomorphism, and 1.035/1.058 for 2018/2016 graph algorithms. These
shared-VM, small-workload ratios characterize this run; individual cases vary.
All scores agree and graph witnesses are independently rescored.

The earlier local builds used `linux_x86_64`; the portable Linux path is now
validated above. macOS/Windows stable-ABI artifacts, wider architectures and
their runtime tests remain packaging work. Remote CI execution remains pending.
The default Cython-inclusive distribution is unchanged. These development artifacts are
partially verified; complete production-source and applicable complexity
proofs still block the final verified release.

The positive-infinity scoring update at `5d7fabd` has also been rebuilt from a
source-only archive through the pinned portable profile. Its wheel passes all
209 tests on glibc 2.28 and each host CPython 3.10–3.14, with strict ABI
auditing clean. This is a separate artifact from the rooted 199-test milestone;
its exact source, wheel and native hashes are recorded in the packaging ledger.
