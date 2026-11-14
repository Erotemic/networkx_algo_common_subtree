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

The locally built platform tag is `linux_x86_64`, not a portable manylinux
claim. Auditwheel repair, macOS/Windows artifacts, wider architectures and
their runtime tests remain packaging work. The production cibuildwheel matrix
and default distribution are unchanged. These development artifacts are
partially verified; complete production-source and applicable complexity
proofs still block the final verified release.
