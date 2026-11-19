# Releasing the package

Version 0.3.0 ships fast ordered and weighted unordered algorithms, with
explicitly documented partial verification. Further proof closure and verified
backend optimization are separate research work.

## Generated CI and project hooks

xcookie owns `.github/workflows/tests.yml`, `checks.yml` and `release.yml`.
Configure `[tool.xcookie]` in `pyproject.toml`; keep project build/test behavior
in its hooks. Do not replace the generated workflows. `verification.yml` is
project-owned and retains the proof, native parity and ABI3 runtime checks.

Use the adjacent `../xcookie` checkout, including generator fixes in commit
`0de04bc` (Windows conditions, optional environment blocks and release action
version). In a development environment with that checkout installed:

```bash
python -m pip install -e ../xcookie xdoctest
xcookie generate . --only_generate='.github/workflows/*.yml' \
  --regen='.github/workflows/*.yml' --yes=true --interactive=false --use_vcs=false
```

This deliberately regenerates only the three xcookie workflows; it preserves
packaging, README and the separate verification workflow. The release policy
is documented in `../xcookie/docs/source/manual/release_workflow_design.rst`.

The configured installed-test command requires Rust/Cython, checks public APIs,
tests minimum NetworkX 2.8.8 on Python 3.10 and runs the Python suite. Native
extension stubs allow type checking from source without first compiling those
optional modules. They declare an opaque native boundary, not a new typed or
formal guarantee.

`ci_wheel_build_post_commands` invokes `dev/ci_wheel_post_build.sh` in both test
and release builds. On Linux x86_64 it builds/audits the additional Rust-only
CP310 ABI3 wheel from a filtered source archive and puts it in the ordinary
wheelhouse for publication. The independent ABI3 runtime matrix remains in
`verification.yml`; the hook does not add a release-time runtime matrix.

## Local distribution validation

Update `pyproject.toml`, package `__version__` and `CHANGELOG.md` together.
Use Python 3.13 for release tooling. Prepare VM caches with
`dev/setup-build-caches.sh` and `dev/setup-build-caches.sh --status`, and put
complete CMake build trees on local disk:

```bash
python -m pip install build twine packaging
python -m build --sdist --outdir /var/tmp/subtree-release-dist
python -m pip wheel /var/tmp/subtree-release-dist/*.tar.gz --no-deps \
  --wheel-dir /var/tmp/subtree-release-dist \
  -Cbuild-dir=/var/tmp/subtree-release-build -Ccmake.define.REQUIRE_RUST_EXTENSIONS=ON
python -m twine check --strict /var/tmp/subtree-release-dist/*.whl /var/tmp/subtree-release-dist/*.tar.gz
python dev/check_distributions.py /var/tmp/subtree-release-dist
```

Install the wheel into a clean environment. Outside the checkout, run
`dev/check_release.py --require-rust --require-cython` and the test directory
with `COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS=1`. Ordinary wheels intentionally
omit the compiled Lean executable, so ten optional Lean tests may skip. To test
that backend, provide it and set `COMMON_SUBTREE_REQUIRE_LEAN=1`.

`dev/abi3-cibuildwheel.toml` describes the portable glibc 2.28 Rust-only wheel;
audit it and exercise CPython 3.10–3.14. The default wheel includes Rust/Cython
for CPython 3.10–3.13. On macOS, project build configuration requests deployment
target **10.12**, matching the Rust Intel requirement. cibuildwheel raises this
for newer interpreters and ARM (at least 11.0). The reported Intel 10.9/10.12
mismatch is corrected in configuration; a remote macOS rerun remains required.
See [Rust's platform requirements](https://doc.rust-lang.org/rustc/platform-support/apple-darwin.html).

## Publish using xcookie's release flow

After review and green CI on `main`, the maintainer release command is:

```bash
git push origin main:release
```

`release.yml` rebuilds distributions and publishes them to PyPI. After live
publication succeeds, it creates or verifies `v$VERSION` at that commit and
creates the GitHub release for that exact tag. Maintainers do not pre-create a
version tag or dispatch the removed manual publisher. An existing tag is reused
only if it points to the same commit.

The generated workflow also exercises release packaging/publication to TestPyPI
on `main`. This project preserves the previous credential/signing policy via
explicit xcookie settings: token publication (`TWINE_PASSWORD` and
`TEST_TWINE_PASSWORD`) and encrypted-repository GPG material (`CI_SECRET`).
No authentication migration is imposed by this repair.

Local checksums are useful review aids. They are not a cross-workflow artifact
promotion requirement. Proof research is separate from the package release
policy. No push, tag or publication was performed during local preparation.
