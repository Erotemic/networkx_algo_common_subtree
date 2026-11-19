# Releasing the package

Version 0.3.0 ships fast ordered and weighted unordered algorithms, with
documented partial verification. Further production proof closure and verified
backend optimization are separate research work, not release gates.

## Prepare and validate

Update `pyproject.toml`, `networkx_algo_common_subtree/__init__.py` and
`CHANGELOG.md` together. From the repository root, prepare the local VM caches
with `dev/setup-build-caches.sh` and `dev/setup-build-caches.sh --status`.
Keep the complete CMake build directory on local disk:
Use Python 3.13 for release tooling (the archive checker requires Python 3.11+).

```bash
python -m pip install build twine packaging
python -m build --sdist --outdir /var/tmp/subtree-release-dist
python -m pip wheel /var/tmp/subtree-release-dist/*.tar.gz --no-deps \
  --wheel-dir /var/tmp/subtree-release-dist \
  -Cbuild-dir=/var/tmp/subtree-release-build -Ccmake.define.REQUIRE_RUST_EXTENSIONS=ON
python -m twine check --strict /var/tmp/subtree-release-dist/*.whl /var/tmp/subtree-release-dist/*.tar.gz
python dev/check_distributions.py /var/tmp/subtree-release-dist --tag v0.3.0
```

Install the wheel into a clean environment with test dependencies. From outside
the checkout, run `dev/check_release.py --require-rust --require-cython` and
the full test directory with `COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS=1`.
The checker rejects imports from the source tree, compares installed metadata
and runtime version, requires native APIs and executes public examples.

The ordinary wheel includes Rust and Cython. The portable Linux Rust-only
CP310 ABI3 profile is `dev/abi3-cibuildwheel.toml`; run its strict ABI audit and
test the same artifact on CPython 3.10–3.14. Optional verified Lean tests may
skip in ordinary wheels because its executable is intentionally not included.
The separate rational CI job requires that executable when testing that mode.

## Build/test gate and publication

`Package CI` (`tests.yml`) builds the source archive, rebuilds and tests its
wheel, builds platform wheels, audits the portable ABI3 wheel and exercises its
runtime matrix. Successful `release-ready` collects **only those tested
distributions** into the `release-dist` artifact with `SHA256SUMS`.
Mathematical/proof research CI is independent of this package release gate.

Once the candidate is reviewed, create a `v0.3.0` tag on that exact
tested commit. Manually dispatch `Publish tested release` (`publish.yml`) with
the successful Package CI run ID and tag. It checks the run, commit/tag identity,
distribution versions, README and saved checksums, then uploads those same
artifacts to PyPI. It reuses the repository's `TWINE_PASSWORD` PyPI API-token
secret; no removed setup.py, automatic branch publishing or signing-key
decryption is involved. See [Twine's publishing documentation](https://twine.readthedocs.io/en/stable/).

Do not tag, push or publish merely to test packaging. Local release evidence
must distinguish the platforms/runtimes actually exercised from jobs still
awaiting remote CI. GitHub release notes can use the corresponding changelog
section after successful publication.
