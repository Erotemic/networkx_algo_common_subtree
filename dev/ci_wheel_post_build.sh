#!/usr/bin/env bash
# Project build hook called by xcookie after normal and release wheel builds.
set -euo pipefail

if [[ "${RUNNER_OS:-$(uname -s)}" == "Linux" && "$(uname -m)" == "x86_64" ]]; then
    python -m pip install build cibuildwheel==4.3.5 abi3audit
    SOURCE_DATE_EPOCH="$(git log -1 --format=%ct)"
    export SOURCE_DATE_EPOCH
    # Build from the filtered sdist so Docker never copies local build caches.
    portable_source_dir="$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/subtree-portable.XXXXXX")"
    trap 'rm -rf "$portable_source_dir"' EXIT
    python -m build --sdist --outdir "$portable_source_dir"
    # The independent ABI3 runtime matrix lives in verification.yml. This hook
    # adds the portable wheel to the normal xcookie wheelhouse for publication.
    CIBW_TEST_SKIP='*' python -m cibuildwheel "$portable_source_dir"/*.tar.gz --platform linux \
        --config-file dev/abi3-cibuildwheel.toml --output-dir wheelhouse
    abi3audit --strict --summary wheelhouse/*-cp310-abi3-*.whl
fi

python -m pip install packaging twine
python -m twine check --strict wheelhouse/*.whl
python dev/check_distributions.py wheelhouse --wheels-only
