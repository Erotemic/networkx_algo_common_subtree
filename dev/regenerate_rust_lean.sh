#!/usr/bin/env bash
# Regenerate the maintained Rust source's Lean semantics with pinned releases.
set -euo pipefail
repo_root=$(cd "$(dirname "$0")/.." && pwd)
release=nightly-2026.11.09-5a392f4
archive_sha256=54982f0f6bb8ec7080ef9d2a23932aebe6e3c032f32015963bbccc43103f723a
cache_root=${XDG_CACHE_HOME:-$HOME/.cache}/common-subtree-verification
binary_dir=${AENEAS_BIN_DIR:-$cache_root/$release}
check=0
if [[ ${1:-} == --check ]]; then check=1; shift; fi
if [[ $# != 0 ]]; then echo 'usage: dev/regenerate_rust_lean.sh [--check]' >&2; exit 2; fi
if [[ ! -x $binary_dir/aeneas || ! -x $binary_dir/charon ]]; then
    if [[ $(uname -s) != Linux || $(uname -m) != x86_64 ]]; then
        echo 'Set AENEAS_BIN_DIR to the pinned release for this platform.' >&2
        exit 1
    fi
    mkdir -p "$binary_dir"
    archive=$(mktemp)
    curl --fail --location --silent --show-error \
        "https://github.com/AeneasVerif/aeneas/releases/download/$release/aeneas-linux-x86_64.tar.gz" \
        --output "$archive"
    printf '%s  %s\n' "$archive_sha256" "$archive" | sha256sum --check --status
    tar -xzf "$archive" -C "$binary_dir"
    rm "$archive"
fi
"$binary_dir/aeneas" -version | grep -Fx "aeneas $release" > /dev/null
rustup toolchain install nightly-2026-09-17 --profile minimal --component rustc-dev --component rust-src --component miri
output_dir=$(mktemp -d)
trap 'rm -rf "$output_dir"' EXIT
for entry in verified_ordered_core:VerifiedOrderedCore verified_assignment_core:VerifiedAssignmentCore; do
    crate_name=${entry%%:*}
    module_name=${entry#*:}
    cd "$repo_root/rust/crates/$crate_name"
    RUSTUP_TOOLCHAIN=nightly-2026-09-17 "$binary_dir/charon" cargo --preset=aeneas
    "$binary_dir/aeneas" -backend lean -abort-on-error -warnings-as-errors -no-progress-bar \
        -dest "$output_dir" -namespace "$crate_name" "$crate_name.llbc"
    maintained="$repo_root/proofs/SubtreeProofs/Rust/Generated/$module_name.lean"
    if [[ $check == 1 ]]; then
        diff -u "$maintained" "$output_dir/$module_name.lean"
    else
        cp "$output_dir/$module_name.lean" "$maintained"
    fi
done
