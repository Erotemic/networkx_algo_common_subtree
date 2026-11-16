#!/usr/bin/env bash
# Mount this repository's nested Lean/Cargo caches on VM-local storage.
set -euo pipefail
repo_root=$(cd "$(dirname "$0")/.." && pwd -P)
mode=${1:---setup}
case "$mode" in
    --setup|--status|--unmount) ;;
    *) echo 'usage: dev/setup-build-caches.sh [--setup|--status|--unmount]' >&2; exit 2 ;;
esac
[[ $# -le 1 ]] || { echo 'expected at most one option' >&2; exit 2; }
tree_id=$(stat -c '%d:%i' "$repo_root")
cache_root=${SUBTREE_BUILD_CACHE_ROOT:-/var/cache/common-subtree/$tree_id}
[[ $cache_root = /* ]] || { echo 'cache root must be absolute' >&2; exit 1; }
is_local() {
    case "$1" in ext4|ext3|xfs|btrfs|f2fs|zfs) return 0 ;; *) return 1 ;; esac
}
paths=(proofs/.lake rust/target)
for manifest in "$repo_root"/proofs/experiments/*/lakefile.toml; do
    [[ -f $manifest ]] || continue
    project=${manifest%/lakefile.toml}
    paths+=("${project#"$repo_root/"}/.lake")
done
for manifest in "$repo_root"/rust/crates/*/Cargo.toml; do
    [[ -f $manifest ]] || continue
    project=${manifest%/Cargo.toml}
    paths+=("${project#"$repo_root/"}/target")
done
for relative in "${paths[@]}"; do
    destination=$repo_root/$relative
    source=$cache_root/$relative
    [[ ! -L $destination ]] || { echo "refusing symlink: $destination" >&2; exit 1; }
    if [[ $mode == --status ]]; then
        if mountpoint -q "$destination"; then
            printf '%s: bind-mounted (%s)\n' "$relative" "$(findmnt -n -o FSTYPE,SOURCE -T "$destination")"
        elif [[ -d $destination ]]; then
            printf '%s: plain directory (%s)\n' "$relative" "$(findmnt -n -o FSTYPE -T "$destination")"
        else
            printf '%s: absent\n' "$relative"
        fi
        continue
    fi
    if mountpoint -q "$destination"; then
        mounted=$(findmnt -n -o SOURCE -T "$destination")
        case "$mounted" in
            *"[$source]"|"$source") ;;
            *) echo "refusing unrelated mount: $destination <- $mounted" >&2; exit 1 ;;
        esac
        if [[ $mode == --unmount ]]; then
            sudo umount "$destination"
            printf '%s: unmounted\n' "$relative"
        else
            is_local "$(findmnt -n -o FSTYPE -T "$destination")" || exit 1
            printf '%s: already mounted\n' "$relative"
        fi
        continue
    fi
    [[ $mode != --unmount ]] || continue
    if is_local "$(findmnt -n -o FSTYPE -T "$repo_root")"; then
        printf '%s: repository already on local disk; no mount needed\n' "$relative"
        continue
    fi
    sudo mkdir -p "$source"
    sudo chown "$(id -u):$(id -g)" "$source"
    is_local "$(findmnt -n -o FSTYPE -T "$source")" || {
        echo "cache must be on local disk: $source" >&2; exit 1;
    }
    mkdir -p "$destination"
    sudo mount --bind "$source" "$destination"
    mountpoint -q "$destination"
    printf '%s: bind-mounted from %s\n' "$relative" "$source"
done
