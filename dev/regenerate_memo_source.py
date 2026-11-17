#!/usr/bin/env python3
"""Regenerate pinned concatenation/insertion source data and proposed normal forms.

The Lean source reader and kernel certificates validate the proposed forms;
Python rendering is not part of the semantic trust boundary.
"""
from __future__ import annotations

import argparse
import difflib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from reify_lookup_llbc import Reifier
from regenerate_lookup_source import source_lean

HELPERS = {"copy_word": "copyWord", "copy_result": "copyResult",
           "concatenate": "concatenate", "memo_insert": "insert"}
ARITIES = {"copy_word": 1, "copy_result": 1, "concatenate": 2, "memo_insert": 4}


def extract(charon: Path, crate: Path, target: Path):
    subprocess.run([str(charon), "cargo", "--preset=aeneas", "--start-from",
                    "verified_ordered_core::memo_insert", "--start-from",
                    "verified_ordered_core::concatenate", "--no-dedup-serialized-ast",
                    "--dest-file", str(target)], cwd=crate, check=True,
                   env={**os.environ, "RUSTUP_TOOLCHAIN": "nightly-2026-09-17"})
    return json.loads(target.read_bytes())


def render(data):
    yield "MemoSourceProgram.lean", Reifier(data, helpers=HELPERS, arities=ARITIES).lean(
        root_namespace="SubtreeProofs.Rust.MemoSource",
        import_module="SubtreeProofs.Rust.MemoSource")
    yield "MemoSourceInput.lean", source_lean(data, "Program",
        root_namespace="SubtreeProofs.Rust.MemoSource.Input",
        source_filename="memo-primitives.llbc", generator="dev/regenerate_memo_source.py")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--charon", required=True, type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    destination = root / "proofs/SubtreeProofs/Rust/Generated"
    with tempfile.TemporaryDirectory(prefix="subtree-memo-source-") as temp:
        data = extract(args.charon.resolve(strict=True), root / "rust/crates/verified_ordered_core",
                       Path(temp) / "memo-primitives.llbc")
        for filename, text in render(data):
            target = destination / filename
            if args.check:
                current = target.read_text()
                if current != text:
                    print("".join(difflib.unified_diff(current.splitlines(keepends=True),
                          text.splitlines(keepends=True), fromfile=str(target),
                          tofile="fresh extraction")), end="")
                    raise SystemExit(1)
            else:
                target.write_text(text)


if __name__ == "__main__":
    main()
