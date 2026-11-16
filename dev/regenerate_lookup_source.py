#!/usr/bin/env python3
"""Regenerate the lookup operational program and its real extra-work mutation.

Uses the existing pinned Charon binary; does not modify production Rust or its
Aeneas-generated semantics. The mutant is compiled in a temporary copied crate.
"""
from __future__ import annotations

import argparse
import difflib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from reify_lookup_llbc import Reifier
import json


def extract(charon: Path, crate: Path, llbc: Path):
    subprocess.run([str(charon), "cargo", "--preset=aeneas", "--start-from",
                    "verified_ordered_core::memo_lookup", "--no-dedup-serialized-ast",
                    "--dest-file", str(llbc)], cwd=crate, check=True,
                   env={**os.environ, "RUSTUP_TOOLCHAIN": "nightly-2026-09-17"})
    return json.loads(llbc.read_bytes())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--charon", required=True, type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    charon = args.charon.resolve(strict=True)
    root = Path(__file__).resolve().parents[1]
    crate = root / "rust/crates/verified_ordered_core"
    maintained = root / "proofs/SubtreeProofs/Rust/Generated"
    with tempfile.TemporaryDirectory(prefix="subtree-lookup-source-") as temp:
        work = Path(temp)
        original = extract(charon, crate, work / "original.llbc")
        mutant = work / "mutant"
        mutant.mkdir()
        for file in ("Cargo.toml", "Cargo.lock"):
            shutil.copyfile(crate / file, mutant / file)
        for directory in ("src", "benches"):
            shutil.copytree(crate / directory, mutant / directory)
        lib = mutant / "src/lib.rs"
        source = lib.read_text()
        start = source.index("pub fn memo_lookup(")
        body = source.index("{", start) + 1
        lib.write_text(source[:body] + "\n    let _ = words_equal(left, left);\n" + source[body:])
        changed = extract(charon, mutant, work / "extra-compare.llbc")
        for data, namespace, filename in (
                (original, "Program", "LookupSourceProgram.lean"),
                (changed, "ExtraCompare", "LookupSourceExtraCompare.lean")):
            generated = Reifier(data).lean(namespace)
            target = maintained / filename
            if args.check:
                current = target.read_text()
                if current != generated:
                    print("".join(difflib.unified_diff(current.splitlines(keepends=True),
                          generated.splitlines(keepends=True), fromfile=str(target),
                          tofile="fresh extraction")), end="")
                    raise SystemExit(1)
            else:
                target.write_text(generated)


if __name__ == "__main__":
    main()
