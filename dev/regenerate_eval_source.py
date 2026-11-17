#!/usr/bin/env python3
"""Retain the complete pinned evaluator/public-core extraction as Lean JSON.

The maintained Lean reader is the source-control program decoder. No external
Python code normalizer is introduced for this expanded instruction fragment.
"""
from __future__ import annotations

import argparse
import difflib
from pathlib import Path
import tempfile

from regenerate_lookup_source import extract, source_lean


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--charon", required=True, type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    destination = root / "proofs/SubtreeProofs/Rust/Generated/SourceEvalInput.lean"
    with tempfile.TemporaryDirectory(prefix="subtree-eval-source-") as temp:
        data = extract(args.charon.resolve(strict=True), root / "rust/crates/verified_ordered_core",
                       Path(temp) / "evaluator.llbc",
                       roots=["verified_ordered_core::maximum_common_embedding"])
        text = source_lean(data, "Program", root_namespace="SubtreeProofs.Rust.SourceEval.Input",
                           source_filename="evaluator.llbc", generator="dev/regenerate_eval_source.py")
        if args.check:
            current = destination.read_text()
            if current != text:
                print("".join(difflib.unified_diff(current.splitlines(keepends=True), text.splitlines(keepends=True),
                                                fromfile=str(destination), tofile="fresh extraction")), end="")
                raise SystemExit(1)
        else:
            destination.write_text(text)


if __name__ == "__main__":
    main()
