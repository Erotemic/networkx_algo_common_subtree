#!/usr/bin/env python3
"""Reproduce the bounded exact-score extraction experiment with pinned tools.

Called by regenerate_rust_lean.sh. Only Types.lean and Funs.lean are generated;
the external rational models and correctness proofs are maintained separately.
All compiler outputs use VM-local /var/tmp, including the rustc test executable.
"""
from __future__ import annotations

import argparse
import difflib
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--charon", type=Path, required=True)
    parser.add_argument("--aeneas", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    source = Path("proofs/experiments/ordered_score_model/score_model.rs")
    module = Path("SubtreeProofs/Rust/ScoreModel")
    env = {**os.environ, "RUSTUP_TOOLCHAIN": "nightly-2026-09-17"}
    with tempfile.TemporaryDirectory(prefix="subtree-score-model-", dir="/var/tmp") as directory:
        work = Path(directory)

        def extract(name, opaque):
            llbc = work / f"{name}.llbc"
            options = (["--opaque=score_model::arithmetic"] if opaque else [])
            subprocess.run([
                str(args.charon), "rustc", "--preset=aeneas",
                "--start-from=score_model::level_step", *options,
                "--dest-file", str(llbc), "--", "--crate-type=lib",
                "--crate-name", "score_model", str(source), "--out-dir", str(work),
            ], cwd=root, env=env, check=True)
            command = [
                str(args.aeneas), "-backend", "lean", "-abort-on-error",
                "-warnings-as-errors", "-no-progress-bar", "-split-files",
                "-namespace", "score_model", "-subdir", str(module),
                "-dest", str(work / name), str(llbc),
            ]
            return subprocess.run(command, cwd=root, text=True, capture_output=True)

        abstract = extract("abstract", opaque=True)
        if abstract.returncode:
            raise RuntimeError(abstract.stdout + abstract.stderr)
        for name in ("Types.lean", "Funs.lean"):
            generated = (work / "abstract" / module / name).read_text()
            target = root / "proofs" / module / name
            if args.check:
                current = target.read_text()
                if current != generated:
                    print("".join(difflib.unified_diff(
                        current.splitlines(keepends=True), generated.splitlines(keepends=True),
                        fromfile=str(target), tofile=f"regenerated/{name}")))
                    raise SystemExit(1)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(generated)

        native = extract("native", opaque=False)
        diagnostics = native.stdout + native.stderr
        if native.returncode == 0:
            raise RuntimeError("Native float extraction unexpectedly succeeded; reassess the spike.")
        if "Invalid inputs for binop" not in diagnostics:
            raise RuntimeError("Native extraction failed for an unexpected reason:\n" + diagnostics)
        print("Opaque score extraction passed; native float operations rejected as expected.")

        executable = work / "score-model-tests"
        subprocess.run(["rustc", "--test", str(source), "-o", str(executable)],
                       cwd=root, env=env, check=True)
        subprocess.run([str(executable)], check=True)
    print("Exact-score model regeneration checks passed.")


if __name__ == "__main__":
    main()
