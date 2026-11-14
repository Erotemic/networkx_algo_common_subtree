#!/usr/bin/env python3
"""
Inspect, run, and report PyTorch-sized common-subtree benchmarks.

This helper runs the native Rust benchmark directly. Both graph families are
also available through the installed Python/PyO3 APIs; use
``dev/bench_unordered_apis.py --module-trees`` to measure those interfaces.
This Python helper keeps the benchmark
inputs easy to inspect, runs the Rust benchmark in a machine-readable mode, and
renders human-friendly tables for communicating score / match / runtime tradeoffs.

Examples:
    python dev/bench_pytorch_sized_common_subtree.py --summary
    python dev/bench_pytorch_sized_common_subtree.py --write-json dev/pytorch_sized_tree_cases.json
    python dev/bench_pytorch_sized_common_subtree.py --run-rust --report rich --write-results dev/pytorch_sized_results.jsonl
    python dev/bench_pytorch_sized_common_subtree.py --results dev/pytorch_sized_results.jsonl --report markdown
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from networkx_algo_common_subtree.benchmark_reports import (  # noqa: E402
    load_benchmark_results,
    parse_benchmark_results,
    print_benchmark_report,
)
from networkx_algo_common_subtree.pytorch_sized_trees import (  # noqa: E402
    benchmark_cases_json,
    make_benchmark_tree_pairs,
    write_benchmark_cases,
)


def _run_rust_benchmark(args) -> str:
    """Run the Rust benchmark target and return JSONL stdout."""

    env = os.environ.copy()
    env["COMMON_SUBTREE_BENCH_FORMAT"] = "jsonl"
    env["COMMON_SUBTREE_BENCH_PROFILE"] = args.profile
    env["COMMON_SUBTREE_BENCH_REPEAT"] = str(args.repeat)
    env["COMMON_SUBTREE_BENCH_WARMUP"] = str(args.warmup)
    env["COMMON_SUBTREE_BENCH_SKIP_PENALTY"] = str(args.skip_penalty)
    env["COMMON_SUBTREE_BENCH_SAMPLE_LIMIT"] = str(args.sample_limit)
    cmd = [
        "cargo",
        "bench",
        "--manifest-path",
        str(_REPO_ROOT / "rust/crates/common_subtree_algorithms/Cargo.toml"),
        "--bench",
        "pytorch_sized_trees",
    ]
    completed = subprocess.run(
        cmd,
        cwd=_REPO_ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    # Cargo prints build status and compiler diagnostics to stderr; benchmark rows
    # are emitted by the bench binary on stdout as JSONL.  Preserve stderr so a
    # failed benchmark command is actionable without re-running it by hand.
    if completed.stderr:
        sys.stderr.write(completed.stderr)
    if completed.returncode != 0:
        if completed.stdout:
            sys.stdout.write(completed.stdout)
        raise SystemExit(f"cargo benchmark failed with exit status {completed.returncode}")
    return completed.stdout


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--summary", action="store_true", help="print a compact CSV table of benchmark cases")
    parser.add_argument("--json", action="store_true", help="print the benchmark corpus JSON to stdout")
    parser.add_argument("--write-json", type=Path, default=None, help="write the benchmark corpus to this path")

    parser.add_argument("--run-rust", action="store_true", help="run the Rust benchmark and collect JSONL results")
    parser.add_argument("--results", type=Path, default=None, help="read existing benchmark results from JSONL/JSON/CSV")
    parser.add_argument("--write-results", type=Path, default=None, help="write raw benchmark results JSONL to this path")
    parser.add_argument(
        "--report",
        choices=["rich", "markdown", "json", "jsonl", "none"],
        default="none",
        help="render collected benchmark results",
    )
    parser.add_argument("--write-report", type=Path, default=None, help="write the rendered report to this path")
    parser.add_argument("--profile", choices=["quick", "full"], default="quick", help="Rust benchmark profile")
    parser.add_argument("--repeat", type=int, default=3, help="timed repetitions per Rust benchmark row")
    parser.add_argument("--warmup", type=int, default=1, help="warmup repetitions per Rust benchmark row")
    parser.add_argument("--skip-penalty", type=float, default=0.25, help="distance penalty for embedding benchmark")
    parser.add_argument("--sample-limit", type=int, default=6, help="sample matched module pairs stored in each result row")
    args = parser.parse_args(argv)

    cases = make_benchmark_tree_pairs()

    if args.summary or not any([args.json, args.write_json, args.run_rust, args.results, args.write_results, args.report != "none"]):
        print("case,left_nodes,right_nodes,left_edges,right_edges,description")
        for case in cases:
            print(
                f"{case.name},"
                f"{case.left.n_nodes},"
                f"{case.right.n_nodes},"
                f"{case.left.n_edges},"
                f"{case.right.n_edges},"
                f"{json.dumps(case.description)}"
            )

    if args.json:
        print(benchmark_cases_json(), end="")

    if args.write_json is not None:
        out_path = write_benchmark_cases(args.write_json)
        print(f"wrote {out_path}")

    raw_results = None
    if args.run_rust:
        raw_results = _run_rust_benchmark(args)
        if args.write_results is not None:
            args.write_results.parent.mkdir(parents=True, exist_ok=True)
            args.write_results.write_text(raw_results)
            print(f"wrote {args.write_results}")
    elif args.results is not None:
        raw_results = args.results.read_text()

    if args.report != "none":
        if raw_results is None:
            if args.results is None:
                raise SystemExit("--report requires --run-rust or --results")
            rows = load_benchmark_results(args.results)
        else:
            rows = parse_benchmark_results(raw_results)

        if args.write_report is None:
            print_benchmark_report(rows, report_format=args.report)
        else:
            args.write_report.parent.mkdir(parents=True, exist_ok=True)
            with args.write_report.open("w") as file:
                print_benchmark_report(rows, report_format=args.report, file=file)
            print(f"wrote {args.write_report}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
