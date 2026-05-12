#!/usr/bin/env python3
"""
Benchmark backend speedups for networkx_algo_common_subtree PR #30.

Usage from a checkout of the PR branch:

    python -m pip install -e '.[tests]'
    python dev/bench_backend_speedups.py --sizes 4,8,12,16,20,24 --cases 8 --repeat 5

For larger runs:

    python dev/bench_backend_speedups.py --sizes 8,16,24,32,40 --cases 20 --repeat 7 --json bench.json
"""

from __future__ import annotations

import argparse
import csv
import json
import random
import statistics as stats
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

from networkx_algo_common_subtree import balanced_embedding
from networkx_algo_common_subtree import balanced_isomorphism


OPEN_TO_CLOSE = {"(": ")", "[": "]", "{": "}"}
PAIRS = list(OPEN_TO_CLOSE.items())


@dataclass(frozen=True)
class Case:
    name: str
    seq1: str
    seq2: str
    open_to_close: dict[str, str]


def random_balanced_sequence(rng: random.Random, pairs: int, labels: int = 3) -> str:
    """
    Generate a random balanced bracket sequence with exactly `pairs` pairs.

    The generator recursively splits pairs across head/tail:
        seq -> open + head + close + tail
    """
    if pairs <= 0:
        return ""

    pair_choices = PAIRS[:labels]
    open_tok, close_tok = rng.choice(pair_choices)

    head_pairs = rng.randint(0, pairs - 1)
    tail_pairs = pairs - 1 - head_pairs

    head = random_balanced_sequence(rng, head_pairs, labels=labels)
    tail = random_balanced_sequence(rng, tail_pairs, labels=labels)
    return open_tok + head + close_tok + tail


def make_cases(
    *,
    sizes: list[int],
    cases_per_size: int,
    seed: int,
    labels: int,
) -> list[Case]:
    rng = random.Random(seed)
    cases: list[Case] = []

    # Include the examples from the new Rust backend tests / doc examples.
    cases.append(Case("small_brackets", "[][[]][]", "[[]][[]]", {"[": "]"}))
    cases.append(
        Case(
            "paper_1label",
            "0010010010111100001011011011",
            "001000101101110001000100101110111011",
            {"0": "1"},
        )
    )

    for n_pairs in sizes:
        for idx in range(cases_per_size):
            seq1 = random_balanced_sequence(rng, n_pairs, labels=labels)
            seq2 = random_balanced_sequence(rng, n_pairs, labels=labels)
            cases.append(
                Case(
                    name=f"random_pairs={n_pairs:04d}_case={idx:03d}",
                    seq1=seq1,
                    seq2=seq2,
                    open_to_close=dict(list(OPEN_TO_CLOSE.items())[:labels]),
                )
            )
    return cases


def median_time_seconds(
    func: Callable[[], object],
    *,
    repeat: int,
    warmup: int,
) -> tuple[float, object]:
    result = None

    for _ in range(warmup):
        result = func()

    times = []
    for _ in range(repeat):
        t0 = time.perf_counter_ns()
        result = func()
        t1 = time.perf_counter_ns()
        times.append((t1 - t0) / 1e9)

    return stats.median(times), result


def available_impls(kind: str) -> list[str]:
    if kind == "embedding":
        return balanced_embedding.available_impls_longest_common_balanced_embedding()
    if kind == "isomorphism":
        return balanced_isomorphism.available_impls_longest_common_balanced_isomorphism()
    raise KeyError(kind)


def call_backend(kind: str, case: Case, impl: str):
    if kind == "embedding":
        return balanced_embedding.longest_common_balanced_embedding(
            case.seq1,
            case.seq2,
            case.open_to_close,
            impl=impl,
        )
    if kind == "isomorphism":
        return balanced_isomorphism.longest_common_balanced_isomorphism(
            case.seq1,
            case.seq2,
            case.open_to_close,
            impl=impl,
        )
    raise KeyError(kind)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sizes", default="4,8,12,16,20")
    parser.add_argument("--cases", type=int, default=5, help="random cases per size")
    parser.add_argument("--repeat", type=int, default=5)
    parser.add_argument("--warmup", type=int, default=1)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--labels", type=int, default=3, choices=[1, 2, 3])
    parser.add_argument(
        "--functions",
        default="embedding,isomorphism",
        help="comma-separated subset: embedding,isomorphism",
    )
    parser.add_argument(
        "--impls",
        default="auto",
        help=(
            "comma-separated impls, or 'auto'. "
            "Recommended explicit value: iter-rust,iter-cython,iter"
        ),
    )
    parser.add_argument(
        "--reference",
        default="iter",
        help="backend used as denominator for speedup, usually iter or iter-cython",
    )
    parser.add_argument("--csv", type=Path, default=None)
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args(argv)

    sizes = [int(p) for p in args.sizes.split(",") if p]
    kinds = [p.strip() for p in args.functions.split(",") if p.strip()]
    cases = make_cases(
        sizes=sizes,
        cases_per_size=args.cases,
        seed=args.seed,
        labels=args.labels,
    )

    rows = []

    for kind in kinds:
        detected = available_impls(kind)
        if args.impls == "auto":
            # Avoid recurse by default: it is useful as a correctness backend,
            # but often unsuitable for larger benchmark inputs.
            impls = [p for p in ["iter-rust", "iter-cython", "iter"] if p in detected]
        else:
            requested = [p.strip() for p in args.impls.split(",") if p.strip()]
            impls = [p for p in requested if p in detected]

        print(f"\n# {kind}")
        print(f"available_impls={detected!r}")
        print(f"bench_impls={impls!r}")
        if args.reference not in impls:
            print(
                f"warning: reference={args.reference!r} not measured for {kind}; "
                "speedup_vs_reference will be null",
                file=sys.stderr,
            )

        for case in cases:
            by_impl = {}
            value_by_impl = {}

            for impl in impls:
                def _run(impl=impl, case=case, kind=kind):
                    return call_backend(kind, case, impl)

                try:
                    seconds, result = median_time_seconds(
                        _run,
                        repeat=args.repeat,
                        warmup=args.warmup,
                    )
                except Exception as ex:
                    row = {
                        "kind": kind,
                        "case": case.name,
                        "pairs1": len(case.seq1) // 2,
                        "pairs2": len(case.seq2) // 2,
                        "impl": impl,
                        "seconds": None,
                        "speedup_vs_reference": None,
                        "value": None,
                        "error": repr(ex),
                    }
                    rows.append(row)
                    print(f"{case.name:32s} {impl:12s} ERROR {ex!r}")
                    continue

                _best, value = result
                by_impl[impl] = seconds
                value_by_impl[impl] = value

                row = {
                    "kind": kind,
                    "case": case.name,
                    "pairs1": len(case.seq1) // 2,
                    "pairs2": len(case.seq2) // 2,
                    "impl": impl,
                    "seconds": seconds,
                    "speedup_vs_reference": None,
                    "value": value,
                    "error": None,
                }
                rows.append(row)

            # Correctness sanity check: all measured impls should agree on value.
            values = {impl: val for impl, val in value_by_impl.items()}
            if len(set(values.values())) > 1:
                print(f"VALUE MISMATCH: {kind} {case.name}: {values}", file=sys.stderr)

            ref_time = by_impl.get(args.reference)
            for row in rows:
                if row["kind"] == kind and row["case"] == case.name:
                    sec = row["seconds"]
                    if ref_time and sec:
                        row["speedup_vs_reference"] = ref_time / sec

            for impl in impls:
                sec = by_impl.get(impl)
                if sec is None:
                    continue
                speed = ref_time / sec if ref_time else None
                speed_text = "" if speed is None else f" speedup_vs_{args.reference}={speed:8.3f}x"
                print(f"{case.name:32s} {impl:12s} {sec:10.6f}s{speed_text}")

    if args.csv:
        args.csv.parent.mkdir(parents=True, exist_ok=True)
        with args.csv.open("w", newline="") as file:
            writer = csv.DictWriter(file, fieldnames=list(rows[0].keys()))
            writer.writeheader()
            writer.writerows(rows)
        print(f"\nwrote {args.csv}")

    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(rows, indent=2))
        print(f"wrote {args.json}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
