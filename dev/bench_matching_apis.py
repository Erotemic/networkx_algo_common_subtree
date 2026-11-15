#!/usr/bin/env python3
"""Short installed exact matching-family measurements with witness rescoring.

The family is the source-proved recomputation reference, not the unfinished
sparse repair integration. The loop baseline independently invokes the public
single-instance API on each masked matrix. Their objective values must agree;
different optimal witnesses are accepted. Run outside the source checkout.
"""
import argparse
import hashlib
import json
import platform
import random
import statistics
import sys
import time
from pathlib import Path

import networkx_algo_common_subtree as common
from networkx_algo_common_subtree import _rust


def loop_family(weights):
    original = common.max_weight_partial_matching(weights)
    width = len(weights[0]) if weights else 0
    deleted = tuple(common.max_weight_partial_matching(
        [[None if j == removed else value for j, value in enumerate(row)] for row in weights])
        for removed in range(width))
    return common.PartialMatchingFamily(original, deleted)


def validate(weights, result, raw):
    original, deleted = result if raw else (result.original, result.without_right)
    width = len(weights[0]) if weights else 0
    assert len(deleted) == width
    scores = []
    for index, matching in enumerate([original, *deleted]):
        pairs, weight = matching if raw else (matching.pairs, matching.weight)
        assert all(0 <= i < len(weights) and 0 <= j < width and j != index-1
                   and weights[i][j] is not None for i, j in pairs)
        assert len({i for i, _ in pairs}) == len(pairs)
        assert len({j for _, j in pairs}) == len(pairs)
        assert sum(weights[i][j] for i, j in pairs) == weight
        scores.append(weight)
    return scores


def measure(call, repeat, warmup):
    for _ in range(warmup):
        call()
    samples = []
    for _ in range(repeat):
        start = time.perf_counter_ns()
        result = call()
        samples.append((time.perf_counter_ns() - start) / 1e9)
    return result, samples


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", default="4,8")
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--warmup", type=int, default=1)
    parser.add_argument("--seed", type=int, default=2016)
    parser.add_argument("--json", type=Path, required=True)
    args = parser.parse_args()
    sizes = [int(size) for size in args.sizes.split(",")]
    if min(sizes) < 1 or args.repeat < 1 or args.warmup < 0:
        parser.error("sizes/repeat must be positive and warmup nonnegative")
    rng = random.Random(args.seed)
    cases, rows = [], []
    for size in sizes:
        for shape, left, right in [("uniform", size, size), ("signed-sparse", size, size),
                                   ("unused-right", size, 2*size), ("tall", 2*size, size),
                                   ("nonpositive", size, size), ("zero-columns", size, 0)]:
            weights = [[1 if shape == "uniform" else None if shape == "unused-right" and j >= size
                        else rng.choice([None, -7, 0]) if shape == "nonpositive"
                        else rng.choice([None, -7, 0, 1, 9]) for j in range(right)] for _ in range(left)]
            case_id = len(cases)
            cases.append(dict(shape=shape, left_size=left, right_size=right, weights=weights))
            expected = None
            for backend, solve in [("public-family", common.max_weight_partial_matching_deletions),
                                   ("raw-pyo3-family", _rust.max_weight_partial_matching_deletions),
                                   ("public-single-loop", loop_family)]:
                result, samples = measure(lambda: solve(weights), args.repeat, args.warmup)
                scores = validate(weights, result, backend == "raw-pyo3-family")
                if expected is None:
                    expected = scores
                assert scores == expected
                row = dict(case_id=case_id, backend=backend, samples_seconds=samples,
                           median_seconds=statistics.median(samples), weights=scores)
                rows.append(row)
                print(json.dumps(row), flush=True)
    binary = Path(_rust.__file__)
    result = dict(python=sys.version, platform=platform.platform(), package_path=common.__file__,
                  extension_path=str(binary), extension_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  configuration=vars(args) | {"json": str(args.json)}, cases=cases, rows=rows)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
