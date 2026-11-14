#!/usr/bin/env python3
"""Measure installed graph APIs and raw PyO3 calls on identical trees.

Run after installing a Release wheel, from outside the checkout with its Python
environment (or PYTHONPATH pointing at a wheel installation). Pure Python is
exhaustive and is restricted by --oracle-max-size. JSON records every timing,
workload, score and execution environment; score mismatches fail the run.
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

import networkx as nx
import networkx_algo_common_subtree as common
from networkx_algo_common_subtree import _rust


def tree(shape, n, seed):
    graph = nx.Graph()
    graph.add_nodes_from(range(n))
    rng = random.Random(seed)
    for u in range(1, n):
        parent = {"chain": u - 1, "star": 0, "balanced": (u - 1) // 2}.get(shape)
        graph.add_edge(u, rng.randrange(u) if parent is None else parent)
    return graph


def measure(call, repeat, warmup):
    for _ in range(warmup):
        call()
    samples = []
    for _ in range(repeat):
        start = time.perf_counter_ns()
        result = call()
        samples.append((time.perf_counter_ns() - start) / 1e9)
    return samples, result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", default="4,8,16,32")
    parser.add_argument("--shapes", default="chain,star,balanced,random")
    parser.add_argument("--repeat", type=int, default=5)
    parser.add_argument("--warmup", type=int, default=1)
    parser.add_argument("--oracle-max-size", type=int, default=4)
    parser.add_argument("--seed", type=int, default=2018)
    parser.add_argument("--json", type=Path, required=True)
    args = parser.parse_args()
    if args.repeat < 1 or args.warmup < 0:
        parser.error("repeat must be positive and warmup nonnegative")
    rows = []
    for n in map(int, args.sizes.split(",")):
        for shape in args.shapes.split(","):
            for asymmetric in [False, True]:
                m = max(1, n // 2) if asymmetric else n
                left, right = tree(shape, n, args.seed), tree(shape, m, args.seed + 1)
                le = [(u, v, 0) for u, v in left.edges]
                re = [(u, v, 0) for u, v in right.edges]
                for name, scorer, extra in [
                    ("maximum_common_subtree_isomorphism", common.score_common_subtree_isomorphism, {}),
                    ("largest_weight_common_subtree_embedding_with_distance_penalty", common.score_common_subtree_embedding,
                     {"skip_vertex_penalty": .25}),
                ]:
                    values = []
                    for backend in ["rust", "raw-pyo3"] + (["python"] if max(n, m) <= args.oracle_max_size else []):
                        if backend == "raw-pyo3":
                            def call():
                                return getattr(_rust, name)([0] * n, le, [0] * m, re, **extra)
                        else:
                            def call():
                                return getattr(common, name)(left, right, impl=backend, **extra)
                        samples, result = measure(call, args.repeat, args.warmup)
                        weight = result[0] if backend == "raw-pyo3" else result.weight
                        if backend != "raw-pyo3":
                            assert scorer(left, right, result, **extra) == weight
                        values.append(weight)
                        row = dict(algorithm=name, shape=shape, left_size=n, right_size=m, backend=backend,
                                   samples_seconds=samples, median_seconds=statistics.median(samples), weight=weight)
                        rows.append(row)
                        print(json.dumps(row), flush=True)
                    assert len(set(values)) == 1, (name, shape, n, m, values)
    binary = Path(_rust.__file__)
    result = dict(python=sys.version, platform=platform.platform(), processor=platform.processor(),
                  package_path=common.__file__, extension_path=str(binary),
                  extension_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  configuration=vars(args) | {"json": str(args.json)}, rows=rows)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
