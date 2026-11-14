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
    if shape not in {"chain", "star", "balanced", "random", "double-star"}:
        raise ValueError(f"unknown tree shape: {shape!r}")
    graph = nx.Graph()
    graph.add_nodes_from(range(n))
    rng = random.Random(seed)
    for u in range(1, n):
        parent = {"chain": u - 1, "star": 0, "balanced": (u - 1) // 2,
                  "double-star": 0 if u == 1 else u % 2}.get(shape)
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
    parser.add_argument("--shapes", default="chain,star,balanced,random,double-star,chain-star")
    parser.add_argument("--repeat", type=int, default=5)
    parser.add_argument("--warmup", type=int, default=1)
    parser.add_argument("--oracle-max-size", type=int, default=4)
    parser.add_argument("--seed", type=int, default=2018)
    parser.add_argument("--algorithm", choices=["both", "isomorphism", "embedding"], default="both")
    parser.add_argument("--weights", choices=["scalar", "callbacks"], default="scalar")
    parser.add_argument("--time-rescoring", action="store_true", help="Also time independent public witness validation")
    parser.add_argument("--module-trees", action="store_true", help="Also measure three existing ResNet-sized fixtures")
    parser.add_argument("--json", type=Path, required=True)
    args = parser.parse_args()
    if args.repeat < 1 or args.warmup < 0:
        parser.error("repeat must be positive and warmup nonnegative")
    workloads = []
    for n in map(int, filter(None, args.sizes.split(","))):
        for shape in args.shapes.split(","):
            for asymmetric in [False, True]:
                m = max(1, n // 2) if asymmetric else n
                ls, rs = ("chain", "star") if shape == "chain-star" else (shape, shape)
                workloads.append((shape, tree(ls, n, args.seed), tree(rs, m, args.seed + 1), {}))
    if args.module_trees:
        from networkx_algo_common_subtree.pytorch_sized_trees import make_benchmark_tree_pairs
        def graph(module):
            result = nx.Graph()
            result.add_nodes_from((u, {"label": label}) for u, label in enumerate(module.node_labels))
            result.add_edges_from((u, v, {"label": label}) for u, v, label in module.edges)
            return result
        fixtures = make_benchmark_tree_pairs()
        for case in [fixtures[0], fixtures[2], fixtures[6]]:
            workloads.append((case.name, graph(case.left), graph(case.right), {"node_label": "label", "edge_label": "label"}))
    rows = []
    for shape, left, right, labels in workloads:
        n, m = len(left), len(right)
        ll = [data.get("label", 0) for _, data in left.nodes(data=True)]
        rl = [data.get("label", 0) for _, data in right.nodes(data=True)]
        le = [(u, v, data.get("label", 0)) for u, v, data in left.edges(data=True)]
        re = [(u, v, data.get("label", 0)) for u, v, data in right.edges(data=True)]
        api_weights, raw_weights = {}, {}
        if args.weights == "callbacks":
            def node_weight(u, v):
                return 1.0 + .125 * (u % 3 == v % 3)
            def edge_weight(a, b):
                return .25 + .125 * (sum(a) % 3 == sum(b) % 3)
            api_weights = dict(node_weight=node_weight, edge_weight=edge_weight)
            # Raw timing starts from the same materialized score tables that
            # the installed public API prepares on every invocation.
            raw_weights = dict(
                node_weights=[[node_weight(u, v) if ll[u] == rl[v] else None for v in range(m)] for u in range(n)],
                edge_weights=[[edge_weight((u, v), (x, y)) if a == b else None
                               for x, y, b in re] for u, v, a in le],
            )
        for name, scorer, extra in [
            ("maximum_common_subtree_isomorphism", common.score_common_subtree_isomorphism, {}),
            ("largest_weight_common_subtree_embedding_with_distance_penalty", common.score_common_subtree_embedding,
             {"skip_vertex_penalty": .25}),
        ]:
            if args.algorithm == "isomorphism" and name != "maximum_common_subtree_isomorphism":
                continue
            if args.algorithm == "embedding" and name == "maximum_common_subtree_isomorphism":
                continue
            values = []
            for backend in ["rust", "raw-pyo3"] + (["python"] if max(n, m) <= args.oracle_max_size else []):
                if backend == "raw-pyo3":
                    def call():
                        return getattr(_rust, name)(ll, le, rl, re, **raw_weights, **extra)
                else:
                    def call():
                        return getattr(common, name)(left, right, impl=backend, **labels, **api_weights, **extra)
                samples, result = measure(call, args.repeat, args.warmup)
                weight = result[0] if backend == "raw-pyo3" else result.weight
                rescore_samples = None
                if backend != "raw-pyo3":
                    def rescore():
                        return scorer(left, right, result, **labels, **api_weights, **extra)
                    if args.time_rescoring:
                        rescore_samples, rescored = measure(rescore, args.repeat, args.warmup)
                    else:
                        rescored = rescore()
                    assert rescored == weight
                values.append(weight)
                row = dict(algorithm=name, shape=shape, left_size=n, right_size=m, backend=backend, weights=args.weights,
                           samples_seconds=samples, median_seconds=statistics.median(samples), weight=weight)
                if rescore_samples is not None:
                    row.update(rescore_samples_seconds=rescore_samples,
                               rescore_median_seconds=statistics.median(rescore_samples))
                rows.append(row)
                print(json.dumps(row), flush=True)
            assert len(set(values)) == 1, (name, shape, n, m, values)
    binary = Path(_rust.__file__)
    result = dict(python=sys.version, platform=platform.platform(), processor=platform.processor(),
                  package_path=common.__file__, extension_path=str(binary),
                  extension_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  configuration=vars(args) | {"json": str(args.json)}, rows=rows)
    try:
        import resource
        # Whole-process high-water mark, including Python, all solvers and any
        # oracle runs. It is not a per-solver allocation/peak measurement.
        result["process_peak_rss_bytes"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == "darwin" else 1024)
    except ImportError:
        result["process_peak_rss_bytes"] = None
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
