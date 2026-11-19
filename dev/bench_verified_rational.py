#!/usr/bin/env python3
"""Benchmark installed public graph APIs and independently rescore witnesses.

Run outside the checkout with an installed wheel on PYTHONPATH. All timed
requests include Python graph/token conversion, IPC, computation and readback.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import statistics
import time

import networkx as nx
import networkx_algo_common_subtree as package
from networkx_algo_common_subtree import maximum_common_ordered_subtree_isomorphism as solve
from networkx_algo_common_subtree import balanced_isomorphism_lean as lean_backend


def graph(size, shape, offset):
    result = nx.DiGraph()
    result.add_nodes_from(range(offset, offset + size))
    for child in range(1, size):
        parent = 0 if shape == "star" else child - 1 if shape == "chain" else (child - 1) // 2
        result.add_edge(offset + parent, offset + child)
    return result


def preorder(tree):
    return [node for root in tree if tree.in_degree(root) == 0
            for node in nx.dfs_preorder_nodes(tree, root)]


def affinity(left, right):
    return Fraction(1 + (left * 3 + right * 5) % 13, 8)


def integer_affinity(left, right):
    return 1 + (left * 3 + right * 5) % 13


def validate(result, left, right, rooted, weights=affinity):
    first, second, value = result
    assert set(first) <= set(left) and set(second) <= set(right)
    assert set(first.edges) <= set(left.edges) and set(second.edges) <= set(right.edges)
    li, ri = preorder(first), preorder(second)
    assert len(li) == len(ri)
    expected = sum((weights(a, b) for a, b in zip(li, ri)), Fraction())
    assert Fraction(value) == expected
    if rooted and li:
        assert li[0] == next(iter(left)) and ri[0] == next(iter(right))
    return str(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--sizes", default="8,16,32")
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--integer-weights", action="store_true")
    args = parser.parse_args()
    sizes = [int(value) for value in args.sizes.split(",")]
    if args.repeat < 1 or not sizes or min(sizes) < 1:
        parser.error("sizes and repeat must be positive")
    weights = integer_affinity if args.integer_weights else affinity
    executable = lean_backend._lean_executable()
    assert executable is not None
    records = []
    cold_start = time.perf_counter()
    solve(graph(1, "star", 0), graph(1, "star", 1000),
          node_affinity=weights, impl="verified-lean")
    cold_seconds = time.perf_counter() - cold_start
    for size in sizes:
        for shape in ("star", "chain", "balanced"):
            left, right = graph(size, shape, 0), graph(size, shape, 1000)
            for rooted in (False, True):
                scores = set()
                for impl in ("verified-lean", "iter-rust", "iter-cython", "iter"):
                    # Explicit backend requests fail if that native path is absent.
                    validate(solve(left, right, node_affinity=weights, impl=impl, rooted=rooted),
                             left, right, rooted, weights)
                    samples = []
                    for _ in range(args.repeat):
                        start = time.perf_counter()
                        result = solve(left, right, node_affinity=weights, impl=impl, rooted=rooted)
                        samples.append(time.perf_counter() - start)
                        scores.add(validate(result, left, right, rooted, weights))
                    records.append(dict(size=size, shape=shape, rooted=rooted, impl=impl,
                                        score=validate(result, left, right, rooted, weights),
                                        seconds=samples, median=statistics.median(samples)))
                assert len(scores) == 1, (size, shape, rooted, scores)
    from networkx_algo_common_subtree import _rust
    artifact = dict(package=package.__file__, python=platform.python_version(),
                    platform=platform.platform(), cold_lean_seconds=cold_seconds,
                    sizes=sizes, repeat=args.repeat, weight_mode="integer" if args.integer_weights else "dyadic",
                    executable_sha256=hashlib.sha256(executable.read_bytes()).hexdigest(),
                    rust_sha256=hashlib.sha256(Path(_rust.__file__).read_bytes()).hexdigest(),
                    records=records)
    status = Path(f"/proc/{lean_backend._worker.pid}/status")
    if status.exists():
        artifact["lean_worker_memory"] = [line for line in status.read_text().splitlines()
                                           if line.startswith(("VmRSS:", "VmHWM:"))]
    args.output.write_text(json.dumps(artifact, indent=2) + "\n")
    print(f"Recorded {len(records)} installed-API measurements in {args.output}")


if __name__ == "__main__":
    main()
