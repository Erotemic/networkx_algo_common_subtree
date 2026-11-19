#!/usr/bin/env python3
"""Check installed release metadata, native endpoints and documented examples."""
import argparse
from importlib import metadata
from pathlib import Path

import networkx as nx
import networkx_algo_common_subtree as common


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-rust", action="store_true")
    parser.add_argument("--require-cython", action="store_true")
    parser.add_argument("--version")
    args = parser.parse_args()
    checkout = Path(__file__).resolve().parents[1]
    package = Path(common.__file__).resolve()
    assert checkout not in package.parents, f"testing checkout instead of installed distribution: {package}"
    version = metadata.version("networkx_algo_common_subtree")
    assert common.__version__ == version, (common.__version__, version)
    if args.version:
        assert version == args.version, (version, args.version)
    if args.require_rust:
        from networkx_algo_common_subtree import _rust
        expected = ["longest_common_balanced_embedding", "longest_common_balanced_isomorphism",
                    "maximum_common_token_embedding", "maximum_common_token_isomorphism",
                    "maximum_common_subtree_isomorphism",
                    "largest_weight_common_subtree_embedding_with_distance_penalty",
                    "min_cost_assignment", "max_weight_partial_matching",
                    "max_weight_partial_matching_deletions"]
        assert all(hasattr(_rust, name) for name in expected), "missing native algorithm endpoint"
        assert "rust" in common.available_unordered_backends()
    if args.require_cython:
        from networkx_algo_common_subtree import balanced_embedding_cython, balanced_isomorphism_cython
        assert balanced_embedding_cython.__file__ and balanced_isomorphism_cython.__file__

    impl = "rust" if args.require_rust else "auto"
    left, right = nx.path_graph(3), nx.path_graph(4)
    result = common.maximum_common_subtree_isomorphism(left, right, impl=impl)
    assert result.weight == 5
    assert common.score_common_subtree_isomorphism(left, right, result) == result.weight
    embedded = common.largest_weight_common_subtree_embedding_with_distance_penalty(
        left, right, skip_vertex_penalty=0.25, impl=impl)
    assert embedded.weight == 5
    assert common.score_common_subtree_embedding(left, right, embedded,
                                                skip_vertex_penalty=0.25) == embedded.weight
    ordered = nx.DiGraph([(0, 1), (0, 2)])
    _, _, value = common.maximum_common_ordered_subtree_isomorphism(
        ordered, ordered, node_affinity=None)
    assert value == 3
    if args.require_rust:
        assignment = common.min_cost_assignment([[3, -2], [0, 4]])
        assert assignment.cost == -2 and assignment.column_for_row == (1, 0)
        matching = common.max_weight_partial_matching([[None, 5], [-2, 3]])
        assert matching.weight == 5 and matching.pairs == ((0, 1),)
    print(f"Installed {version}: documented ordered/unordered APIs and native requirements pass ({package}).")


if __name__ == "__main__":
    main()
