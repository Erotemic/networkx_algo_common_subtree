from __future__ import annotations

import json

from networkx_algo_common_subtree.pytorch_sized_trees import (
    benchmark_cases_json,
    make_benchmark_tree_pairs,
    make_resnet_module_tree,
    resnet50_spec,
    resnet101_spec,
)


def test_resnet_like_module_tree_sizes_are_pytorch_sized():
    resnet50 = make_resnet_module_tree(resnet50_spec())
    resnet101 = make_resnet_module_tree(resnet101_spec())

    assert resnet50.n_nodes >= 150
    assert resnet50.n_edges == resnet50.n_nodes - 1
    assert resnet101.n_nodes > resnet50.n_nodes
    assert resnet101.n_edges == resnet101.n_nodes - 1


def test_perturbed_cases_are_valid_trees_and_include_expected_variants():
    cases = make_benchmark_tree_pairs()
    names = {case.name for case in cases}
    assert "resnet50_vs_wrapped_convolutions" in names
    assert "resnet50_vs_squeeze_excitation" in names
    assert "resnet50_vs_resnet101" in names

    for case in cases:
        left = case.left.to_reference_tree()
        right = case.right.to_reference_tree()
        assert left.n == case.left.n_nodes
        assert right.n == case.right.n_nodes
        assert len(case.left.edges) == case.left.n_nodes - 1
        assert len(case.right.edges) == case.right.n_nodes - 1


def test_json_export_is_stable_and_self_describing():
    payload = json.loads(benchmark_cases_json())
    assert payload["schema"] == "networkx_algo_common_subtree.pytorch_sized_tree_pairs.v1"
    assert payload["edge_label_names"]["0"] == "contains"
    assert payload["cases"]
    first = payload["cases"][0]
    assert first["left"]["label_names"]
    assert len(first["left"]["node_labels"]) == len(first["left"]["node_names"])
