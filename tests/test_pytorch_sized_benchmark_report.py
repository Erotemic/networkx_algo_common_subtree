from __future__ import annotations

import json

from networkx_algo_common_subtree.benchmark_reports import (
    BenchmarkResult,
    benchmark_results_json,
    parse_benchmark_results,
    render_markdown_report,
)


def _fake_rows():
    return [
        BenchmarkResult(
            schema="networkx_algo_common_subtree.pytorch_sized_benchmark_result.v1",
            profile="quick",
            case="resnet50_vs_wrapped_convolutions",
            algorithm="isomorphism",
            left_nodes=166,
            right_nodes=214,
            median_seconds=0.0123,
            weight=250.0,
            node_pairs=120,
            left_match_ratio=120 / 166,
            right_match_ratio=120 / 214,
            warmup=1,
            repeat=3,
            sample_pairs=("resnet50.layer1.0.conv1 -> resnet50_wrapped.layer1.0.conv1",),
            label_counts=(("block", 16), ("conv1x1", 20)),
            description="Convolution leaves on the right are hidden behind wrapper modules.",
        ),
        BenchmarkResult(
            schema="networkx_algo_common_subtree.pytorch_sized_benchmark_result.v1",
            profile="quick",
            case="resnet50_vs_wrapped_convolutions",
            algorithm="embedding",
            left_nodes=166,
            right_nodes=214,
            median_seconds=0.0345,
            weight=330.0,
            node_pairs=166,
            left_match_ratio=1.0,
            right_match_ratio=166 / 214,
            skip_penalty=0.25,
            warmup=1,
            repeat=3,
            sample_pairs=("resnet50.layer1.0.conv1 -> resnet50_wrapped.layer1.0.conv1",),
            label_counts=(("block", 16), ("conv1x1", 32)),
            description="Convolution leaves on the right are hidden behind wrapper modules.",
        ),
    ]


def test_json_result_roundtrip_is_serializable():
    text = "".join(json.dumps(row.to_json_dict()) + "\n" for row in _fake_rows())
    rows = parse_benchmark_results(text)
    assert [row.algorithm for row in rows] == ["isomorphism", "embedding"]
    assert rows[1].skip_penalty == 0.25
    assert rows[1].label_counts[0] == ("block", 16)

    payload = json.loads(benchmark_results_json(rows))
    assert payload[0]["schema"].endswith("benchmark_result.v1")
    assert payload[1]["sample_pairs"]


def test_csv_result_parser_accepts_legacy_and_current_rows():
    text = "\n".join([
        "profile,case,algorithm,left_nodes,right_nodes,median_seconds,weight,node_pairs,left_match_ratio,right_match_ratio,skip_penalty,warmup,repeat,sample_pairs,label_counts,description",
        "quick,resnet50_identical,isomorphism,166,166,0.001,331,166,1.0,1.0,,1,3,root -> root,block:16 | conv1x1:35,identical",
    ])
    rows = parse_benchmark_results(text)
    assert rows[0].case == "resnet50_identical"
    assert rows[0].label_counts == (("block", 16), ("conv1x1", 35))


def test_markdown_report_compares_algorithms():
    report = render_markdown_report(_fake_rows())
    assert "Algorithm comparison" in report
    assert "resnet50_vs_wrapped_convolutions" in report
    assert "+46" in report
    assert "Representative" not in report  # markdown uses a simpler heading
    assert "Match detail" in report
