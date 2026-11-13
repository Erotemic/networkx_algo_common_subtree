"""
PyTorch-sized tree fixtures for common-subtree benchmarks.

The benchmark cases in this module intentionally model a PyTorch *module tree*,
not a full tensor data-flow graph.  The goal is to produce reproducible trees at
roughly ResNet50 / ResNet101 module-hierarchy scale without depending on
``torch`` or ``torchvision`` at benchmark time.

These fixtures are useful for the partial-weight-loading use case: compare two
similar model hierarchies where one side may contain inserted wrappers,
normalization layers, adapters, or squeeze-excitation style auxiliary modules.
The algorithms can then be timed on inputs that are much closer to model-zoo
sizes than the tiny proof-oracle examples.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass, replace
import json
from pathlib import Path
from typing import Iterable

from networkx_algo_common_subtree.common_subtree_reference import ReferenceLabeledTree

EDGE_CONTAINS = 0

LABEL_IDS: dict[str, int] = {
    "model": 1,
    "stem": 2,
    "stage": 3,
    "block": 4,
    "conv1x1": 5,
    "conv3x3": 6,
    "batchnorm": 7,
    "relu": 8,
    "maxpool": 9,
    "downsample": 10,
    "avgpool": 11,
    "linear": 12,
    "dropout": 13,
    "squeeze_excitation": 14,
    "sigmoid": 15,
    "wrapper": 16,
    "adapter": 17,
    "identity": 18,
}

LABEL_NAMES: dict[int, str] = {value: key for key, value in LABEL_IDS.items()}


@dataclass(frozen=True)
class ModuleTreeSpec:
    """Configuration for a synthetic ResNet-like module tree."""

    name: str
    block_counts: tuple[int, int, int, int] = (3, 4, 6, 3)
    include_classifier: bool = True
    squeeze_excitation: bool = False
    wrap_convolutions: bool = False
    extra_norm_after_conv2: bool = False
    adapter_after_blocks: bool = False
    dropout_after_classifier: bool = False


@dataclass(frozen=True)
class ModuleTree:
    """Integer-labeled tree plus human-readable metadata."""

    name: str
    node_labels: tuple[int, ...]
    edges: tuple[tuple[int, int, int], ...]
    node_names: tuple[str, ...]

    @property
    def n_nodes(self) -> int:
        return len(self.node_labels)

    @property
    def n_edges(self) -> int:
        return len(self.edges)

    def to_reference_tree(self) -> ReferenceLabeledTree:
        """Convert to the slow reference tree representation."""

        return ReferenceLabeledTree(self.node_labels, self.edges)

    def to_json_dict(self) -> dict:
        """Return a stable JSON-friendly representation."""

        return {
            "name": self.name,
            "node_labels": list(self.node_labels),
            "edges": [list(edge) for edge in self.edges],
            "node_names": list(self.node_names),
            "label_names": {str(key): value for key, value in sorted(LABEL_NAMES.items())},
        }


@dataclass(frozen=True)
class BenchmarkTreePair:
    """Pair of module trees used by benchmark CLIs and docs."""

    name: str
    left: ModuleTree
    right: ModuleTree
    description: str

    def to_json_dict(self) -> dict:
        return {
            "name": self.name,
            "description": self.description,
            "left": self.left.to_json_dict(),
            "right": self.right.to_json_dict(),
        }


class _TreeBuilder:
    def __init__(self, name: str):
        self.name = name
        self.node_labels: list[int] = []
        self.node_names: list[str] = []
        self.edges: list[tuple[int, int, int]] = []

    def add_node(self, label_name: str, node_name: str) -> int:
        node_id = len(self.node_labels)
        self.node_labels.append(LABEL_IDS[label_name])
        self.node_names.append(node_name)
        return node_id

    def add_child(self, parent: int, label_name: str, node_name: str) -> int:
        child = self.add_node(label_name, node_name)
        self.edges.append((parent, child, EDGE_CONTAINS))
        return child

    def finish(self) -> ModuleTree:
        return ModuleTree(
            name=self.name,
            node_labels=tuple(self.node_labels),
            edges=tuple(self.edges),
            node_names=tuple(self.node_names),
        )


def resnet50_spec(**overrides) -> ModuleTreeSpec:
    """Return the default ResNet50-scale module tree spec."""

    return replace(ModuleTreeSpec(name="resnet50", block_counts=(3, 4, 6, 3)), **overrides)


def resnet101_spec(**overrides) -> ModuleTreeSpec:
    """Return the default ResNet101-scale module tree spec."""

    return replace(ModuleTreeSpec(name="resnet101", block_counts=(3, 4, 23, 3)), **overrides)


def make_resnet_module_tree(spec: ModuleTreeSpec) -> ModuleTree:
    """Build a deterministic ResNet-like PyTorch module hierarchy tree.

    The tree is deliberately a module-containment tree.  Every edge has the same
    ``contains`` label so inserted wrapper modules can be crossed by the
    distance-penalized embedding benchmark.
    """

    builder = _TreeBuilder(spec.name)
    root = builder.add_node("model", spec.name)

    stem = builder.add_child(root, "stem", f"{spec.name}.stem")
    _add_conv_norm_relu(builder, stem, f"{spec.name}.stem", conv_label="conv3x3")
    builder.add_child(stem, "maxpool", f"{spec.name}.stem.maxpool")

    for stage_index, block_count in enumerate(spec.block_counts, start=1):
        stage = builder.add_child(root, "stage", f"{spec.name}.layer{stage_index}")
        for block_index in range(block_count):
            block = builder.add_child(
                stage,
                "block",
                f"{spec.name}.layer{stage_index}.{block_index}",
            )
            _add_bottleneck_block(
                builder,
                block,
                prefix=f"{spec.name}.layer{stage_index}.{block_index}",
                has_downsample=(block_index == 0 and stage_index > 1),
                spec=spec,
            )

    if spec.include_classifier:
        head = builder.add_child(root, "stage", f"{spec.name}.head")
        builder.add_child(head, "avgpool", f"{spec.name}.avgpool")
        if spec.dropout_after_classifier:
            builder.add_child(head, "dropout", f"{spec.name}.dropout")
        builder.add_child(head, "linear", f"{spec.name}.fc")

    return builder.finish()


def _add_conv_norm_relu(builder: _TreeBuilder, parent: int, prefix: str, *, conv_label: str) -> None:
    conv = builder.add_child(parent, conv_label, f"{prefix}.conv")
    builder.add_child(parent, "batchnorm", f"{prefix}.bn")
    builder.add_child(parent, "relu", f"{prefix}.relu")
    assert conv >= 0


def _add_conv_child(builder: _TreeBuilder, parent: int, label_name: str, node_name: str, *, wrap: bool) -> int:
    if wrap:
        wrapper = builder.add_child(parent, "wrapper", f"{node_name}_wrapper")
        return builder.add_child(wrapper, label_name, node_name)
    return builder.add_child(parent, label_name, node_name)


def _add_bottleneck_block(
    builder: _TreeBuilder,
    block: int,
    *,
    prefix: str,
    has_downsample: bool,
    spec: ModuleTreeSpec,
) -> None:
    _add_conv_child(builder, block, "conv1x1", f"{prefix}.conv1", wrap=spec.wrap_convolutions)
    builder.add_child(block, "batchnorm", f"{prefix}.bn1")
    builder.add_child(block, "relu", f"{prefix}.relu1")

    _add_conv_child(builder, block, "conv3x3", f"{prefix}.conv2", wrap=spec.wrap_convolutions)
    builder.add_child(block, "batchnorm", f"{prefix}.bn2")
    builder.add_child(block, "relu", f"{prefix}.relu2")
    if spec.extra_norm_after_conv2:
        builder.add_child(block, "batchnorm", f"{prefix}.extra_norm_after_conv2")

    _add_conv_child(builder, block, "conv1x1", f"{prefix}.conv3", wrap=spec.wrap_convolutions)
    builder.add_child(block, "batchnorm", f"{prefix}.bn3")

    if spec.squeeze_excitation:
        se = builder.add_child(block, "squeeze_excitation", f"{prefix}.se")
        builder.add_child(se, "avgpool", f"{prefix}.se.avgpool")
        builder.add_child(se, "linear", f"{prefix}.se.fc1")
        builder.add_child(se, "relu", f"{prefix}.se.relu")
        builder.add_child(se, "linear", f"{prefix}.se.fc2")
        builder.add_child(se, "sigmoid", f"{prefix}.se.sigmoid")

    if spec.adapter_after_blocks:
        adapter = builder.add_child(block, "adapter", f"{prefix}.adapter")
        builder.add_child(adapter, "conv1x1", f"{prefix}.adapter.conv")
        builder.add_child(adapter, "batchnorm", f"{prefix}.adapter.bn")

    if has_downsample:
        down = builder.add_child(block, "downsample", f"{prefix}.downsample")
        builder.add_child(down, "conv1x1", f"{prefix}.downsample.0")
        builder.add_child(down, "batchnorm", f"{prefix}.downsample.1")


def make_benchmark_tree_pairs() -> list[BenchmarkTreePair]:
    """Return deterministic PyTorch-sized benchmark cases."""

    base = make_resnet_module_tree(resnet50_spec())
    reordered_metadata_only = make_resnet_module_tree(resnet50_spec(name="resnet50_relabelled_names"))
    wrapped = make_resnet_module_tree(resnet50_spec(name="resnet50_wrapped_convs", wrap_convolutions=True))
    extra_norm = make_resnet_module_tree(resnet50_spec(name="resnet50_extra_norm", extra_norm_after_conv2=True))
    se = make_resnet_module_tree(resnet50_spec(name="resnet50_se", squeeze_excitation=True))
    adapters = make_resnet_module_tree(resnet50_spec(name="resnet50_adapters", adapter_after_blocks=True))
    resnet101 = make_resnet_module_tree(resnet101_spec())

    return [
        BenchmarkTreePair(
            name="resnet50_identical",
            left=base,
            right=base,
            description="Identical ResNet50-scale module trees; the full tree should match.",
        ),
        BenchmarkTreePair(
            name="resnet50_name_changes_only",
            left=base,
            right=reordered_metadata_only,
            description="Same labels and structure with different human-readable node names.",
        ),
        BenchmarkTreePair(
            name="resnet50_vs_wrapped_convolutions",
            left=base,
            right=wrapped,
            description="Convolution leaves on the right are hidden behind wrapper modules.",
        ),
        BenchmarkTreePair(
            name="resnet50_vs_extra_norm",
            left=base,
            right=extra_norm,
            description="The right tree has an extra normalization child inside each bottleneck block.",
        ),
        BenchmarkTreePair(
            name="resnet50_vs_squeeze_excitation",
            left=base,
            right=se,
            description="The right tree has squeeze-excitation auxiliary modules in each block.",
        ),
        BenchmarkTreePair(
            name="resnet50_vs_adapters",
            left=base,
            right=adapters,
            description="The right tree has adapter submodules in each block.",
        ),
        BenchmarkTreePair(
            name="resnet50_vs_resnet101",
            left=base,
            right=resnet101,
            description="Different depths with the same ResNet-like block vocabulary.",
        ),
    ]


def benchmark_cases_json() -> str:
    """Serialize benchmark cases as pretty JSON."""

    payload = {
        "schema": "networkx_algo_common_subtree.pytorch_sized_tree_pairs.v1",
        "edge_label_names": {str(EDGE_CONTAINS): "contains"},
        "cases": [case.to_json_dict() for case in make_benchmark_tree_pairs()],
    }
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def write_benchmark_cases(path: str | Path) -> Path:
    """Write the benchmark case corpus to JSON and return its path."""

    out_path = Path(path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(benchmark_cases_json())
    return out_path


__all__ = [
    "BenchmarkTreePair",
    "EDGE_CONTAINS",
    "LABEL_IDS",
    "LABEL_NAMES",
    "ModuleTree",
    "ModuleTreeSpec",
    "benchmark_cases_json",
    "make_benchmark_tree_pairs",
    "make_resnet_module_tree",
    "resnet50_spec",
    "resnet101_spec",
    "write_benchmark_cases",
]
