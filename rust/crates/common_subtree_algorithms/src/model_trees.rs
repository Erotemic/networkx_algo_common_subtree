//! PyTorch-sized module-tree fixtures for benchmarks.
//!
//! These fixtures are deterministic, dependency-free approximations of PyTorch
//! module hierarchies. They are intentionally module-containment trees rather
//! than tensor data-flow graphs. The goal is to benchmark the common-subtree
//! algorithms on inputs whose scale and perturbations resemble partial
//! weight-loading between related ResNet-style models.

use crate::tree::LabeledTree;

/// Every synthetic module edge uses a single containment label.
pub const EDGE_CONTAINS: i64 = 0;

const LABEL_MODEL: i64 = 1;
const LABEL_STEM: i64 = 2;
const LABEL_STAGE: i64 = 3;
const LABEL_BLOCK: i64 = 4;
const LABEL_CONV1X1: i64 = 5;
const LABEL_CONV3X3: i64 = 6;
const LABEL_BATCHNORM: i64 = 7;
const LABEL_RELU: i64 = 8;
const LABEL_MAXPOOL: i64 = 9;
const LABEL_DOWNSAMPLE: i64 = 10;
const LABEL_AVGPOOL: i64 = 11;
const LABEL_LINEAR: i64 = 12;
const LABEL_DROPOUT: i64 = 13;
const LABEL_SQUEEZE_EXCITATION: i64 = 14;
const LABEL_SIGMOID: i64 = 15;
const LABEL_WRAPPER: i64 = 16;
const LABEL_ADAPTER: i64 = 17;

/// Return the stable human-readable label name used by synthetic module trees.
pub fn label_name(label: i64) -> &'static str {
    match label {
        LABEL_MODEL => "model",
        LABEL_STEM => "stem",
        LABEL_STAGE => "stage",
        LABEL_BLOCK => "block",
        LABEL_CONV1X1 => "conv1x1",
        LABEL_CONV3X3 => "conv3x3",
        LABEL_BATCHNORM => "batchnorm",
        LABEL_RELU => "relu",
        LABEL_MAXPOOL => "maxpool",
        LABEL_DOWNSAMPLE => "downsample",
        LABEL_AVGPOOL => "avgpool",
        LABEL_LINEAR => "linear",
        LABEL_DROPOUT => "dropout",
        LABEL_SQUEEZE_EXCITATION => "squeeze_excitation",
        LABEL_SIGMOID => "sigmoid",
        LABEL_WRAPPER => "wrapper",
        LABEL_ADAPTER => "adapter",
        _ => "unknown",
    }
}

/// Configuration for a synthetic ResNet-like module tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleTreeSpec {
    pub name: String,
    pub block_counts: [usize; 4],
    pub include_classifier: bool,
    pub squeeze_excitation: bool,
    pub wrap_convolutions: bool,
    pub extra_norm_after_conv2: bool,
    pub adapter_after_blocks: bool,
    pub dropout_after_classifier: bool,
}

impl ModuleTreeSpec {
    /// ResNet50-scale bottleneck counts: 3, 4, 6, 3.
    pub fn resnet50() -> Self {
        Self {
            name: "resnet50".to_string(),
            block_counts: [3, 4, 6, 3],
            include_classifier: true,
            squeeze_excitation: false,
            wrap_convolutions: false,
            extra_norm_after_conv2: false,
            adapter_after_blocks: false,
            dropout_after_classifier: false,
        }
    }

    /// ResNet101-scale bottleneck counts: 3, 4, 23, 3.
    pub fn resnet101() -> Self {
        Self {
            name: "resnet101".to_string(),
            block_counts: [3, 4, 23, 3],
            include_classifier: true,
            squeeze_excitation: false,
            wrap_convolutions: false,
            extra_norm_after_conv2: false,
            adapter_after_blocks: false,
            dropout_after_classifier: false,
        }
    }

    pub fn named(mut self, name: impl Into<String>) -> Self {
        self.name = name.into();
        self
    }

    pub fn with_squeeze_excitation(mut self) -> Self {
        self.squeeze_excitation = true;
        self
    }

    pub fn with_wrapped_convolutions(mut self) -> Self {
        self.wrap_convolutions = true;
        self
    }

    pub fn with_extra_norm_after_conv2(mut self) -> Self {
        self.extra_norm_after_conv2 = true;
        self
    }

    pub fn with_adapters(mut self) -> Self {
        self.adapter_after_blocks = true;
        self
    }

    pub fn with_classifier_dropout(mut self) -> Self {
        self.dropout_after_classifier = true;
        self
    }
}

/// A labeled tree plus human-readable module-path metadata.
#[derive(Clone, Debug)]
pub struct ModuleTree {
    pub name: String,
    pub tree: LabeledTree,
    pub node_names: Vec<String>,
}

impl ModuleTree {
    pub fn len(&self) -> usize {
        self.tree.len()
    }

    pub fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }
}

/// Benchmark pair used by the Rust benchmark target.
#[derive(Clone, Debug)]
pub struct BenchmarkTreePair {
    pub name: &'static str,
    pub left: ModuleTree,
    pub right: ModuleTree,
    pub description: &'static str,
}

struct TreeBuilder {
    name: String,
    node_labels: Vec<i64>,
    node_names: Vec<String>,
    edges: Vec<(usize, usize, i64)>,
}

impl TreeBuilder {
    fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            node_labels: Vec::new(),
            node_names: Vec::new(),
            edges: Vec::new(),
        }
    }

    fn add_node(&mut self, label: i64, node_name: String) -> usize {
        let node_id = self.node_labels.len();
        self.node_labels.push(label);
        self.node_names.push(node_name);
        node_id
    }

    fn add_child(&mut self, parent: usize, label: i64, node_name: String) -> usize {
        let child = self.add_node(label, node_name);
        self.edges.push((parent, child, EDGE_CONTAINS));
        child
    }

    fn finish(self) -> ModuleTree {
        let tree = LabeledTree::new(self.node_labels, &self.edges).expect("fixture must be a tree");
        ModuleTree {
            name: self.name,
            tree,
            node_names: self.node_names,
        }
    }
}

/// Build a deterministic ResNet-like PyTorch module hierarchy tree.
pub fn make_resnet_module_tree(spec: &ModuleTreeSpec) -> ModuleTree {
    let mut builder = TreeBuilder::new(spec.name.clone());
    let root = builder.add_node(LABEL_MODEL, spec.name.clone());

    let stem = builder.add_child(root, LABEL_STEM, format!("{}.stem", spec.name));
    add_conv_norm_relu(&mut builder, stem, &format!("{}.stem", spec.name), LABEL_CONV3X3);
    builder.add_child(stem, LABEL_MAXPOOL, format!("{}.stem.maxpool", spec.name));

    for (stage_offset, &block_count) in spec.block_counts.iter().enumerate() {
        let stage_index = stage_offset + 1;
        let stage = builder.add_child(root, LABEL_STAGE, format!("{}.layer{}", spec.name, stage_index));
        for block_index in 0..block_count {
            let prefix = format!("{}.layer{}.{}", spec.name, stage_index, block_index);
            let block = builder.add_child(stage, LABEL_BLOCK, prefix.clone());
            add_bottleneck_block(
                &mut builder,
                block,
                &prefix,
                block_index == 0 && stage_index > 1,
                spec,
            );
        }
    }

    if spec.include_classifier {
        let head = builder.add_child(root, LABEL_STAGE, format!("{}.head", spec.name));
        builder.add_child(head, LABEL_AVGPOOL, format!("{}.avgpool", spec.name));
        if spec.dropout_after_classifier {
            builder.add_child(head, LABEL_DROPOUT, format!("{}.dropout", spec.name));
        }
        builder.add_child(head, LABEL_LINEAR, format!("{}.fc", spec.name));
    }

    builder.finish()
}

fn add_conv_norm_relu(builder: &mut TreeBuilder, parent: usize, prefix: &str, conv_label: i64) {
    builder.add_child(parent, conv_label, format!("{}.conv", prefix));
    builder.add_child(parent, LABEL_BATCHNORM, format!("{}.bn", prefix));
    builder.add_child(parent, LABEL_RELU, format!("{}.relu", prefix));
}

fn add_conv_child(
    builder: &mut TreeBuilder,
    parent: usize,
    label: i64,
    node_name: String,
    wrap: bool,
) -> usize {
    if wrap {
        let wrapper = builder.add_child(parent, LABEL_WRAPPER, format!("{}_wrapper", node_name));
        builder.add_child(wrapper, label, node_name)
    } else {
        builder.add_child(parent, label, node_name)
    }
}

fn add_bottleneck_block(
    builder: &mut TreeBuilder,
    block: usize,
    prefix: &str,
    has_downsample: bool,
    spec: &ModuleTreeSpec,
) {
    add_conv_child(
        builder,
        block,
        LABEL_CONV1X1,
        format!("{}.conv1", prefix),
        spec.wrap_convolutions,
    );
    builder.add_child(block, LABEL_BATCHNORM, format!("{}.bn1", prefix));
    builder.add_child(block, LABEL_RELU, format!("{}.relu1", prefix));

    add_conv_child(
        builder,
        block,
        LABEL_CONV3X3,
        format!("{}.conv2", prefix),
        spec.wrap_convolutions,
    );
    builder.add_child(block, LABEL_BATCHNORM, format!("{}.bn2", prefix));
    builder.add_child(block, LABEL_RELU, format!("{}.relu2", prefix));
    if spec.extra_norm_after_conv2 {
        builder.add_child(block, LABEL_BATCHNORM, format!("{}.extra_norm_after_conv2", prefix));
    }

    add_conv_child(
        builder,
        block,
        LABEL_CONV1X1,
        format!("{}.conv3", prefix),
        spec.wrap_convolutions,
    );
    builder.add_child(block, LABEL_BATCHNORM, format!("{}.bn3", prefix));

    if spec.squeeze_excitation {
        let se = builder.add_child(block, LABEL_SQUEEZE_EXCITATION, format!("{}.se", prefix));
        builder.add_child(se, LABEL_AVGPOOL, format!("{}.se.avgpool", prefix));
        builder.add_child(se, LABEL_LINEAR, format!("{}.se.fc1", prefix));
        builder.add_child(se, LABEL_RELU, format!("{}.se.relu", prefix));
        builder.add_child(se, LABEL_LINEAR, format!("{}.se.fc2", prefix));
        builder.add_child(se, LABEL_SIGMOID, format!("{}.se.sigmoid", prefix));
    }

    if spec.adapter_after_blocks {
        let adapter = builder.add_child(block, LABEL_ADAPTER, format!("{}.adapter", prefix));
        builder.add_child(adapter, LABEL_CONV1X1, format!("{}.adapter.conv", prefix));
        builder.add_child(adapter, LABEL_BATCHNORM, format!("{}.adapter.bn", prefix));
    }

    if has_downsample {
        let down = builder.add_child(block, LABEL_DOWNSAMPLE, format!("{}.downsample", prefix));
        builder.add_child(down, LABEL_CONV1X1, format!("{}.downsample.0", prefix));
        builder.add_child(down, LABEL_BATCHNORM, format!("{}.downsample.1", prefix));
    }
}

/// Deterministic benchmark cases for PyTorch-sized module trees.
pub fn make_benchmark_tree_pairs() -> Vec<BenchmarkTreePair> {
    let base = make_resnet_module_tree(&ModuleTreeSpec::resnet50());
    let renamed = make_resnet_module_tree(&ModuleTreeSpec::resnet50().named("resnet50_renamed_modules"));
    let wrapped = make_resnet_module_tree(
        &ModuleTreeSpec::resnet50()
            .named("resnet50_wrapped_convs")
            .with_wrapped_convolutions(),
    );
    let extra_norm = make_resnet_module_tree(
        &ModuleTreeSpec::resnet50()
            .named("resnet50_extra_norm")
            .with_extra_norm_after_conv2(),
    );
    let se = make_resnet_module_tree(
        &ModuleTreeSpec::resnet50()
            .named("resnet50_se")
            .with_squeeze_excitation(),
    );
    let adapters = make_resnet_module_tree(
        &ModuleTreeSpec::resnet50()
            .named("resnet50_adapters")
            .with_adapters(),
    );
    let resnet101 = make_resnet_module_tree(&ModuleTreeSpec::resnet101());

    vec![
        BenchmarkTreePair {
            name: "resnet50_identical",
            left: base.clone(),
            right: base.clone(),
            description: "Identical ResNet50-scale module trees; the full tree should match.",
        },
        BenchmarkTreePair {
            name: "resnet50_name_changes_only",
            left: base.clone(),
            right: renamed,
            description: "Same labels and structure with different human-readable node names.",
        },
        BenchmarkTreePair {
            name: "resnet50_vs_wrapped_convolutions",
            left: base.clone(),
            right: wrapped,
            description: "Convolution leaves on the right are hidden behind wrapper modules.",
        },
        BenchmarkTreePair {
            name: "resnet50_vs_extra_norm",
            left: base.clone(),
            right: extra_norm,
            description: "The right tree has an extra normalization child inside each bottleneck block.",
        },
        BenchmarkTreePair {
            name: "resnet50_vs_squeeze_excitation",
            left: base.clone(),
            right: se,
            description: "The right tree has squeeze-excitation auxiliary modules in each block.",
        },
        BenchmarkTreePair {
            name: "resnet50_vs_adapters",
            left: base.clone(),
            right: adapters,
            description: "The right tree has adapter submodules in each block.",
        },
        BenchmarkTreePair {
            name: "resnet50_vs_resnet101",
            left: base,
            right: resnet101,
            description: "Different depths with the same ResNet-like block vocabulary.",
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resnet50_tree_has_expected_scale() {
        let tree = make_resnet_module_tree(&ModuleTreeSpec::resnet50());
        assert!(tree.len() >= 150, "expected ResNet50-scale tree, got {}", tree.len());
        assert_eq!(tree.tree.len(), tree.node_names.len());
    }

    #[test]
    fn perturbations_increase_tree_size() {
        let base = make_resnet_module_tree(&ModuleTreeSpec::resnet50());
        let wrapped = make_resnet_module_tree(&ModuleTreeSpec::resnet50().with_wrapped_convolutions());
        let se = make_resnet_module_tree(&ModuleTreeSpec::resnet50().with_squeeze_excitation());
        assert!(wrapped.len() > base.len());
        assert!(se.len() > base.len());
    }
}
