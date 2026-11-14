//! Graph-only Rust implementations for weighted common subtree algorithms.
//!
//! The algorithms in this crate are based on the public descriptions in:
//!
//! - A. Droschinsky, N. M. Kriege, and P. Mutzel, "Faster Algorithms for the
//!   Maximum Common Subtree Isomorphism Problem" (arXiv:1602.07210). In this
//!   crate, *maximum common subtree isomorphism* is sometimes abbreviated as
//!   **MCSI** in comments or test names.
//! - A. Droschinsky, N. M. Kriege, and P. Mutzel, "Largest Weight Common
//!   Subtree Embeddings with Distance Penalties" (arXiv:1805.00821).
//!
//! This crate is independent of PyO3. Its typed APIs are consumed by the Python
//! extension in `rust/` and by native benchmarks. Independent exhaustive tests
//! validate its witnesses/objectives. Related matching families and fixed-left
//! orientations improve both solvers; f64 source refinement and formal published
//! runtime proofs remain open, including the 2018 constant-time view lookup.

pub mod matching;
pub mod model_trees;
pub mod tree;

pub use matching::{
    max_weight_bipartite_matching, max_weight_bipartite_matching_with_right_deletions,
    WeightedMatching, WeightedMatchingFamily,
};
pub use model_trees::{
    label_name, make_benchmark_tree_pairs, make_resnet_module_tree, BenchmarkTreePair, ModuleTree,
    ModuleTreeSpec,
};
pub use tree::{
    largest_weight_common_subtree_embedding_with_distance_penalty,
    largest_weight_nonempty_common_subtree_embedding_with_distance_penalty,
    maximum_common_subtree_isomorphism, maximum_nonempty_common_subtree_isomorphism, CommonSubtree,
    EdgeRef, ExactLabelScoring, LabeledTree, NodeId, Scoring,
};

/// Weight type used by the algorithms.
pub type Weight = f64;
