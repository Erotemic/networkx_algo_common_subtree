//! Graph-only Rust reference implementations for weighted common subtree algorithms.
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
//! This crate is intentionally independent from the existing PyO3 extension in
//! `rust/`. It provides small, typed Rust APIs and tests that can be hardened
//! before a Python or NetworkX-facing wrapper is added.

pub mod matching;
pub mod tree;

pub use matching::{max_weight_bipartite_matching, WeightedMatching};
pub use tree::{
    largest_weight_common_subtree_embedding_with_distance_penalty,
    maximum_common_subtree_isomorphism, CommonSubtree, EdgeRef, ExactLabelScoring,
    LabeledTree, NodeId, Scoring,
};

/// Weight type used by the algorithms.
pub type Weight = f64;
