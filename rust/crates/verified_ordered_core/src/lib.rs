//! Safe, extraction-friendly operations for the ordered contraction solver.
//!
//! The first operation connects a contraction's edge budget to the independent
//! mathematical edge count. The solver and its refinement are developed next.

/// Remaining edge budget after exactly one contraction. A singleton tree has
/// no edge to contract, so an empty budget returns `None`.
pub fn remaining_edges_after_contraction(edges: u32) -> Option<u32> {
    if edges == 0 {
        None
    } else {
        Some(edges - 1)
    }
}
