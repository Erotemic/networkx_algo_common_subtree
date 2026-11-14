"""Exact integer weighted matching backed by the verified Rust core.

These functions require the PyO3 extension. Inputs are signed 64-bit integers;
totals and dual potentials are checked signed 128-bit integers, returned as
Python integers without a floating-point conversion. Indices are zero based.
The core algorithms have Lean source-refinement proofs; Python conversion and
these thin wrappers are covered by tests.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class AssignmentResult:
    """Minimum assignment with feasible, attaining row/column dual potentials."""
    column_for_row: tuple
    cost: int
    row_potential: tuple
    column_potential: tuple


@dataclass(frozen=True)
class PartialMatchingResult:
    """Maximum partial matching; omitted vertices are unmatched."""
    pairs: tuple
    weight: int


def min_cost_assignment(cost):
    """Minimize a square integer cost matrix, matching every row and column.

    Empty input has cost zero. Each returned dual satisfies
    ``row_potential[i] + column_potential[j] <= cost[i][j]``; their sum equals
    the optimum. Ragged/nonsquare matrices raise ``ValueError``. Values outside
    i64 or checked arithmetic overflow raise ``OverflowError``. Ties are
    deterministic for a fixed matrix. No integer is rounded through f64.
    """
    from . import _rust
    columns, total, rows, cols = _rust.min_cost_assignment(cost)
    return AssignmentResult(tuple(columns), total, tuple(rows), tuple(cols))


def max_weight_partial_matching(weights):
    """Maximize an optional integer rectangular weight matrix.

    ``None`` forbids an edge. Each row/column may appear at most once, and the
    empty matching (weight zero) is allowed. Negative edges need never be
    selected. Ragged matrices raise ``ValueError``; out-of-i64 values and
    checked arithmetic overflow raise ``OverflowError``. Ties are deterministic
    for a fixed matrix. ``[]`` and rows with zero columns have weight zero.
    """
    from . import _rust
    pairs, total = _rust.max_weight_partial_matching(weights)
    return PartialMatchingResult(tuple(pairs), total)


__all__ = ["AssignmentResult", "PartialMatchingResult", "min_cost_assignment", "max_weight_partial_matching"]
