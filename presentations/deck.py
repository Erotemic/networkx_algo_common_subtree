"""Stable presentation composition; one scene can be reused in several decks.

Keep the chapter order out of the renderer.  Scene modules own mathematical
content; this manifest owns presentation ordering and export naming.
"""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Deck:
    slug: str
    scenes: tuple[str, ...]


MATHEMATICS = Deck(
    slug="common-subtree-mathematics",
    scenes=(
        "AllProblems", "OrderedContraction", "BalancedWords",
        "DeletionIsContraction", "OrderedRecurrence", "CorrectnessAndComplexity",
        "AffinityExtensions", "WeightedUnorderedMatching",
        "SparseMatchingOptimization", "TopologicalDistancePenalties",
        "MappedAndSkippedStates", "ProofBoundary", "ApplicationExperiment",
        "PaperContribution",
    ),
)


__all__ = ["Deck", "MATHEMATICS"]
