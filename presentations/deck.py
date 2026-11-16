"""Standalone presentation manifests; rendering and visuals are independent.

Keep the 14-scene mixed deck for backwards compatibility.  The three newer
lectures are self-contained; shared source scenes are reused intentionally.
"""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Deck:
    slug: str
    scenes: tuple[str, ...]
    # A scene may live in a lecture-specific module or the original scene file.
    modules: tuple[tuple[str, str], ...] = ()

    def module_for(self, name: str) -> str:
        return dict(self.modules).get(name, 'scenes.py')


MATHEMATICS = Deck(
    slug='common-subtree-mathematics',
    scenes=(
        'AllProblems', 'OrderedContraction', 'BalancedWords',
        'DeletionIsContraction', 'OrderedRecurrence', 'CorrectnessAndComplexity',
        'AffinityExtensions', 'WeightedUnorderedMatching',
        'SparseMatchingOptimization', 'TopologicalDistancePenalties',
        'MappedAndSkippedStates', 'ProofBoundary', 'ApplicationExperiment',
        'PaperContribution',
    ),
)


def specialized(slug: str, module: str, names: tuple[str, ...],
                original: tuple[str, ...]) -> Deck:
    return Deck(slug=slug, scenes=names,
                modules=tuple((name,module) for name in names if name not in original))


LOZANO = specialized(
    'lozano-valiente-2004', 'lozano_scenes.py',
    (
        'L01Question', 'L02Order', 'OrderedContraction', 'L10ChildSiblingTraversal', 'BalancedWords',
        'L03Factorization', 'DeletionIsContraction', 'L04PrintedGap',
        'OrderedRecurrence', 'L05ValueTrace', 'L11RecurrenceReuse', 'L06Witness', 'L08StructuralCases',
        'L07StateBound', 'L09ShapeSensitivity', 'CorrectnessAndComplexity', 'AffinityExtensions',
    ),
    MATHEMATICS.scenes,
)

DROSCHINSKY = specialized(
    'droschinsky-2016-2018', 'droschinsky_scenes.py',
    (
        'D01Question', 'D02Unordered', 'D03Score', 'D04RootRecurrence',
        'WeightedUnorderedMatching', 'D05MatchingAlternatives', 'D14AugmentingPath',
        'D06Assignment', 'D07Rerooting', 'SparseMatchingOptimization',
        'D11DualCut', 'D12DeletionReuse', 'D08Topology', 'D15BranchCollision', 'TopologicalDistancePenalties', 'MappedAndSkippedStates',
        'D09TwoStateTrace', 'D13Unrooted2018', 'D10Bounds',
    ),
    MATHEMATICS.scenes,
)

FORMALIZATION = specialized(
    'common-subtree-formalization', 'formalization_scenes.py',
    (
        'F01Question', 'F02Feasibility', 'F03Bridge', 'F04Countermodel',
        'F05ReferenceProof', 'F11IndependentEvidence', 'F06RustTranslation',
        'F07RustMemo', 'F08Assignment', 'F12Numbers', 'F09GraphProofs', 'ProofBoundary',
        'F10Research', 'ApplicationExperiment', 'PaperContribution',
    ),
    MATHEMATICS.scenes,
)

DECKS = {
    'lozano': LOZANO,
    'droschinsky': DROSCHINSKY,
    'formalization': FORMALIZATION,
    'mathematics': MATHEMATICS,  # prior combined presentation
}

__all__ = ['Deck', 'MATHEMATICS', 'LOZANO', 'DROSCHINSKY', 'FORMALIZATION', 'DECKS']
