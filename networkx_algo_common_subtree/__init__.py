"""Fast ordered and weighted unordered common subtree algorithms for NetworkX."""
__version__ = '0.3.0'

__mkinit__ = """
mkinit -m networkx_algo_common_subtree -w
"""

__submodules__ = {
    'utils': [],
    'balanced_embedding': [],
    'balanced_isomorphism': [],
    'tree_embedding': ['maximum_common_ordered_subtree_embedding'],
    'tree_isomorphism': ['maximum_common_ordered_subtree_isomorphism'],
    'unordered': ['CommonSubtreeResult', 'available_unordered_backends',
                  'maximum_common_subtree_isomorphism',
                  'largest_weight_common_subtree_embedding_with_distance_penalty',
                  'score_common_subtree_isomorphism', 'score_common_subtree_embedding'],
    'matching': ['AssignmentResult', 'PartialMatchingResult', 'PartialMatchingFamily',
                 'min_cost_assignment', 'max_weight_partial_matching',
                 'max_weight_partial_matching_deletions'],
}

from networkx_algo_common_subtree import balanced_embedding
from networkx_algo_common_subtree import balanced_isomorphism
from networkx_algo_common_subtree import tree_embedding
from networkx_algo_common_subtree import tree_isomorphism
from networkx_algo_common_subtree import utils

from networkx_algo_common_subtree.tree_embedding import (
    maximum_common_ordered_subtree_embedding,)
from networkx_algo_common_subtree.tree_isomorphism import (
    maximum_common_ordered_subtree_isomorphism,)
from networkx_algo_common_subtree.unordered import (
    CommonSubtreeResult, available_unordered_backends,
    maximum_common_subtree_isomorphism,
    largest_weight_common_subtree_embedding_with_distance_penalty,
    score_common_subtree_isomorphism, score_common_subtree_embedding,
)
from networkx_algo_common_subtree.matching import (
    AssignmentResult, PartialMatchingResult, PartialMatchingFamily, min_cost_assignment,
    max_weight_partial_matching, max_weight_partial_matching_deletions,
)

__all__ = ['balanced_embedding', 'balanced_isomorphism',
           'maximum_common_ordered_subtree_embedding',
           'maximum_common_ordered_subtree_isomorphism', 'tree_embedding',
           'tree_isomorphism', 'utils', 'CommonSubtreeResult',
           'available_unordered_backends', 'maximum_common_subtree_isomorphism',
           'largest_weight_common_subtree_embedding_with_distance_penalty',
           'score_common_subtree_isomorphism', 'score_common_subtree_embedding',
           'AssignmentResult', 'PartialMatchingResult', 'min_cost_assignment',
           'max_weight_partial_matching', 'PartialMatchingFamily',
           'max_weight_partial_matching_deletions']
