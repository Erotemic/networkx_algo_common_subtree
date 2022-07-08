"""
Algorithm extensions
"""
__version__ = '0.1.0'

__mkinit__ = """
mkinit -m networkx_algo_common_subtree
"""
from networkx_algo_common_subtree import balanced_embedding
from networkx_algo_common_subtree import balanced_isomorphism
from networkx_algo_common_subtree import balanced_sequence
from networkx_algo_common_subtree import tree_embedding
from networkx_algo_common_subtree import tree_isomorphism
from networkx_algo_common_subtree import utils

from networkx_algo_common_subtree.balanced_embedding import (
    available_impls_longest_common_balanced_embedding,
    longest_common_balanced_embedding,)
from networkx_algo_common_subtree.balanced_isomorphism import (
    available_impls_longest_common_balanced_isomorphism,
    balanced_decomp_unsafe_nocat, generate_all_decomp_nocat,
    longest_common_balanced_isomorphism,)
from networkx_algo_common_subtree.balanced_sequence import (
    random_balanced_sequence,)
from networkx_algo_common_subtree.tree_embedding import (
    maximum_common_ordered_subtree_embedding,)
from networkx_algo_common_subtree.tree_isomorphism import (
    maximum_common_ordered_subtree_isomorphism,)
from networkx_algo_common_subtree.utils import (forest_str,
                                                random_ordered_tree,
                                                random_tree,)

__all__ = ['available_impls_longest_common_balanced_embedding',
           'available_impls_longest_common_balanced_isomorphism',
           'balanced_decomp_unsafe_nocat', 'balanced_embedding',
           'balanced_isomorphism', 'balanced_sequence', 'forest_str',
           'generate_all_decomp_nocat', 'longest_common_balanced_embedding',
           'longest_common_balanced_isomorphism',
           'maximum_common_ordered_subtree_embedding',
           'maximum_common_ordered_subtree_isomorphism',
           'random_balanced_sequence', 'random_ordered_tree', 'random_tree',
           'tree_embedding', 'tree_isomorphism', 'utils']
