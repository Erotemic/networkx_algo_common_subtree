"""
Algorithm extensions
"""
__version__ = '0.2.1'

__mkinit__ = """
mkinit -m networkx_algo_common_subtree -w
"""

__submodules__ = {
    'utils': [],
    'balanced_embedding': [],
    'balanced_isomorphism': [],
    'tree_embedding': ['maximum_common_ordered_subtree_embedding'],
    'tree_isomorphism': ['maximum_common_ordered_subtree_isomorphism'],
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

__all__ = ['balanced_embedding', 'balanced_isomorphism',
           'maximum_common_ordered_subtree_embedding',
           'maximum_common_ordered_subtree_isomorphism', 'tree_embedding',
           'tree_isomorphism', 'utils']
