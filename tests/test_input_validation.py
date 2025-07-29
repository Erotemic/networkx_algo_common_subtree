import networkx as nx
import pytest
from networkx_algo_common_subtree.tree_embedding import maximum_common_ordered_subtree_embedding
from networkx_algo_common_subtree.tree_isomorphism import maximum_common_ordered_subtree_isomorphism
from networkx_algo_common_subtree._types import OrderedDiGraph


def test_invalid_type_tree2_embedding():
    tree1 = OrderedDiGraph([(0, 1)])
    tree2 = nx.Graph([(0, 1)])  # not a directed ordered graph
    with pytest.raises(nx.NetworkXNotImplemented):
        maximum_common_ordered_subtree_embedding(tree1, tree2)


def test_invalid_type_tree2_isomorphism():
    tree1 = OrderedDiGraph([(0, 1)])
    tree2 = nx.Graph([(0, 1)])  # not a directed ordered graph
    with pytest.raises(nx.NetworkXNotImplemented):
        maximum_common_ordered_subtree_isomorphism(tree1, tree2)
