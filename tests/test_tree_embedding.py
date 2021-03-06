import networkx as nx
import pytest
from networkx.utils import create_py_random_state
from networkx_algo_common_subtree import balanced_embedding
from networkx_algo_common_subtree import maximum_common_ordered_subtree_embedding
from networkx_algo_common_subtree.utils import graph_str
from networkx_algo_common_subtree.utils import random_tree
from networkx_algo_common_subtree._types import OrderedDiGraph
from networkx_algo_common_subtree.tree_embedding import tree_to_seq


def test_null_common_embedding():
    """
    The empty graph is not a tree and should raise an error
    """
    empty = OrderedDiGraph()
    non_empty = random_tree(n=1, create_using=OrderedDiGraph)

    with pytest.raises(nx.NetworkXPointlessConcept):
        maximum_common_ordered_subtree_embedding(empty, empty)

    with pytest.raises(nx.NetworkXPointlessConcept):
        maximum_common_ordered_subtree_embedding(empty, non_empty)

    with pytest.raises(nx.NetworkXPointlessConcept):
        maximum_common_ordered_subtree_embedding(non_empty, empty)


def test_self_common_embedding():
    """
    The common embedding of a tree with itself should always be itself
    """
    rng = create_py_random_state(85652972257)
    for n in range(1, 10):
        tree = random_tree(n=n, seed=rng, create_using=OrderedDiGraph)
        embedding1, embedding2, _ = maximum_common_ordered_subtree_embedding(
            tree, tree
        )
        assert tree.edges == embedding1.edges


def test_common_tree_embedding_small():
    tree1 = OrderedDiGraph([(0, 1)])
    tree2 = OrderedDiGraph([(0, 1), (1, 2)])
    print(graph_str(tree1))
    print(graph_str(tree2))

    embedding1, embedding2, _ = maximum_common_ordered_subtree_embedding(
        tree1, tree2
    )
    print(graph_str(embedding1))
    print(graph_str(embedding2))


def test_common_tree_embedding_small2():
    tree1 = OrderedDiGraph([(0, 1), (2, 3), (4, 5), (5, 6)])
    tree2 = OrderedDiGraph([(0, 1), (1, 2), (0, 3)])
    print(graph_str(tree1))
    print(graph_str(tree2))

    embedding1, embedding2, _ = maximum_common_ordered_subtree_embedding(
        tree1, tree2, node_affinity=None
    )
    print(graph_str(embedding1))
    print(graph_str(embedding2))


def test_all_implementations_are_same():
    """
    Tests several random sequences
    """

    seed = 24658885408229410362279507020239
    rng = create_py_random_state(seed)

    maxsize = 20
    num_trials = 5

    node_affinity = "eq"

    for _ in range(num_trials):
        n1 = rng.randint(1, maxsize)
        n2 = rng.randint(1, maxsize)

        tree1 = random_tree(n1, seed=rng, create_using=OrderedDiGraph)
        tree2 = random_tree(n2, seed=rng, create_using=OrderedDiGraph)

        # Note: the returned sequences may be different (maximum embeddings may
        # not be unique), but the values should all be the same.
        results = {}
        impls = balanced_embedding.available_impls_longest_common_balanced_embedding()
        for impl in impls:
            # FIXME: do we need to rework the return value here?
            embedding1, embedding2, value = maximum_common_ordered_subtree_embedding(
                tree1, tree2, node_affinity=node_affinity, impl=impl
            )
            _check_common_embedding_invariants(tree1, tree2, embedding1, embedding2)
            results[impl] = value

        x = max(results.values())
        assert all(v == x for v in results.values())


def _check_embedding_invariants(tree, subtree):
    assert set(subtree.nodes).issubset(set(tree.nodes)), "must have a node subset"
    assert len(subtree.edges) <= len(tree.edges)


def _check_common_embedding_invariants(tree1, tree2, embedding1, embedding2):
    """
    Validates that this solution satisfies properties of an embedding
    """
    _check_embedding_invariants(tree1, embedding1)
    _check_embedding_invariants(tree2, embedding2)
    assert len(embedding1.nodes) == len(embedding2.nodes)

    _check_contractions(tree1, tree2, embedding1, embedding2)


def _check_contractions(tree1, tree2, embedding1, embedding2):
    """
    Only valid if ``node_affinity`` was "auto"
    """
    # We reverse topologically sort so we always contract from leaves to the
    # root
    remove_nodes1 = [
        n for n in nx.topological_sort(tree1) if n not in embedding1.nodes
    ][::-1]
    remove_nodes2 = [
        n for n in nx.topological_sort(tree2) if n not in embedding2.nodes
    ][::-1]

    contract_edges1 = [(u, v) for v in remove_nodes1 for u in tree1.pred[v]]
    contract_edges2 = [(u, v) for v in remove_nodes2 for u in tree2.pred[v]]

    embedding1_alt = tree1.copy()
    for u, v in contract_edges1:
        nx.contracted_nodes(embedding1_alt, u, v, copy=False, self_loops=False)
    # Handle the case where sources nodes are removed
    embedding1_alt.remove_nodes_from(remove_nodes1)

    embedding2_alt = tree2.copy()
    for u, v in contract_edges2:
        nx.contracted_nodes(embedding2_alt, u, v, copy=False, self_loops=False)
    # Handle the case where sources nodes are removed
    embedding2_alt.remove_nodes_from(remove_nodes2)

    assert set(embedding1.nodes) == set(embedding1_alt.nodes)
    assert set(embedding1.edges) == set(embedding1_alt.edges)

    assert set(embedding2.nodes) == set(embedding2_alt.nodes)
    assert set(embedding2.edges) == set(embedding2_alt.edges)

    if 0:
        graph_str(tree1, write=print)
        graph_str(tree2, write=print)
        graph_str(embedding1, write=print)
        graph_str(embedding2, write=print)
        graph_str(embedding1_alt, write=print)
        graph_str(embedding2_alt, write=print)


def test_forest_case():
    # Test forest case
    F = nx.disjoint_union_all(
        [
            random_tree(3, seed=0, create_using=OrderedDiGraph),
            random_tree(5, seed=1, create_using=OrderedDiGraph),
            random_tree(5, seed=1, create_using=OrderedDiGraph),
            random_tree(2, seed=2, create_using=OrderedDiGraph),
            random_tree(1, seed=3, create_using=OrderedDiGraph),
        ]
    )

    # Just verify everything runs without error for now. Would be best to find
    # something to check though.
    print(graph_str(F))
    sequence, *_ = tree_to_seq(F, item_type="number")
    print("sequence = {!r}".format(sequence))
    sequence, *_ = tree_to_seq(F, item_type="chr")
    print("sequence = {!r}".format(sequence))
    sequence, *_ = tree_to_seq(F, item_type="chr", container_type="str")
    print("sequence = {!r}".format(sequence))
    sequence, *_ = tree_to_seq(F, item_type="chr", container_type="tuple")
    print("sequence = {!r}".format(sequence))
