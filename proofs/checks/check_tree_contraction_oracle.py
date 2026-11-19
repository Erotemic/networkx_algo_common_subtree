"""Independent rooted ordered-tree contraction oracle.

No Dyck-word or Lean code is used to enumerate or contract trees. A tree is
represented by a tuple of its ordered child trees. Each step selects a parent-
child edge and splices the child's children in its place; steps below the root
are enumerated recursively. The two encodings are compared only at the end.

Run: python3 proofs/checks/check_tree_contraction_oracle.py
"""

from functools import lru_cache
from check_printed_containment import operational_contained, dyck_words


@lru_cache(maxsize=None)
def trees_with_edges(edges):
    """All rooted ordered trees with exactly `edges` edges, via child forests."""
    return frozenset(forests_with_edges(edges))


@lru_cache(maxsize=None)
def forests_with_edges(edges):
    if edges == 0:
        return frozenset({()})
    return frozenset(
        (child,) + rest
        for child_edges in range(edges)
        for child in trees_with_edges(child_edges)
        for rest in forests_with_edges(edges - child_edges - 1)
    )


def encode_tree(tree):
    return "".join("0" + encode_tree(child) + "1" for child in tree)


def tree_one_steps(tree):
    results = set()
    for i, child in enumerate(tree):
        # Contract the edge from this tree's root to `child`.
        results.add(tree[:i] + child + tree[i + 1 :])
        # Or contract an edge strictly below this root.
        for replacement in tree_one_steps(child):
            results.add(tree[:i] + (replacement,) + tree[i + 1 :])
    return frozenset(results)


@lru_cache(maxsize=None)
def tree_contracted_closure(tree):
    results = {tree}
    for after in tree_one_steps(tree):
        assert edge_count(after) + 1 == edge_count(tree)
        results.update(tree_contracted_closure(after))
    return frozenset(results)


def edge_count(tree):
    return sum(1 + edge_count(child) for child in tree)


def main():
    total = 0
    for edges in range(7):
        trees = trees_with_edges(edges)
        encodings = {encode_tree(tree) for tree in trees}
        assert encodings == set(dyck_words(edges))
        for tree in trees:
            expected = {encode_tree(result) for result in tree_contracted_closure(tree)}
            actual = operational_contained(encode_tree(tree))
            assert expected == actual, (tree, expected ^ actual)
        total += len(trees)
        print(f"edges={edges}: {len(trees)} independent ordered trees agree")
    print(f"Checked {total} trees and all their reachable contraction results")

    # The concrete counterexample is also present in the independent tree model.
    tree = (((), ()),)     # one child with two leaf children
    after = (((),),)       # one child with one leaf child
    assert encode_tree(tree) == "001011"
    assert encode_tree(after) == "0011"
    assert after in tree_one_steps(tree)
    print("Confirmed tree contraction 001011 -> 0011")


if __name__ == "__main__":
    main()
