"""Run with: python3 -m unittest discover -s presentations/tests -v"""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from math_examples import (  # noqa: E402
    EXAMPLE_BRANCHING, EXAMPLE_MATCHING, EXAMPLE_REDUCED, EXAMPLE_SPLICED,
    all_contractions, all_dyck_words, common_embedding_oracle,
    contract_once, decode_tree, encode_tree, lozano_dp_word,
    max_weight_partial_matching, path_contribution, lozano_recurrence_candidate_scores,
    first_child_next_sibling, memoized_recurrence_trace, flip_augmenting_path,
    skipped_path_conflicts, node,
)


class AnimatedExampleTests(unittest.TestCase):
    def test_balanced_sequence_pair(self):
        self.assertEqual(encode_tree(EXAMPLE_BRANCHING), "001011")
        self.assertEqual(encode_tree(EXAMPLE_REDUCED), "0011")
        self.assertIn(EXAMPLE_REDUCED, contract_once(EXAMPLE_BRANCHING))
        self.assertIn(encode_tree(EXAMPLE_REDUCED), {encode_tree(t) for t in all_contractions(EXAMPLE_BRANCHING)})

    def test_roundtrip_and_recurrence_against_independent_oracle(self):
        # Every pair of Dyck words up to four edges: 23^2 = 529 cases.
        words = [word for n in range(5) for word in all_dyck_words(n)]
        for a in words:
            self.assertEqual(encode_tree(decode_tree(a)), a)
        for a in words:
            for b in words:
                optimum, _ = common_embedding_oracle(decode_tree(a), decode_tree(b))
                self.assertEqual(len(lozano_dp_word(a, b)) // 2, optimum, (a, b))

    def test_internal_vertex_splicing_and_candidate_values(self):
        self.assertEqual(encode_tree(EXAMPLE_SPLICED), "0101")
        self.assertIn(EXAMPLE_SPLICED, contract_once(EXAMPLE_BRANCHING))
        self.assertEqual(lozano_recurrence_candidate_scores("001011", "0011"), (2, 1, 1))

    def test_matching_example(self):
        score, pairs = max_weight_partial_matching(EXAMPLE_MATCHING)
        self.assertEqual(score, 15)
        self.assertEqual(set(pairs), {(0, 0), (1, 1)})
        self.assertEqual(max_weight_partial_matching(((-4, -1),))[0], 0)

    def test_skipped_path_example(self):
        self.assertEqual(path_contribution(1, 1, 1, .25), 1)
        self.assertEqual(path_contribution(1, 1, 2, .25), -.25)
        self.assertEqual(1 + 1 + path_contribution(1, 1, 2, .25), 1.75)

    def test_first_child_next_sibling_traversal(self):
        tree = node("r", node("a", node("b"), node("c")), node("d"))
        links = first_child_next_sibling(tree)
        self.assertEqual(links[()], ((0,), None))
        self.assertEqual(links[(0,)], ((0, 0), (1,)))
        self.assertEqual(links[(0, 0)], (None, (0, 1)))
        self.assertEqual(links[(0, 1)], (None, None))
        visited = []

        def traverse(path):
            visited.append(path)
            child, sibling = links[path]
            if child is not None:
                traverse(child)
            if sibling is not None:
                traverse(sibling)

        traverse(())
        self.assertEqual(visited, [(), (0,), (0, 0), (0, 1), (1,)])
        self.assertEqual(len(visited), len(links))

    def test_shape_parameters_use_paper_vertex_depth(self):
        chain = node('r', node('a', node('b', node('c'))))
        star = node('r', node('a'), node('b'), node('c'))
        self.assertEqual((chain.edge_count, chain.vertex_depth, chain.leaf_count), (3, 4, 1))
        self.assertEqual((star.edge_count, star.vertex_depth, star.leaf_count), (3, 2, 3))
        self.assertEqual((node('r').vertex_depth, node('r').leaf_count), (1, 1))

    def test_memo_trace_against_independent_contractions(self):
        words = [w for n in range(4) for w in all_dyck_words(n)]
        for a in words:
            for b in words:
                score, events = memoized_recurrence_trace(a, b)
                self.assertEqual(score, common_embedding_oracle(decode_tree(a), decode_tree(b))[0])
                expanded = {}
                for kind, key, value in events:
                    if kind == "expand":
                        self.assertNotIn(key, expanded)
                        expanded[key] = value
                    else:
                        self.assertEqual(expanded[key], value)
        _, events = memoized_recurrence_trace("001011", "0011")
        self.assertIn(("hit", ("01", "01"), 1), events)

    def test_augmenting_path_and_related_deletions(self):
        weights = ((8, 7), (7, None))
        path = (("L", 1), ("R", 0), ("L", 0), ("R", 1))
        pairs = flip_augmenting_path(((0, 0),), path)
        self.assertEqual(pairs, ((0, 1), (1, 0)))
        score = sum(weights[r][c] for r, c in pairs)
        self.assertEqual(score, max_weight_partial_matching(weights)[0])
        self.assertEqual(score, 14)
        for removed, expected in ((0, 7), (1, 8)):
            reduced = tuple(tuple(w for j, w in enumerate(row) if j != removed) for row in weights)
            self.assertEqual(max_weight_partial_matching(reduced)[0], expected)
        for invalid in (
            (("L", 0), ("R", 1)),  # starting row is already occupied
            (("L", 1), ("R", 1), ("L", 0), ("R", 0)),  # middle edge not matched
            (("L", 1), ("R", 0), ("L", 1), ("R", 1)),  # repeated vertex
        ):
            with self.assertRaises(ValueError):
                flip_augmenting_path(((0, 0),), invalid)

    def test_skipped_branch_collision(self):
        self.assertEqual(skipped_path_conflicts((("r", "x", "a"), ("r", "x", "b")),
                                               {"r", "a", "b"}), {"x"})
        self.assertEqual(skipped_path_conflicts((("x", "a"), ("x", "b")),
                                               {"x", "a", "b"}), set())
        self.assertEqual(skipped_path_conflicts((("r", "x", "a"),),
                                               {"r", "x", "a"}), {"x"})


if __name__ == "__main__":
    unittest.main()
