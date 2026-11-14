"""Run with: python3 -m unittest discover -s presentations/tests -v"""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from math_examples import (  # noqa: E402
    EXAMPLE_BRANCHING, EXAMPLE_MATCHING, EXAMPLE_REDUCED,
    all_contractions, all_dyck_words, common_embedding_oracle,
    contract_once, decode_tree, encode_tree, lozano_dp_word,
    max_weight_partial_matching, path_contribution,
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

    def test_matching_example(self):
        score, pairs = max_weight_partial_matching(EXAMPLE_MATCHING)
        self.assertEqual(score, 15)
        self.assertEqual(set(pairs), {(0, 0), (1, 1)})
        self.assertEqual(max_weight_partial_matching(((-4, -1),))[0], 0)

    def test_skipped_path_example(self):
        self.assertEqual(path_contribution(1, 1, 1, .25), 1)
        self.assertEqual(path_contribution(1, 1, 2, .25), -.25)
        self.assertEqual(1 + 1 + path_contribution(1, 1, 2, .25), 1.75)


if __name__ == "__main__":
    unittest.main()
