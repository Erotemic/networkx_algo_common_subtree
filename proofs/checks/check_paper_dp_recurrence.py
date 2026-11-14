"""Independent finite comparison for Lozano--Valiente (2004), Lemma 8.

Run from the repository root:
    python3 proofs/checks/check_paper_dp_recurrence.py

The recurrence is coded from Lemma 8. The two objective functions come from
independent enumerators of the printed Definition 2 and operational matched-
pair deletion. This is executable evidence, not a Lean correctness proof.
"""

from functools import lru_cache
from check_printed_containment import (
    dyck_words, operational_contained, printed_contained, matching_pairs,
)


@lru_cache(maxsize=None)
def first_return_split(word):
    if not word:
        raise ValueError('head/tail only defined for nonempty Dyck words')
    matching = next(end for begin, end in matching_pairs(word) if begin == 0)
    return word[1:matching], word[matching + 1:]


@lru_cache(maxsize=None)
def paper_lcs_dp(left, right):
    """Paper Lemma 8 recurrence, with head/tail decompositions."""
    if not left or not right:
        return 0
    left_head, left_tail = first_return_split(left)
    right_head, right_tail = first_return_split(right)
    return max(
        1 + paper_lcs_dp(left_head, right_head)
        + paper_lcs_dp(left_tail, right_tail),
        paper_lcs_dp(left_head + left_tail, right),
        paper_lcs_dp(left, right_head + right_tail),
    )


@lru_cache(maxsize=None)
def oracle_lcs(left, right, *, printed=False):
    candidates = printed_contained if printed else operational_contained
    return max(len(w) // 2 for w in candidates(left) & candidates(right))


def main():
    # The smallest example of a score discrepancy.
    short, long = '0011', '001011'
    assert oracle_lcs(short, long, printed=False) == 2
    assert oracle_lcs(short, long, printed=True) == 1
    assert paper_lcs_dp(short, long) == 2
    print('3-edge regression: recurrence=2; operational optimum=2; printed optimum=1')

    words = [w for n in range(7) for w in dyck_words(n)]
    mismatches_operational = []
    mismatches_printed = []
    for i, left in enumerate(words):
        for right in words[i:]:
            result = paper_lcs_dp(left, right)
            assert result == paper_lcs_dp(right, left), (left, right)
            oracle = oracle_lcs(left, right)
            literal = oracle_lcs(left, right, printed=True)
            if result != oracle:
                mismatches_operational.append((left, right, result, oracle))
            if result != literal:
                mismatches_printed.append((left, right, result, literal))
    total = len(words) * (len(words) + 1) // 2
    print(f'Compared {total} unordered word-pairs over {len(words)} Dyck words (0-6 edges)')
    print(f'Recurrence vs operational mismatches: {len(mismatches_operational)}')
    print(f'Recurrence vs literal printed mismatches: {len(mismatches_printed)}')
    assert not mismatches_operational, mismatches_operational[:5]
    assert mismatches_printed
    print('First mismatches with the literal definition:', mismatches_printed[:4])


if __name__ == '__main__':
    main()
