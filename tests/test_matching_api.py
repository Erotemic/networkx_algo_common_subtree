"""Installed exact matching API versus independent permutation/injection search."""
import itertools
import os
import random

import pytest
import networkx_algo_common_subtree as common


@pytest.fixture(autouse=True)
def native_matching():
    try:
        from networkx_algo_common_subtree import _rust
        assert all(hasattr(_rust, name) for name in (
            "min_cost_assignment", "max_weight_partial_matching",
            "max_weight_partial_matching_deletions",
        ))
    except (ImportError, AssertionError):
        if os.environ.get("COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS") == "1":
            pytest.fail("required exact matching Rust bindings are missing")
        pytest.skip("optional exact matching Rust bindings are missing")


def test_assignment_optimum_and_dual_certificate():
    rng = random.Random(16384)
    for n in range(6):
        for _ in range(8):
            costs = [[rng.randrange(-20, 21) for _ in range(n)] for _ in range(n)]
            result = common.min_cost_assignment(costs)
            optimum = min(sum(costs[i][p[i]] for i in range(n)) for p in itertools.permutations(range(n)))
            assert result.cost == optimum
            assert sorted(result.column_for_row) == list(range(n))
            assert sum(costs[i][j] for i, j in enumerate(result.column_for_row)) == optimum
            assert sum(result.row_potential) + sum(result.column_potential) == optimum
            assert all(result.row_potential[i] + result.column_potential[j] <= costs[i][j]
                       for i in range(n) for j in range(n))
            assert result == common.min_cost_assignment(costs)


def exhaustive_weight(weights, removed=None):
    """Enumerate partial injections, independently of the assignment solver."""
    n = len(weights)
    m = len(weights[0]) if n else 0
    columns = [j for j in range(m) if j != removed]
    optimum = 0
    for k in range(min(n, len(columns)) + 1):
        for rows in itertools.combinations(range(n), k):
            for selected in itertools.permutations(columns, k):
                values = [weights[i][j] for i, j in zip(rows, selected)]
                if all(value is not None for value in values):
                    optimum = max(optimum, sum(values))
    return optimum


def assert_matching(weights, result, removed=None):
    n = len(weights)
    m = len(weights[0]) if n else 0
    assert len({i for i, _ in result.pairs}) == len(result.pairs)
    assert len({j for _, j in result.pairs}) == len(result.pairs)
    assert all(0 <= i < n and 0 <= j < m and j != removed
               and weights[i][j] is not None for i, j in result.pairs)
    assert sum(weights[i][j] for i, j in result.pairs) == result.weight
    assert result.weight == exhaustive_weight(weights, removed)


def test_partial_matching_independent_injection_oracle():
    rng = random.Random(2016)
    for n in range(5):
        for m in range(5):
            for _ in range(4):
                weights = [[rng.choice([None, -7, 0, 1, 9]) for _ in range(m)] for _ in range(n)]
                result = common.max_weight_partial_matching(weights)
                assert_matching(weights, result)
                assert result == common.max_weight_partial_matching(weights)


def test_matching_deletion_family_exhaustive_original_indices():
    for n, m in [(0, 0), (1, 0), (2, 0), (1, 1), (1, 2), (2, 1), (2, 2)]:
        for entries in itertools.product([None, -1, 0, 1], repeat=n * m):
            weights = [list(entries[i*m:(i+1)*m]) for i in range(n)]
            family = common.max_weight_partial_matching_deletions(weights)
            assert_matching(weights, family.original)
            assert len(family.without_right) == m
            used = {j for _, j in family.original.pairs}
            for removed, result in enumerate(family.without_right):
                assert_matching(weights, result, removed)
                if removed not in used:
                    assert result == family.original


def test_matching_deletion_family_rectangular_ties_and_signed_weights():
    rng = random.Random(160218)
    cases = [[[1] * 5 for _ in range(3)], [[1] * 3 for _ in range(5)],
             [[0] * 3 for _ in range(2)], [[None] * 4 for _ in range(3)]]
    for n, m in [(3, 4), (4, 2), (1, 5), (5, 1)]:
        for _ in range(6):
            cases.append([[rng.choice([None, -9, 0, 2, 7]) for _ in range(m)] for _ in range(n)])
    for weights in cases:
        family = common.max_weight_partial_matching_deletions(weights)
        assert family == common.max_weight_partial_matching_deletions(weights)
        assert_matching(weights, family.original)
        for removed, result in enumerate(family.without_right):
            assert_matching(weights, result, removed)


def test_matching_deletion_family_exact_boundaries_and_empty_sides():
    maximum, minimum = 2**63 - 1, -2**63
    weights = [[maximum, None, minimum], [None, maximum, 0]]
    family = common.max_weight_partial_matching_deletions(weights)
    assert family.original.weight == 2 * maximum
    assert [result.weight for result in family.without_right] == [maximum, maximum, 2 * maximum]
    assert family.without_right[0].pairs == ((1, 1),)
    assert family.without_right[2] == family.original
    for weights in [[], [[]], [[], []]]:
        family = common.max_weight_partial_matching_deletions(weights)
        assert family.original == common.PartialMatchingResult((), 0)
        assert family.without_right == ()
    with pytest.raises(ValueError):
        common.max_weight_partial_matching_deletions([[1], []])


def test_exact_integer_boundaries_and_errors():
    maximum, minimum = 2**63 - 1, -2**63
    assert common.min_cost_assignment([[minimum, maximum], [maximum, minimum]]).cost == 2 * minimum
    assert common.max_weight_partial_matching([[maximum, None], [None, maximum]]).weight == 2 * maximum
    for matrix in [[[1, 2]], [[1], []]]:
        with pytest.raises(ValueError):
            common.min_cost_assignment(matrix)
    with pytest.raises(ValueError):
        common.max_weight_partial_matching([[1], []])
    for solve in [common.min_cost_assignment, common.max_weight_partial_matching,
                  common.max_weight_partial_matching_deletions]:
        with pytest.raises(OverflowError):
            solve([[2**63]])
        with pytest.raises(OverflowError):
            solve([[-2**63 - 1]])
        with pytest.raises(TypeError):
            solve([[0.5]])


def test_nonpositive_matching_families_and_late_positive_entry():
    for weights in [[[] for _ in range(4096)], [[None] * 8 for _ in range(4)],
                    [[-2**63, 0, None] for _ in range(8)]]:
        assert common.max_weight_partial_matching(weights) == common.PartialMatchingResult((), 0)
        family = common.max_weight_partial_matching_deletions(weights)
        assert family.original == common.PartialMatchingResult((), 0)
        assert all(result == family.original for result in family.without_right)
        assert len(family.without_right) == len(weights[0])
    weights = [[-7] * 5 for _ in range(4)]
    weights[-1][-1] = 11
    family = common.max_weight_partial_matching_deletions(weights)
    assert_matching(weights, family.original)
    assert family.original.pairs == ((3, 4),)
    for removed, result in enumerate(family.without_right):
        assert_matching(weights, result, removed)
