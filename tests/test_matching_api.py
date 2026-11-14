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
        assert hasattr(_rust, "min_cost_assignment")
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


def test_partial_matching_independent_injection_oracle():
    rng = random.Random(2016)
    for n in range(5):
        for m in range(5):
            for _ in range(4):
                weights = [[rng.choice([None, -7, 0, 1, 9]) for _ in range(m)] for _ in range(n)]
                # Enumerate every partial injection, independently of assignment DP.
                optimum = 0
                for k in range(min(n, m) + 1):
                    for rows in itertools.combinations(range(n), k):
                        for cols in itertools.permutations(range(m), k):
                            values = [weights[i][j] for i, j in zip(rows, cols)]
                            if all(v is not None for v in values):
                                optimum = max(optimum, sum(values))
                result = common.max_weight_partial_matching(weights)
                assert result.weight == optimum
                assert len({i for i, _ in result.pairs}) == len(result.pairs)
                assert len({j for _, j in result.pairs}) == len(result.pairs)
                assert sum(weights[i][j] for i, j in result.pairs) == optimum
                assert result == common.max_weight_partial_matching(weights)


def test_exact_integer_boundaries_and_errors():
    maximum, minimum = 2**63 - 1, -2**63
    assert common.min_cost_assignment([[minimum, maximum], [maximum, minimum]]).cost == 2 * minimum
    assert common.max_weight_partial_matching([[maximum, None], [None, maximum]]).weight == 2 * maximum
    for matrix in [[[1, 2]], [[1], []]]:
        with pytest.raises(ValueError):
            common.min_cost_assignment(matrix)
    with pytest.raises(ValueError):
        common.max_weight_partial_matching([[1], []])
    for solve in [common.min_cost_assignment, common.max_weight_partial_matching]:
        with pytest.raises(OverflowError):
            solve([[2**63]])
        with pytest.raises(OverflowError):
            solve([[-2**63 - 1]])
        with pytest.raises(TypeError):
            solve([[0.5]])
