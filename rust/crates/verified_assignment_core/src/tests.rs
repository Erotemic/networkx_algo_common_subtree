use super::*;

fn independent_minimum(cost: &[Vec<i64>]) -> i128 {
    fn search(cost: &[Vec<i64>], columns: &mut [bool], row: usize, total: i128) -> i128 {
        if row == cost.len() {
            return total;
        }
        let mut best = i128::MAX;
        for col in 0..columns.len() {
            if !columns[col] {
                columns[col] = true;
                best = best.min(search(
                    cost,
                    columns,
                    row + 1,
                    total + cost[row][col] as i128,
                ));
                columns[col] = false;
            }
        }
        best
    }
    search(cost, &mut vec![false; cost.len()], 0, 0)
}

fn check(cost: &[Vec<i64>]) -> Assignment {
    let result = min_cost_assignment(cost).unwrap();
    let n = cost.len();
    assert_eq!(result.cost, independent_minimum(cost));
    assert_eq!(result.column_for_row.len(), n);
    assert_eq!(result.row_potential.len(), n);
    assert_eq!(result.column_potential.len(), n);
    let mut chosen = result.column_for_row.clone();
    chosen.sort_unstable();
    assert_eq!(chosen, (0..n).collect::<Vec<_>>());
    for (row, costs) in cost.iter().enumerate() {
        for (col, weight) in costs.iter().enumerate() {
            assert!(result.row_potential[row] + result.column_potential[col] <= *weight as i128);
        }
        let col = result.column_for_row[row];
        assert_eq!(
            result.row_potential[row] + result.column_potential[col],
            costs[col] as i128
        );
    }
    assert_eq!(
        result.cost,
        result.row_potential.iter().sum::<i128>() + result.column_potential.iter().sum::<i128>()
    );
    result
}

#[test]
fn empty_singleton_and_shape_errors() {
    check(&[]);
    assert_eq!(check(&[vec![-9]]).cost, -9);
    assert_eq!(
        min_cost_assignment(&[vec![1, 2]]),
        Err(AssignmentError::NonSquare)
    );
    assert_eq!(
        min_cost_assignment(&[vec![], vec![]]),
        Err(AssignmentError::NonSquare)
    );
}

#[test]
fn negative_extreme_costs_and_ties() {
    check(&[vec![i64::MIN, i64::MAX], vec![i64::MAX, i64::MIN]]);
    check(&[vec![i64::MAX, i64::MIN], vec![i64::MIN, i64::MAX]]);
    check(&vec![vec![i64::MAX; 5]; 5]);
    check(&vec![vec![i64::MIN; 5]; 5]);
    let tied = vec![vec![0; 5]; 5];
    assert_eq!(check(&tied), check(&tied));
}

#[test]
fn signed_matrices_agree_with_independent_permutation_enumeration() {
    let mut seed = 0x719e_a04c_d3b2_f865u64;
    for n in 0..=7 {
        for _ in 0..40 {
            let mut cost = vec![vec![0; n]; n];
            for row in &mut cost {
                for value in row {
                    seed = seed
                        .wrapping_mul(6364136223846793005)
                        .wrapping_add(1442695040888963407);
                    *value = ((seed >> 32) % 101) as i64 - 50;
                }
            }
            check(&cost);
        }
    }
}
