use verified_assignment_core::{sparse_search::find_sparse_augmenting_path, AssignmentError};

fn minimum_permutation_cost(cost: &[Vec<Option<i64>>]) -> i128 {
    fn visit(cost: &[Vec<Option<i64>>], used: &mut [bool], row: usize, total: i128, best: &mut Option<i128>) {
        if row == cost.len() {
            *best = Some(best.map_or(total, |old| old.min(total)));
        } else {
            for column in 0..cost.len() {
                if !used[column] {
                    if let Some(value) = cost[row][column] {
                        used[column] = true;
                        visit(cost, used, row+1, total+value as i128, best);
                        used[column] = false;
                    }
                }
            }
        }
    }
    let mut best = None;
    visit(cost, &mut vec![false;cost.len()], 0, 0, &mut best);
    best.expect("constructed cyclic assignment must be compatible")
}

#[test]
fn sparse_search_paths_are_ranked_tight_and_globally_optimal() {
    for n in 1..=5 {
        for seed in 0..8 {
            let completed: Vec<usize> = (0..n).map(|row| (row+seed)%n).collect();
            for root in 0..n {
                let rows: Vec<i128> = (0..n).map(|row| -(row as i128)-4).collect();
                let columns: Vec<i128> = (0..n).map(|column| -(column as i128)-5).collect();
                let cost: Vec<Vec<Option<i64>>> = (0..n).map(|row| (0..n).map(|column| {
                    let old_edge = column == completed[row];
                    let cyclic_edge = column == completed[(row+1)%n];
                    let present = (row != root && old_edge) || cyclic_edge ||
                        ((row+column+seed)%3 != 0 && !(row == root && old_edge && seed%2 == 1));
                    if present {
                        let slack = if row != root && old_edge { 0 } else { ((row*3+column+seed)%4+1) as i128 };
                        Some((rows[row]+columns[column]+slack) as i64)
                    } else { None }
                }).collect()).collect();
                let search = match find_sparse_augmenting_path(&cost, rows, columns, &completed, root) {
                    Ok(search) => search,
                    Err(_) => panic!("constructed feasible single-deficit state must succeed"),
                };
                assert_eq!(search.target, completed[root]);
                assert!((1..=n).contains(&search.steps));
                let mut repaired = completed.clone();
                let mut column = search.target;
                let mut previous_rank = n+1;
                let mut path_length = 0;
                loop {
                    path_length += 1;
                    assert!(path_length <= n);
                    assert!(search.discovery[column] > 0 && search.discovery[column] < previous_rank);
                    previous_rank = search.discovery[column];
                    let row = search.predecessor_row[column];
                    assert!(row < n);
                    repaired[row] = column;
                    if row == root { break; }
                    column = completed[row];
                }
                let mut sorted = repaired.clone();
                sorted.sort_unstable();
                assert_eq!(sorted, (0..n).collect::<Vec<_>>());
                let mut actual_cost = 0;
                for row in 0..n {
                    let column = repaired[row];
                    let value = cost[row][column].expect("returned path edges must be allowed") as i128;
                    assert_eq!(search.rows[row]+search.columns[column], value);
                    actual_cost += value;
                    for column in 0..n {
                        if let Some(value) = cost[row][column] {
                            assert!(search.rows[row]+search.columns[column] <= value as i128);
                        }
                    }
                }
                assert_eq!(actual_cost, search.rows.iter().chain(search.columns.iter()).sum::<i128>());
                assert_eq!(actual_cost, minimum_permutation_cost(&cost));
            }
        }
    }
}

#[test]
fn sparse_search_reports_invalid_shape_permutations_root_and_no_cut() {
    assert!(matches!(find_sparse_augmenting_path(&[vec![Some(0)]], vec![], vec![0], &[0], 0), Err(AssignmentError::NonSquare)));
    assert!(matches!(find_sparse_augmenting_path(&[vec![Some(0),None]], vec![0], vec![0], &[0], 0), Err(AssignmentError::NonSquare)));
    assert!(matches!(find_sparse_augmenting_path(&[vec![Some(0)]], vec![0], vec![0], &[1], 0), Err(AssignmentError::InvariantViolation)));
    assert!(matches!(find_sparse_augmenting_path(&[vec![Some(0)]], vec![0], vec![0], &[0], 1), Err(AssignmentError::InvariantViolation)));
    assert!(matches!(find_sparse_augmenting_path(&vec![vec![Some(0);2];2], vec![0;2], vec![0;2], &[0,0], 0), Err(AssignmentError::InvariantViolation)));
    assert!(matches!(find_sparse_augmenting_path(&[vec![None]], vec![0], vec![0], &[0], 0), Err(AssignmentError::InvariantViolation)));
}
