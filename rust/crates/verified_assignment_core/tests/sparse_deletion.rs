use verified_assignment_core::{sparse_deletion::repair_deleted_sparse_vertex, AssignmentError};

fn minimum_cost(cost: &[Vec<Option<i64>>]) -> i128 {
    fn enumerate(cost: &[Vec<Option<i64>>], row: usize, mask: usize, total: i128, best: &mut Option<i128>) {
        if row == cost.len() {
            *best = Some(best.map_or(total, |old| old.min(total)));
        } else {
            for column in 0..cost.len() {
                if mask & (1 << column) == 0 {
                    if let Some(value) = cost[row][column] {
                        enumerate(cost, row+1, mask | (1 << column), total+value as i128, best);
                    }
                }
            }
        }
    }
    let mut best = None;
    enumerate(cost,0,0,0,&mut best);
    best.expect("identity edges provide a compatible perfect assignment")
}

#[test]
fn sparse_deletion_matches_every_induced_optimum_in_original_coordinates() {
    let mut cases = 0;
    for n in 1..=6 {
        for active in 0..=n {
            if active == 1 { continue; }
            for seed in 0..6 {
                let shift = if active == 0 { 0 } else { seed % (active-1)+1 };
                let completed: Vec<usize> = (0..n).map(|r| if r < active { (r+shift)%active } else { r }).collect();
                let rows: Vec<i128> = (0..n).map(|r| if r < active { -(((r+seed)%5+1) as i128) } else { 0 }).collect();
                let columns: Vec<i128> = (0..n).map(|c| if c < active { -(((c+2*seed)%7+1) as i128) } else { 0 }).collect();
                let cost: Vec<Vec<Option<i64>>> = (0..n).map(|r| (0..n).map(|c| {
                    if r == c { Some(0) }
                    else if c == completed[r] { Some((rows[r]+columns[c]) as i64) }
                    else if (r+2*c+seed)%3 == 0 { None }
                    else { Some((rows[r]+columns[c]+((r*3+c+seed)%5) as i128).min(0) as i64) }
                }).collect()).collect();
                let old_primal: i128 = (0..n).map(|r| cost[r][completed[r]].unwrap() as i128).sum();
                let old_dual: i128 = rows.iter().chain(columns.iter()).sum();
                assert_eq!(old_primal, old_dual);
                assert_eq!(old_primal, minimum_cost(&cost));
                for r in 0..n {
                    assert_eq!(rows[r]+columns[completed[r]],cost[r][completed[r]].unwrap() as i128);
                    for c in 0..n {
                        if let Some(value) = cost[r][c] { assert!(rows[r]+columns[c] <= value as i128); }
                    }
                }
                for removed in 0..n {
                    cases += 1;
                    let result = match repair_deleted_sparse_vertex(&cost, &rows, &columns, &completed, removed) {
                        Ok(result) => result,
                        Err(_) => panic!("feasible tight old optimum and identity graph must repair"),
                    };
                    let expected_vertices: Vec<usize> = (0..n).filter(|&v| v != removed).collect();
                    assert_eq!(result.vertices, expected_vertices);
                    assert_eq!(result.repaired, completed[removed] != removed);
                    assert_eq!(result.rows.len(), n-1);
                    assert_eq!(result.columns.len(), n-1);
                    let mut sorted = result.column_for_row.clone();
                    sorted.sort_unstable();
                    assert_eq!(sorted, expected_vertices);
                    let projected: Vec<Vec<Option<i64>>> = result.vertices.iter().map(|&r|
                        result.vertices.iter().map(|&c| cost[r][c]).collect()).collect();
                    let mut actual_cost = 0;
                    for (i,&r) in result.vertices.iter().enumerate() {
                        let c = result.column_for_row[i];
                        let j = result.vertices.iter().position(|&v| v == c).unwrap();
                        let value = cost[r][c].expect("repaired original edge must be allowed") as i128;
                        actual_cost += value;
                        assert_eq!(result.rows[i]+result.columns[j],value);
                        for (j,&c) in result.vertices.iter().enumerate() {
                            if let Some(value) = cost[r][c] { assert!(result.rows[i]+result.columns[j] <= value as i128); }
                        }
                        if !result.repaired {
                            assert_eq!(c,completed[r]);
                            assert_eq!(result.rows[i],rows[r]);
                            assert_eq!(result.columns[i],columns[r]);
                        }
                    }
                    assert_eq!(actual_cost, minimum_cost(&projected));
                    assert_eq!(actual_cost, result.rows.iter().chain(result.columns.iter()).sum::<i128>());
                }
            }
        }
    }
    assert_eq!(cases,546);
}

#[test]
fn sparse_deletion_reports_bad_shapes_removed_vertices_and_permutations() {
    assert!(matches!(repair_deleted_sparse_vertex(&[vec![Some(0), None]], &[0], &[0], &[0], 0), Err(AssignmentError::NonSquare)));
    assert!(matches!(repair_deleted_sparse_vertex(&[vec![Some(0)]], &[], &[0], &[0], 0), Err(AssignmentError::NonSquare)));
    assert!(matches!(repair_deleted_sparse_vertex(&[], &[], &[], &[], 0), Err(AssignmentError::InvariantViolation)));
    assert!(matches!(repair_deleted_sparse_vertex(&[vec![Some(0)]], &[0], &[0], &[0], 1), Err(AssignmentError::InvariantViolation)));
    assert!(matches!(repair_deleted_sparse_vertex(&vec![vec![Some(0);2];2], &[0,0], &[0,0], &[0,0], 0), Err(AssignmentError::InvariantViolation)));
}
