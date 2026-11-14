use verified_assignment_core::{sparse::minimum_sparse_cut, AssignmentError};

#[test]
fn sparse_cut_matches_independent_allowed_edge_minimum() {
    for n in 0..=4 {
        for seed in 0..8 {
            let cost: Vec<Vec<Option<i64>>> = (0..n)
                .map(|r| {
                    (0..n)
                        .map(|c| {
                            if (r + 2 * c + seed) % 4 == 0 {
                                None
                            } else {
                                Some(((r * 5 + c * 11 + seed) % 7) as i64 - 3)
                            }
                        })
                        .collect()
                })
                .collect();
            let rows: Vec<i128> = (0..n).map(|r| (r % 5) as i128 - 2).collect();
            let columns: Vec<i128> = (0..n).map(|c| (c % 7) as i128 - 3).collect();
            for row_mask in 0..(1 << n) {
                for column_mask in 0..(1 << n) {
                    let selected_rows: Vec<bool> =
                        (0..n).map(|r| row_mask & (1 << r) != 0).collect();
                    let selected_columns: Vec<bool> =
                        (0..n).map(|c| column_mask & (1 << c) != 0).collect();
                    let mut candidates = Vec::new();
                    for r in 0..n {
                        for c in 0..n {
                            if selected_rows[r] && !selected_columns[c] {
                                if let Some(value) = cost[r][c] {
                                    candidates.push((value as i128 - rows[r] - columns[c], r, c));
                                }
                            }
                        }
                    }
                    let expected = candidates.into_iter().min();
                    let actual = match minimum_sparse_cut(
                        &cost,
                        &rows,
                        &columns,
                        &selected_rows,
                        &selected_columns,
                    ) {
                        Ok(cut) => cut,
                        Err(_) => panic!("small cut arithmetic fits"),
                    };
                    assert_eq!(actual.map(|cut| (cut.delta, cut.row, cut.column)), expected);
                }
            }
        }
    }
}

#[test]
fn sparse_cut_reports_shape_and_arithmetic_errors() {
    assert!(matches!(
        minimum_sparse_cut(&[vec![Some(0), None]], &[0], &[0], &[true], &[false]),
        Err(AssignmentError::NonSquare)
    ));
    assert!(matches!(
        minimum_sparse_cut(&[vec![Some(0)]], &[], &[0], &[true], &[false]),
        Err(AssignmentError::NonSquare)
    ));
    assert!(matches!(
        minimum_sparse_cut(
            &[vec![Some(i64::MAX)]],
            &[i128::MIN],
            &[0],
            &[true],
            &[false]
        ),
        Err(AssignmentError::ArithmeticOverflow)
    ));
    assert!(matches!(
        minimum_sparse_cut(
            &[vec![Some(0)]],
            &[i128::MAX],
            &[i128::MAX],
            &[true],
            &[false]
        ),
        Err(AssignmentError::ArithmeticOverflow)
    ));
    assert!(matches!(
        minimum_sparse_cut(&[vec![None]], &[i128::MAX], &[i128::MAX], &[true], &[false]),
        Ok(None)
    ));
}
