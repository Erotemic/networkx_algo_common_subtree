use verified_assignment_core::{sparse::{adjust_sparse_cut, advance_sparse_cut, minimum_sparse_cut}, AssignmentError};

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

#[test]
fn sparse_adjustment_preserves_feasibility_and_creates_tight_edge() {
    // Identity edges provide a perfect assignment, including in each sparse case.
    for n in 1..=4 {
        for seed in 0..8 {
            let cost: Vec<Vec<Option<i64>>> = (0..n).map(|r| (0..n).map(|c| {
                if r == c || (r + c + seed) % 3 != 0 {
                    Some(((r * 7 + c * 3 + seed) % 9) as i64)
                } else { None }
            }).collect()).collect();
            let rows: Vec<i128> = (0..n).map(|r| -(r as i128) - 1).collect();
            let columns: Vec<i128> = (0..n).map(|c| -(c as i128) - 2).collect();
            for row_mask in 0usize..(1 << n) {
                for column_mask in 0usize..(1 << n) {
                    if row_mask.count_ones() != column_mask.count_ones() + 1 { continue; }
                    let sr: Vec<bool> = (0..n).map(|r| row_mask & (1 << r) != 0).collect();
                    let sc: Vec<bool> = (0..n).map(|c| column_mask & (1 << c) != 0).collect();
                    let cut = match minimum_sparse_cut(&cost, &rows, &columns, &sr, &sc) {
                        Ok(Some(cut)) => cut,
                        _ => panic!("one-excess-row cut must cross a real edge"),
                    };
                    let (ur, uc) = match adjust_sparse_cut(&rows, &columns, &sr, &sc, cut.delta) {
                        Ok(output) => output,
                        Err(_) => panic!("small feasible adjustment must fit"),
                    };
                    let step = match advance_sparse_cut(&cost, &rows, &columns, &sr, &sc) {
                        Ok(Some(step)) => step,
                        _ => panic!("feasible source step must succeed"),
                    };
                    assert_eq!((step.cut.row, step.cut.column, step.cut.delta), (cut.row, cut.column, cut.delta));
                    assert_eq!((&step.rows, &step.columns), (&ur, &uc));
                    assert_eq!(ur[cut.row] + uc[cut.column], cost[cut.row][cut.column].unwrap() as i128);
                    for r in 0..n {
                        for c in 0..n {
                            if let Some(value) = cost[r][c] { assert!(ur[r] + uc[c] <= value as i128); }
                        }
                    }
                    let before: i128 = rows.iter().chain(columns.iter()).sum();
                    let after: i128 = ur.iter().chain(uc.iter()).sum();
                    assert_eq!(after, before + cut.delta);
                }
            }
        }
    }
}

#[test]
fn sparse_adjustment_checks_dimensions_sign_and_both_overflow_directions() {
    assert!(matches!(adjust_sparse_cut(&[], &[], &[], &[], 0), Ok((r,c)) if r.is_empty() && c.is_empty()));
    assert!(matches!(adjust_sparse_cut(&[0], &[], &[true], &[false], 0), Err(AssignmentError::NonSquare)));
    assert!(matches!(adjust_sparse_cut(&[0], &[0], &[true], &[false], -1), Err(AssignmentError::InvariantViolation)));
    assert!(matches!(adjust_sparse_cut(&[i128::MAX], &[0], &[true], &[false], 1), Err(AssignmentError::ArithmeticOverflow)));
    assert!(matches!(adjust_sparse_cut(&[0], &[i128::MIN], &[false], &[true], 1), Err(AssignmentError::ArithmeticOverflow)));
    assert!(matches!(adjust_sparse_cut(&[i128::MAX], &[i128::MIN], &[false], &[false], i128::MAX), Ok((r,c)) if r == [i128::MAX] && c == [i128::MIN]));
    assert!(matches!(advance_sparse_cut(&[vec![None]], &[0], &[0], &[true], &[false]), Ok(None)));
    assert!(matches!(advance_sparse_cut(&[vec![Some(-1)]], &[0], &[0], &[true], &[false]), Err(AssignmentError::InvariantViolation)));
}
