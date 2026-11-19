use super::*;

// Independent injections use original coordinates and simply exclude a right
// endpoint; they neither build the production mask nor call another solver.
fn optimum(weights: &[Vec<Option<i64>>], removed: Option<usize>) -> i128 {
    fn visit(
        weights: &[Vec<Option<i64>>],
        removed: Option<usize>,
        row: usize,
        used: &mut [bool],
    ) -> i128 {
        if row == weights.len() {
            return 0;
        }
        let mut best = visit(weights, removed, row + 1, used);
        for col in 0..used.len() {
            if !used[col] && removed != Some(col) {
                if let Some(weight) = weights[row][col] {
                    used[col] = true;
                    best = best.max(weight as i128 + visit(weights, removed, row + 1, used));
                    used[col] = false;
                }
            }
        }
        best
    }
    visit(
        weights,
        removed,
        0,
        &mut vec![false; weights.first().map_or(0, Vec::len)],
    )
}

fn check_result(weights: &[Vec<Option<i64>>], removed: Option<usize>, result: &PartialMatching) {
    let mut left = vec![false; weights.len()];
    let mut right = vec![false; weights.first().map_or(0, Vec::len)];
    let mut score = 0i128;
    for pair in &result.pairs {
        assert!(pair.left < left.len() && pair.right < right.len());
        assert!(!left[pair.left] && !right[pair.right]);
        assert_ne!(removed, Some(pair.right));
        left[pair.left] = true;
        right[pair.right] = true;
        let value = weights[pair.left][pair.right].unwrap();
        assert!(value > 0);
        score += value as i128;
    }
    assert_eq!(result.weight, score);
    assert_eq!(score, optimum(weights, removed));
}

fn check(weights: &[Vec<Option<i64>>]) {
    let family = max_weight_matching_deletions(weights).unwrap();
    assert_eq!(
        family.without_right.len(),
        weights.first().map_or(0, Vec::len)
    );
    check_result(weights, None, &family.original);
    for (removed, result) in family.without_right.iter().enumerate() {
        check_result(weights, Some(removed), result);
        if !family
            .original
            .pairs
            .iter()
            .any(|pair| pair.right == removed)
        {
            assert_eq!(result, &family.original);
        }
    }
}

#[test]
fn deletion_families_match_independent_injections() {
    let mut state = 0x459c_17b2_783e_ac41u64;
    for left in 0..=6 {
        for right in 0..=6 {
            for _ in 0..8 {
                let mut weights = vec![vec![None; right]; left];
                for row in &mut weights {
                    for value in row {
                        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
                        *value = if state % 4 == 0 {
                            None
                        } else {
                            Some(((state >> 32) % 31) as i64 - 15)
                        };
                    }
                }
                check(&weights);
            }
        }
    }
    check(&[
        vec![Some(i64::MAX), None, Some(i64::MIN)],
        vec![None, Some(i64::MAX), Some(0)],
    ]);
    check(&[
        vec![Some(5), Some(5), Some(5)],
        vec![Some(5), Some(5), Some(5)],
    ]);
    assert_eq!(
        max_weight_matching_deletions(&[vec![], vec![Some(1)]]),
        Err(MatchingError::NonRectangular)
    );
}
