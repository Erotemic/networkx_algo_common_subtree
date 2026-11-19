use std::collections::HashSet;
use verified_assignment_core::uniform_pairs::uniform_pair_indices;

fn check(left: usize, right: usize, deleted: Option<usize>) {
    let pairs = uniform_pair_indices(left, right, deleted);
    let available_right = right - usize::from(deleted.is_some_and(|r| r < right));
    assert_eq!(pairs.len(), left.min(available_right));
    let mut rows = HashSet::new();
    let mut columns = HashSet::new();
    for &(row, column) in &pairs {
        assert!(row < left && column < right);
        assert_ne!(Some(column), deleted);
        assert!(rows.insert(row));
        assert!(columns.insert(column));
    }
    assert!(pairs.windows(2).all(|p| p[0].0 < p[1].0));
    assert_eq!(pairs, uniform_pair_indices(left, right, deleted));
}

#[test]
fn empty_rectangular_and_every_original_deletion() {
    for left in 0..=16 {
        for right in 0..=16 {
            check(left, right, None);
            for removed in 0..=right {
                check(left, right, Some(removed));
            }
            check(left, right, Some(usize::MAX));
        }
    }
    // The replacement keeps its original index, not a compressed column ID.
    assert_eq!(uniform_pair_indices(2, 5, Some(0)), vec![(0, 2), (1, 1)]);
    assert_eq!(uniform_pair_indices(5, 2, Some(0)), vec![(1, 1)]);
    assert_eq!(uniform_pair_indices(2, 5, Some(4)), vec![(0, 0), (1, 1)]);
}

#[test]
fn extreme_dimensions_with_small_outputs() {
    for (left, right) in [
        (0, usize::MAX),
        (usize::MAX, 0),
        (1, usize::MAX),
        (usize::MAX, 1),
    ] {
        for deleted in [None, Some(0), Some(1), Some(usize::MAX)] {
            check(left, right, deleted);
        }
    }
}
