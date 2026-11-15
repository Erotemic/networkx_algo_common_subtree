use verified_ordered_core::isomorphism_choices::{
    append_isomorphism_choice, reconstruct_isomorphism_choices, IsomorphismChoice,
};

fn pair(open: u32, close: u32, head: Option<usize>, tail: Option<usize>) -> IsomorphismChoice {
    IsomorphismChoice {
        left_open: open,
        left_close: close,
        right_open: open + 100,
        right_close: close + 100,
        head,
        tail,
    }
}

#[test]
fn choices_preserve_head_tail_order_and_original_tokens() {
    let mut choices = Vec::new();
    let head = append_isomorphism_choice(&mut choices, pair(2, 3, None, None));
    let tail = append_isomorphism_choice(&mut choices, pair(8, 11, None, None));
    let before = reconstruct_isomorphism_choices(&choices, Some(head));
    let root = append_isomorphism_choice(&mut choices, pair(0, 7, Some(head), Some(tail)));
    append_isomorphism_choice(&mut choices, pair(20, 21, None, None)); // Unselected.
    assert_eq!(
        reconstruct_isomorphism_choices(&choices, Some(head)),
        before
    );
    let (left, right) = reconstruct_isomorphism_choices(&choices, Some(root)).unwrap();
    assert_eq!(left, vec![0, 2, 3, 7, 8, 11]);
    assert_eq!(right, vec![100, 102, 103, 107, 108, 111]);
    assert_eq!(
        reconstruct_isomorphism_choices(&choices, None),
        Some((vec![], vec![]))
    );
    assert_eq!(
        reconstruct_isomorphism_choices(&[], None),
        Some((vec![], vec![]))
    );
}

#[test]
fn choices_reject_out_of_bounds_roots_and_cyclic_or_forward_children() {
    assert!(reconstruct_isomorphism_choices(&[], Some(0)).is_none());
    for choices in [
        vec![pair(0, 1, Some(0), None)],
        vec![pair(0, 1, None, Some(1))],
        vec![pair(0, 1, Some(1), None), pair(2, 3, Some(0), None)],
    ] {
        assert!(reconstruct_isomorphism_choices(&choices, Some(0)).is_none());
        assert!(reconstruct_isomorphism_choices(&choices, Some(choices.len())).is_none());
    }
}

#[test]
fn long_nested_witness_uses_an_explicit_stack() {
    let depth = 4096u32;
    let choices: Vec<_> = (0..depth)
        .map(|index| {
            pair(
                depth - 1 - index,
                depth + index,
                if index == 0 {
                    None
                } else {
                    Some(index as usize - 1)
                },
                None,
            )
        })
        .collect();
    let (left, right) =
        reconstruct_isomorphism_choices(&choices, Some(depth as usize - 1)).unwrap();
    assert_eq!(left, (0..2 * depth).collect::<Vec<_>>());
    assert_eq!(right, (100..2 * depth + 100).collect::<Vec<_>>());
}
