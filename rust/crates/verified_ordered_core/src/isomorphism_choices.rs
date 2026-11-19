//! Integer-only witness materialization used by the production ordered solver.
//!
//! Each stored pair points to older head/tail choices. Scores and affinities
//! stay in the caller; only the winning token indices are materialized here.

pub struct IsomorphismChoice {
    pub left_open: u32,
    pub left_close: u32,
    pub right_open: u32,
    pub right_close: u32,
    pub head: Option<usize>,
    pub tail: Option<usize>,
}

/// Append one matched-pair choice and return its stable arena index.
/// Existing choices remain unchanged. The production DP supplies head/tail
/// indices from the old arena, making both children older than this entry.
#[inline]
pub fn append_isomorphism_choice(
    choices: &mut Vec<IsomorphismChoice>,
    choice: IsomorphismChoice,
) -> usize {
    let index = choices.len();
    choices.push(choice);
    index
}

enum Visit {
    Pair(usize),
    Close(u32, u32),
}

fn older_child(child: Option<usize>, parent: usize) -> bool {
    match child {
        None => true,
        Some(index) => index < parent,
    }
}

// Keep an active prefix of reusable slots. The pinned extraction backend
// supports these indexed reads/writes; Vec::pop is an unmodeled external.
fn push_visit(mut pending: Vec<Visit>, length: usize, visit: Visit) -> (Vec<Visit>, usize) {
    if length < pending.len() {
        pending[length] = visit;
    } else {
        pending.push(visit);
    }
    (pending, length + 1)
}

/// Emit one selected ordered forest, in original token coordinates.
///
/// Empty choices emit empty vectors. Invalid roots and nondecreasing child
/// links return `None`, preventing cycles even for externally built arenas.
/// Valid children are emitted as open, head, close, tail; shared choices are
/// expanded at each occurrence. Output storage depends on the chosen witness,
/// rather than all DP states. The actual-source Lean proof derives emitted
/// tokens and termination from valid earlier-child links and output bounds.
pub fn reconstruct_isomorphism_choices(
    choices: &[IsomorphismChoice],
    root: Option<usize>,
) -> Option<(Vec<u32>, Vec<u32>)> {
    let mut pending = Vec::new();
    match root {
        None => {}
        Some(index) => pending.push(Visit::Pair(index)),
    }
    let mut left = Vec::new();
    let mut right = Vec::new();
    let mut length = pending.len();
    while length > 0 {
        length -= 1;
        let visit = &pending[length];
        match visit {
            Visit::Close(left_close, right_close) => {
                left.push(*left_close);
                right.push(*right_close);
            }
            Visit::Pair(index) => {
                let index = *index;
                if index >= choices.len() {
                    return None;
                }
                let choice = &choices[index];
                if !older_child(choice.head, index) || !older_child(choice.tail, index) {
                    return None;
                }
                left.push(choice.left_open);
                right.push(choice.right_open);
                match choice.tail {
                    None => {}
                    Some(tail) => {
                        (pending, length) = push_visit(pending, length, Visit::Pair(tail))
                    }
                }
                (pending, length) = push_visit(
                    pending,
                    length,
                    Visit::Close(choice.left_close, choice.right_close),
                );
                match choice.head {
                    None => {}
                    Some(head) => {
                        (pending, length) = push_visit(pending, length, Visit::Pair(head))
                    }
                }
            }
        }
    }
    Some((left, right))
}
