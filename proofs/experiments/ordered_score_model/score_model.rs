//! Extraction spike only; not a production backend.
//! Charon treats exactly this module as opaque. Its Lean model uses rationals,
//! so the extracted callers prove control flow under ideal arithmetic, not f64.
pub mod arithmetic {
    #[derive(Clone, Copy, Debug)]
    pub struct Score(pub f64);

    pub fn zero() -> Score {
        Score(0.0)
    }

    pub fn add(left: Score, right: Score) -> Score {
        Score(left.0 + right.0)
    }

    pub fn positive(value: Score) -> bool {
        value.0 > 0.0
    }

    pub fn greater(left: Score, right: Score) -> bool {
        left.0 > right.0
    }
}

pub struct Candidate {
    pub score: arithmetic::Score,
    pub witness: u32,
}

/// Keep the first witness on ties, as in the production rooted recurrence.
pub fn improve(best: Candidate, candidate: Candidate) -> Candidate {
    if arithmetic::greater(candidate.score, best.score) {
        candidate
    } else {
        best
    }
}

/// One rooted recurrence step, given already computed child candidates.
/// Witness 0 denotes the empty candidate; other IDs are opaque to this spike.
pub fn level_step(
    drop_right: Candidate,
    drop_left: Candidate,
    head: arithmetic::Score,
    tail: arithmetic::Score,
    affinity: arithmetic::Score,
    matched_witness: u32,
) -> Candidate {
    let empty = Candidate { score: arithmetic::zero(), witness: 0 };
    let best = improve(empty, drop_right);
    let best = improve(best, drop_left);
    if arithmetic::positive(affinity) {
        let score = arithmetic::add(arithmetic::add(head, tail), affinity);
        improve(best, Candidate { score, witness: matched_witness })
    } else {
        best
    }
}

#[cfg(test)]
mod tests {
    use super::{arithmetic::Score, *};

    fn candidate(score: f64, witness: u32) -> Candidate {
        Candidate { score: Score(score), witness }
    }

    #[test]
    fn tie_order_and_positive_affinity() {
        let result = level_step(candidate(4.0, 1), candidate(4.0, 2),
                                Score(1.0), Score(1.0), Score(2.0), 3);
        assert_eq!((result.score.0, result.witness), (4.0, 1));
        let result = level_step(candidate(0.0, 1), candidate(0.0, 2),
                                Score(100.0), Score(100.0), Score(0.0), 3);
        assert_eq!((result.score.0, result.witness), (0.0, 0));
        let result = level_step(candidate(4.0, 1), candidate(3.0, 2),
                                Score(1.5), Score(1.0), Score(2.0), 3);
        assert_eq!((result.score.0, result.witness), (4.5, 3));
    }

    #[test]
    fn integral_float_inputs_do_not_imply_exact_sums() {
        // Both inputs are exactly represented; their mathematical sum is not.
        let result = arithmetic::add(Score(9_007_199_254_740_992.0), Score(1.0));
        assert_eq!(result.0, 9_007_199_254_740_992.0);
    }
}
