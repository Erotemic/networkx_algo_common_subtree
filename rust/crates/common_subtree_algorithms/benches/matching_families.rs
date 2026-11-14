//! Related-family kernel timing, including witnesses and induced-matrix copies.
use common_subtree_algorithms::{
    max_weight_bipartite_matching, max_weight_bipartite_matching_with_right_deletions,
};
use std::hint::black_box;
use std::time::Instant;

fn repeated(call: impl Fn() -> Vec<f64>, repeat: usize, warmup: usize) -> (Vec<f64>, Vec<f64>) {
    for _ in 0..warmup {
        black_box(call());
    }
    let mut timings = Vec::with_capacity(repeat);
    let mut result = Vec::new();
    for _ in 0..repeat {
        let start = Instant::now();
        result = black_box(call());
        timings.push(start.elapsed().as_secs_f64());
    }
    (timings, result)
}

fn median(samples: &[f64]) -> f64 {
    let mut ordered = samples.to_vec();
    ordered.sort_by(f64::total_cmp);
    ordered[ordered.len() / 2]
}

fn main() {
    let repeat = std::env::var("COMMON_SUBTREE_BENCH_REPEAT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(3);
    let warmup = std::env::var("COMMON_SUBTREE_BENCH_WARMUP")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);
    assert!(repeat > 0);
    for (left, right) in [
        (8, 8),
        (16, 16),
        (32, 32),
        (4, 64),
        (64, 4),
        (1, 256),
        (256, 1),
    ] {
        for shape in ["uniform", "signed-optional"] {
            let mut seed = 2016_u64;
            let weights: Vec<Vec<_>> = (0..left)
                .map(|_| {
                    (0..right)
                        .map(|_| {
                            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
                            if shape == "uniform" {
                                Some(1.0)
                            } else {
                                [
                                    None,
                                    Some(-2.0),
                                    Some(0.0),
                                    Some(0.125),
                                    Some(1.0),
                                    Some(4.0),
                                ][(seed >> 32) as usize % 6]
                            }
                        })
                        .collect()
                })
                .collect();
            let (independent_samples, independent) = repeated(
                || {
                    let mut result = vec![max_weight_bipartite_matching(&weights).weight];
                    for deleted in 0..right {
                        let induced: Vec<Vec<_>> = weights
                            .iter()
                            .map(|row| {
                                row.iter()
                                    .enumerate()
                                    .filter(|&(j, _)| j != deleted)
                                    .map(|(_, &value)| value)
                                    .collect()
                            })
                            .collect();
                        result.push(max_weight_bipartite_matching(&induced).weight);
                    }
                    result
                },
                repeat,
                warmup,
            );
            let (family_samples, family) = repeated(
                || {
                    let family = max_weight_bipartite_matching_with_right_deletions(&weights);
                    std::iter::once(family.base.weight)
                        .chain((0..right).map(|j| family.without_right(j).unwrap().weight))
                        .collect()
                },
                repeat,
                warmup,
            );
            assert_eq!(independent, family);
            let independent_time = median(&independent_samples);
            let family_time = median(&family_samples);
            println!("{{\"shape\":\"{shape}\",\"left\":{left},\"right\":{right},\"repeat\":{repeat},\"warmup\":{warmup},\"independent_samples\":{independent_samples:?},\"family_samples\":{family_samples:?},\"independent_seconds\":{independent_time},\"family_seconds\":{family_time},\"speedup\":{},\"base_weight\":{}}}", independent_time / family_time, family[0]);
        }
    }
}
