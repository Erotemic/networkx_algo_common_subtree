use std::collections::BTreeMap;
use std::env;
use std::time::{Duration, Instant};

use common_subtree_algorithms::{
    label_name, largest_weight_common_subtree_embedding_with_distance_penalty,
    make_benchmark_tree_pairs, maximum_common_subtree_isomorphism, CommonSubtree,
    ExactLabelScoring, ModuleTree,
};

fn env_usize(name: &str, default: usize) -> usize {
    env::var(name)
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(default)
}

fn env_f64(name: &str, default: f64) -> f64 {
    env::var(name)
        .ok()
        .and_then(|value| value.parse::<f64>().ok())
        .unwrap_or(default)
}

fn median_duration(mut times: Vec<Duration>) -> Duration {
    times.sort_unstable();
    times[times.len() / 2]
}

fn seconds(duration: Duration) -> f64 {
    duration.as_secs_f64()
}

fn bench_one<F, R>(mut run: F, warmup: usize, repeat: usize) -> (Duration, R)
where
    F: FnMut() -> R,
{
    let mut result = None;
    for _ in 0..warmup {
        result = Some(run());
    }

    let mut times = Vec::with_capacity(repeat);
    for _ in 0..repeat {
        let start = Instant::now();
        result = Some(run());
        times.push(start.elapsed());
    }
    (median_duration(times), result.expect("benchmark must run at least once"))
}

#[derive(Clone, Debug)]
struct BenchRow<'a> {
    schema: &'static str,
    profile: &'a str,
    case: &'a str,
    algorithm: &'static str,
    left_nodes: usize,
    right_nodes: usize,
    median_seconds: f64,
    weight: f64,
    node_pairs: usize,
    left_match_ratio: f64,
    right_match_ratio: f64,
    skip_penalty: Option<f64>,
    warmup: usize,
    repeat: usize,
    sample_pairs: Vec<String>,
    label_counts: Vec<(String, usize)>,
    description: &'a str,
}

fn summarize_result<'a>(
    profile: &'a str,
    case_name: &'a str,
    algorithm: &'static str,
    left: &ModuleTree,
    right: &ModuleTree,
    elapsed: Duration,
    result: &CommonSubtree,
    skip_penalty: Option<f64>,
    warmup: usize,
    repeat: usize,
    sample_limit: usize,
    description: &'a str,
) -> BenchRow<'a> {
    let mut sample_pairs = Vec::new();
    for &(u, v) in result.node_pairs.iter().take(sample_limit) {
        sample_pairs.push(format!("{} -> {}", left.node_names[u], right.node_names[v]));
    }

    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    for &(u, _v) in &result.node_pairs {
        let name = label_name(left.tree.node_label(u)).to_string();
        *counts.entry(name).or_insert(0) += 1;
    }

    BenchRow {
        schema: "networkx_algo_common_subtree.pytorch_sized_benchmark_result.v1",
        profile,
        case: case_name,
        algorithm,
        left_nodes: left.len(),
        right_nodes: right.len(),
        median_seconds: seconds(elapsed),
        weight: result.weight,
        node_pairs: result.node_pairs.len(),
        left_match_ratio: ratio(result.node_pairs.len(), left.len()),
        right_match_ratio: ratio(result.node_pairs.len(), right.len()),
        skip_penalty,
        warmup,
        repeat,
        sample_pairs,
        label_counts: counts.into_iter().collect(),
        description,
    }
}

fn ratio(num: usize, den: usize) -> f64 {
    if den == 0 {
        0.0
    } else {
        num as f64 / den as f64
    }
}

fn main() {
    let profile = env::var("COMMON_SUBTREE_BENCH_PROFILE").unwrap_or_else(|_| "quick".to_string());
    let format = env::var("COMMON_SUBTREE_BENCH_FORMAT").unwrap_or_else(|_| "csv".to_string());
    let default_repeat = if profile == "full" { 10 } else { 3 };
    let default_warmup = if profile == "full" { 2 } else { 1 };
    let repeat = env_usize("COMMON_SUBTREE_BENCH_REPEAT", default_repeat).max(1);
    let warmup = env_usize("COMMON_SUBTREE_BENCH_WARMUP", default_warmup);
    let skip_penalty = env_f64("COMMON_SUBTREE_BENCH_SKIP_PENALTY", 0.25);
    let sample_limit = env_usize("COMMON_SUBTREE_BENCH_SAMPLE_LIMIT", 6);

    let mut cases = make_benchmark_tree_pairs();
    if profile != "full" {
        // Keep the default local run short, but include one wrapper case where
        // the embedding routine should have a reason to skip inserted vertices.
        cases.retain(|case| {
            matches!(
                case.name,
                "resnet50_identical" | "resnet50_vs_wrapped_convolutions" | "resnet50_vs_resnet101"
            )
        });
    }

    if format == "csv" {
        println!("profile,case,algorithm,left_nodes,right_nodes,median_seconds,weight,node_pairs,left_match_ratio,right_match_ratio,skip_penalty,warmup,repeat,sample_pairs,label_counts,description");
    }

    let scoring = ExactLabelScoring::default();

    for case in cases {
        let (iso_time, iso_result) = bench_one(
            || maximum_common_subtree_isomorphism(&case.left.tree, &case.right.tree, &scoring),
            warmup,
            repeat,
        );
        let iso_row = summarize_result(
            &profile,
            case.name,
            "isomorphism",
            &case.left,
            &case.right,
            iso_time,
            &iso_result,
            None,
            warmup,
            repeat,
            sample_limit,
            case.description,
        );
        print_row(&format, &iso_row);

        let (embedding_time, embedding_result) = bench_one(
            || {
                largest_weight_common_subtree_embedding_with_distance_penalty(
                    &case.left.tree,
                    &case.right.tree,
                    &scoring,
                    skip_penalty,
                )
            },
            warmup,
            repeat,
        );
        let embedding_row = summarize_result(
            &profile,
            case.name,
            "embedding",
            &case.left,
            &case.right,
            embedding_time,
            &embedding_result,
            Some(skip_penalty),
            warmup,
            repeat,
            sample_limit,
            case.description,
        );
        print_row(&format, &embedding_row);
    }
}

fn print_row(format: &str, row: &BenchRow<'_>) {
    match format {
        "jsonl" | "json" => println!("{}", row_to_json(row)),
        "csv" => println!("{}", row_to_csv(row)),
        other => {
            eprintln!("unknown COMMON_SUBTREE_BENCH_FORMAT={other:?}; expected csv or jsonl");
            std::process::exit(2);
        }
    }
}

fn row_to_csv(row: &BenchRow<'_>) -> String {
    let sample_pairs = row.sample_pairs.join(" | ");
    let label_counts = row
        .label_counts
        .iter()
        .map(|(name, count)| format!("{name}:{count}"))
        .collect::<Vec<_>>()
        .join(" | ");
    let skip_penalty = row
        .skip_penalty
        .map(|value| format!("{value:.6}"))
        .unwrap_or_default();
    [
        row.profile.to_string(),
        row.case.to_string(),
        row.algorithm.to_string(),
        row.left_nodes.to_string(),
        row.right_nodes.to_string(),
        format!("{:.9}", row.median_seconds),
        format!("{:.6}", row.weight),
        row.node_pairs.to_string(),
        format!("{:.6}", row.left_match_ratio),
        format!("{:.6}", row.right_match_ratio),
        skip_penalty,
        row.warmup.to_string(),
        row.repeat.to_string(),
        sample_pairs,
        label_counts,
        row.description.to_string(),
    ]
    .iter()
    .map(|field| escape_csv(field))
    .collect::<Vec<_>>()
    .join(",")
}

fn row_to_json(row: &BenchRow<'_>) -> String {
    let sample_pairs = row
        .sample_pairs
        .iter()
        .map(|item| json_string(item))
        .collect::<Vec<_>>()
        .join(",");
    let label_counts = row
        .label_counts
        .iter()
        .map(|(name, count)| format!("{{\"label\":{},\"count\":{}}}", json_string(name), count))
        .collect::<Vec<_>>()
        .join(",");
    let skip_penalty = row
        .skip_penalty
        .map(|value| format!("{value:.9}"))
        .unwrap_or_else(|| "null".to_string());

    format!(
        "{{\"schema\":{},\"profile\":{},\"case\":{},\"algorithm\":{},\"left_nodes\":{},\"right_nodes\":{},\"median_seconds\":{:.9},\"weight\":{:.6},\"node_pairs\":{},\"left_match_ratio\":{:.9},\"right_match_ratio\":{:.9},\"skip_penalty\":{},\"warmup\":{},\"repeat\":{},\"sample_pairs\":[{}],\"label_counts\":[{}],\"description\":{}}}",
        json_string(row.schema),
        json_string(row.profile),
        json_string(row.case),
        json_string(row.algorithm),
        row.left_nodes,
        row.right_nodes,
        row.median_seconds,
        row.weight,
        row.node_pairs,
        row.left_match_ratio,
        row.right_match_ratio,
        skip_penalty,
        row.warmup,
        row.repeat,
        sample_pairs,
        label_counts,
        json_string(row.description),
    )
}

fn escape_csv(text: &str) -> String {
    if text.contains(',') || text.contains('"') || text.contains('\n') {
        format!("\"{}\"", text.replace('"', "\"\""))
    } else {
        text.to_string()
    }
}

fn json_string(text: &str) -> String {
    let mut out = String::from("\"");
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch.is_control() => out.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}
