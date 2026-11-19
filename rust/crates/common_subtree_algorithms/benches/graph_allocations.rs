//! Allocation profiling executable; instrumentation never enters the library.
//! Requested sizes exclude allocator metadata and do not measure process RSS.
use common_subtree_algorithms::{
    largest_weight_common_subtree_embedding_with_distance_penalty, make_benchmark_tree_pairs,
    maximum_common_subtree_isomorphism, CommonSubtree, ExactLabelScoring, LabeledTree,
};
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::time::Instant;

struct CountingSystem;
static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
static REQUESTED: AtomicUsize = AtomicUsize::new(0);
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

fn allocated(bytes: usize) {
    ALLOCATIONS.fetch_add(1, Relaxed);
    REQUESTED.fetch_add(bytes, Relaxed);
    let current = LIVE.fetch_add(bytes, Relaxed) + bytes;
    PEAK.fetch_max(current, Relaxed);
}

unsafe impl GlobalAlloc for CountingSystem {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pointer = System.alloc(layout);
        if !pointer.is_null() {
            allocated(layout.size());
        }
        pointer
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let pointer = System.alloc_zeroed(layout);
        if !pointer.is_null() {
            allocated(layout.size());
        }
        pointer
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        LIVE.fetch_sub(layout.size(), Relaxed);
        System.dealloc(pointer, layout);
    }
    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        let output = System.realloc(pointer, layout, size);
        if !output.is_null() {
            LIVE.fetch_sub(layout.size(), Relaxed);
            allocated(size);
        }
        output
    }
}

#[global_allocator]
static ALLOCATOR: CountingSystem = CountingSystem;

fn measure(
    name: &str,
    algorithm: &str,
    left: usize,
    right: usize,
    solve: impl FnOnce() -> CommonSubtree,
) {
    let baseline = LIVE.load(Relaxed);
    PEAK.store(baseline, Relaxed);
    ALLOCATIONS.store(0, Relaxed);
    REQUESTED.store(0, Relaxed);
    let start = Instant::now();
    let result = solve();
    let elapsed = start.elapsed().as_secs_f64();
    let allocations = ALLOCATIONS.load(Relaxed);
    let requested = REQUESTED.load(Relaxed);
    let peak_extra = PEAK.load(Relaxed) - baseline;
    println!("{{\"case\":\"{name}\",\"algorithm\":\"{algorithm}\",\"left_nodes\":{left},\"right_nodes\":{right},\"allocations_and_reallocations\":{allocations},\"total_requested_bytes\":{requested},\"peak_extra_live_requested_bytes\":{peak_extra},\"instrumented_seconds\":{elapsed},\"weight\":{},\"node_pairs\":{}}}", result.weight, result.node_pairs.len());
    std::hint::black_box(result);
}

fn profile(name: &str, left: &LabeledTree, right: &LabeledTree) {
    let scoring = ExactLabelScoring::default();
    measure(name, "isomorphism", left.len(), right.len(), || {
        maximum_common_subtree_isomorphism(left, right, &scoring)
    });
    measure(name, "embedding", left.len(), right.len(), || {
        largest_weight_common_subtree_embedding_with_distance_penalty(left, right, &scoring, 0.25)
    });
}

fn main() {
    let fixtures = make_benchmark_tree_pairs();
    for i in [0, 2, 6] {
        let case = &fixtures[i];
        profile(&case.name, &case.left.tree, &case.right.tree);
    }
    let star =
        LabeledTree::new(vec![0; 32], &(1..32).map(|u| (0, u, 0)).collect::<Vec<_>>()).unwrap();
    profile("star32", &star, &star);
    let chain = LabeledTree::new(
        vec![0; 64],
        &(1..64).map(|u| (u - 1, u, 0)).collect::<Vec<_>>(),
    )
    .unwrap();
    profile("chain64", &chain, &chain);
}
