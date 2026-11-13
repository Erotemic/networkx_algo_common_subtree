PyTorch-sized common-subtree benchmarks
=======================================

The graph-only common-subtree algorithms should eventually support partial
weight loading between related neural-network models.  A realistic optimization
target is therefore not just tiny proof examples, but module-hierarchy graphs on
the order of a ResNet50 or ResNet101 model.

This repository keeps the benchmark inputs dependency-free.  They model a
PyTorch-style **module containment tree** rather than a full tensor data-flow
DAG.  That distinction is intentional: the new paper-derived algorithms are tree
algorithms, and the partial-weight-loading use case commonly starts from a
module hierarchy where many parameters have stable semantic names even when a
few wrappers, adapters, or auxiliary modules are inserted.

Fixture design
--------------

The fixture generator lives in
``networkx_algo_common_subtree.pytorch_sized_trees``.  It builds deterministic
integer-labeled trees with human-readable module-path metadata.

The default benchmark corpus includes:

* ``resnet50_identical``: identical ResNet50-scale module trees;
* ``resnet50_name_changes_only``: same labels and structure with different
  display names, useful for checking that benchmark labels drive compatibility;
* ``resnet50_vs_wrapped_convolutions``: convolution leaves on one side are hidden
  behind wrapper modules, which gives the distance-penalized embedding routine a
  reason to skip vertices;
* ``resnet50_vs_extra_norm``: extra normalization children inside bottleneck
  blocks;
* ``resnet50_vs_squeeze_excitation``: squeeze-excitation auxiliary modules;
* ``resnet50_vs_adapters``: adapter submodules; and
* ``resnet50_vs_resnet101``: different depths with the same ResNet-like block
  vocabulary.

The generated trees are intentionally approximate.  They are meant to preserve
scale and perturbation patterns, not to duplicate any specific ``torchvision``
implementation detail.

Inspecting the fixtures
-----------------------

Print a compact summary::

    python dev/bench_pytorch_sized_common_subtree.py --summary

Write the corpus to JSON::

    python dev/bench_pytorch_sized_common_subtree.py \
        --write-json dev/pytorch_sized_tree_cases.json

The JSON export is useful for comparing external prototypes or future Python / 
Rust bindings on exactly the same case set.

Running the Rust benchmark
--------------------------

The optimized implementation for these large cases currently lives in the
``common_subtree_algorithms`` Rust crate.  Run the default quick benchmark with::

    cargo bench --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml \
        --bench pytorch_sized_trees

The quick profile measures three representative cases.  Run the full corpus with
more repetitions using environment variables::

    COMMON_SUBTREE_BENCH_PROFILE=full \
    COMMON_SUBTREE_BENCH_REPEAT=10 \
    COMMON_SUBTREE_BENCH_WARMUP=2 \
    cargo bench --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml \
        --bench pytorch_sized_trees

By default the benchmark still prints CSV rows for quick shell inspection.  For
reviewable reports and archival results, prefer the JSONL mode exposed by the
Python helper::

    python dev/bench_pytorch_sized_common_subtree.py \
        --run-rust \
        --profile quick \
        --repeat 3 \
        --warmup 1 \
        --write-results dev/pytorch_sized_results.jsonl \
        --report rich

The raw JSONL result file is the stable machine-readable artifact.  Each row
contains:

* schema identifier;
* case name and profile;
* algorithm family, either strict isomorphism or distance-penalized embedding;
* left and right node counts;
* median runtime;
* objective weight;
* number of mapped node pairs;
* left/right match ratios;
* skip penalty for embedding rows;
* representative matched module-path pairs; and
* counts of matched module labels.

The same results can be rendered later without rerunning the benchmark::

    python dev/bench_pytorch_sized_common_subtree.py \
        --results dev/pytorch_sized_results.jsonl \
        --report markdown \
        --write-report dev/pytorch_sized_results.md

If ``rich`` is installed, ``--report rich`` displays a terminal table suitable
for human review.  Without ``rich``, the report machinery falls back to markdown.
Install the optional reporting dependency with::

    python -m pip install -e '.[benchmarks]'

Relationship to correctness tests
---------------------------------

The PyTorch-sized cases are performance and regression fixtures, not proof
oracles.  The exponential Python reference implementation remains the correctness
oracle for small trees.  The large benchmark cases complement those tests by
answering a different question: whether the optimized recurrence is fast enough
on module-tree sizes that matter for partial weight loading.
