Exact rational ordered isomorphism
=================================

``impl="verified-lean"`` exposes a compiled Lean solver for maximum-weight
ordered subtree isomorphism, with either root policy. It accepts exact integer
or ``fractions.Fraction`` affinities and returns an exact ``Fraction`` score.
Zero forbids a match; negative weights are rejected. Float inputs require an
explicit conversion, such as ``Fraction.from_float``, or selection of an
existing floating-point backend.

For balanced sequences::

    from fractions import Fraction
    from networkx_algo_common_subtree.balanced_isomorphism import (
        longest_common_balanced_isomorphism,
    )

    witnesses, value = longest_common_balanced_isomorphism(
        "()()", "()()", {"(": ")"},
        node_affinity=lambda a, b: Fraction(1, 3),
        impl="verified-lean", rooted=True,
    )
    assert witnesses == ("()()", "()()")
    assert value == Fraction(2, 3)

The same backend works with
``maximum_common_ordered_subtree_isomorphism(tree1, tree2, ...)`` and returns
subgraphs containing original NetworkX nodes. ``rooted=True`` preserves the
input root level; the default can choose descendant roots. Sibling order and
parent edges are preserved in both modes. Tied witnesses can differ between
backends. Balanced-sequence outputs preserve string/list/tuple containers,
including Python strings containing lone surrogates.

What is verified
----------------

The executable calls ``RationalSolver.solveResult`` directly. Lean proves:

* termination of the memoized algorithm and correctness of its real hash cache;
* equality to the independent rooted/general rational affinity recurrence;
* independently specified feasibility and global optimality;
* exact additive score, original preorder, and endpoint uniqueness for unique
  original input identities.

The complete endpoint is
``SubtreeProofs.Paper2004.AnnotatedIso.RationalSolver.solveResult_correct``;
``solve_unique_endpoints`` supplies uniqueness. Both are checked on pinned Lean
4.35.0. This is direct compilation of the proved Lean implementation, rather
than a claim that the optimized floating Rust implementation has been proved.
The standard Lean compiler/runtime and rational/hash-map implementation are in
the execution trust boundary. Python/NetworkX conversion, JSON encoding and
process transport are independently tested integration boundaries.
Running-time bounds are not part of the theorem.

The affinity callback is evaluated eagerly once for each original node pair;
it must describe fixed pair weights. A native worker is reused within each
Python process, and requests from threads are serialized. Every request starts
with a fresh solver cache. Forked children create their own worker. Explicitly
selecting this backend raises ``ImportError`` if its executable is unavailable;
it never silently substitutes another algorithm.

Build and availability
----------------------

The native executable is an optional wheel component. Build tooling requires
the pinned Lean toolchain and mathematical dependencies; the installed runtime
does not require Lean, Lake, Mathlib sources or the development submodule.
From the repository root, prepare VM-local build caches and dependencies::

    dev/setup-build-caches.sh
    dev/setup-build-caches.sh --status
    (cd proofs && lake exe cache get && lake build verified_ordered)
    python -m pip wheel . --no-deps --wheel-dir /var/tmp/subtree-wheels \
      --config-settings=build-dir=/var/tmp/subtree-wheel-build \
      --config-settings=cmake.define.BUILD_LEAN_BACKEND=ON \
      --config-settings=cmake.define.REQUIRE_RUST_EXTENSIONS=ON
    python -m pip install /var/tmp/subtree-wheels/*.whl

The installed binary lives in ``networkx_algo_common_subtree/_bin``. Development
checkouts also find ``proofs/.lake/build/bin/verified_ordered``. The environment
variable ``COMMON_SUBTREE_VERIFIED_LEAN`` can select a development executable.
Backend discovery lists ``verified-lean`` with ``include_restricted=True``.

Performance and backend choice
------------------------------

The optimized floating Rust/Cython/Python implementations remain selectable;
``auto`` retains its existing policy. A local installed-wheel comparison on
8/16/32-node stars, chains and balanced trees, for both policies and exactly
representable dyadic weights, measured a median Lean/Rust latency ratio of
7.60 (range 4.56--26.02). Median ratios against Cython and Python iterative
references were 4.16 and 3.86. These timings include conversion, IPC, solving
and reconstruction. The first Lean call additionally costs about 125 ms on
this VM; warmed requests reuse the worker. These are small development
measurements, not universal performance claims.

Use ``verified-lean`` for the exact rational guarantee and ``iter-rust`` for the
existing empirically tested floating implementation when that tradeoff fits.
Further score caching and representation improvements can reduce the verified
backend's cost. Full source refinement of the optimized Rust algorithm remains
a separate research/engineering task.
