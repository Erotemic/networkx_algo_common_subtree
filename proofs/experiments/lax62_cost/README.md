# Isolated Lax62 timed lookup pilot

This standalone project interprets the same four generated lookup bodies as
the native WP and charged arlib pilots. It uses the upstream NREST timed
computation, currency and bind/refinement laws. Main dependencies, production
Rust, generated programs and backend defaults are unchanged.

Pins: Lean 4.35.0; main Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`; Lax62Proofs
`0503df0eaf4e41104b9a3aa31e3e028b5adf7a0e` (`refinement-tower/proofs`);
the transitive word-RAM packages are pinned to
`9394e531cc51cb67a0214bca3f9264dfe97ba5c7`. The manifest preserves every
overlapping main dependency revision. The upstream declares Lean 4.33.0; its
selected `ACost`, `NREST.Basic` and `NREST.Pw` sources build unmodified here.
This is not a full upstream project, IR/codegen, or original-toolchain build.
The upstream license is Apache-2.0 (`refinement-tower/LICENSE`).

From the repository root on a virtiofs VM, then from this directory:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
cd proofs/experiments/lax62_cost
lake build
lake env lean LaxSpike/SourceExecution.lean
```

The optional build passes (3,490 jobs). It compiles the source-model dependency
chain, not every unrelated main-library target. `SourceExecution.lean` prints
the final function/refinement signatures and ten endpoint axiom closures, all
within the established baseline. The new module has no linter warnings; the
upstream legacy/deprecation warnings are retained. The native and arlib pilots
also print their final signatures for comparison.

`action`, `execute` and `run` interpret the generated syntax through
`NRest.bindT`, `returnT` and `consume`. Instruction/access work and five packet
currencies remain separate. They do not inspect cost annotations or run the
old interpreter inside a free return. `run_exact` proves equality with the
original operational interpretation for arbitrary body maps and fuel.
`run_success` proves exact singleton behavior and `nofailT` for successful
operational runs. `lookup_spec`, `compare_spec`, `copy_spec` and
`copyResult_spec` use upstream `NRest.spec` and its refinement order.

`original_empty_meets_zero_compare` proves the original source satisfies the
empty-input contract. `extra_compare_violates_old_budget` proves that the actual
compiled/reified Rust mutation fails it. Only comparison work is constrained;
all other currencies have infinite budgets, so this result does not depend
on rejecting a loose aggregate instruction envelope.

This is **operational C2**, not a Rust, heap, allocator, space or Lax IR/RAM
realization theorem. The Python reifier, read-only reference interpretation
and source/compiler relationship retain the original pilot's boundaries.
Unsupported/insufficient-fuel execution becomes NREST failure, which cannot
refine a successful finite specification. No failure-path work bound is claimed.
The successful contracts use the original explicit sufficient-fuel premises.

During this execution only the exact-pinned Aeneas `.lake` cache was reused
through a nested bind mount. Remove it before unmounting the outer experiment
cache. Ordinary fresh installations can let Lake materialize/build the pinned
dependencies. See the [G1 comparison and decision](../../../docs/planning/lean-complexity-campaign/evidence/g1-backend-decision.md)
for the other candidates, precise remaining machine/source gaps, and next work.
