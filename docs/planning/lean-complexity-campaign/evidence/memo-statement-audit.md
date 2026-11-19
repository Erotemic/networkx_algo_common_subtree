# Memoization statement/reuse audit, 2026-11-16

This follows the [G1 decision](g1-backend-decision.md) before the generic memo
core. It audits selected declarations, not the absence of all prior art.
No external project is added to the main Lake manifest. The
[interpreter report](memo-interpreter.md) identifies the resulting local proofs
and the obligations still retained by clients.

## Inspected artifacts and compatibility

| Artifact | Exact revision | Evidence and outcome |
| --- | --- | --- |
| Lean Std / Mathlib | Lean 4.35.0 / `56a005855ea17e0b0958f73ec801ae140b0a1679` | Inspected the pinned sources, including `Std.WP`, list lookup, finite sums/cardinality, well-founded recursion and arrays. Reuse these APIs directly. The limited memoization searches found implementation caches, not the required combined adaptive memo theorem. |
| CLRS-Lean | `9352a92ba9b1d44ad1349f9e57ac31c858ec81b8` | Compiled the two original files named below against this project's pinned Lean/Mathlib, then printed their signatures and five axiom closures. Original declared toolchain is 4.32.0-rc1; no full upstream build or original-toolchain test is claimed. One upstream `if_false` deprecation warning. |
| AFP `Monad_Memo_DP` | mirror-afp-devel `bda1576f4422c042210bb7cc8406ef1335dcdfb5` | Source inspection of `DP_CRelVS`, `Memory`, tracing, bottom-up iteration and edit-distance example. Isabelle is unavailable here; no build or axiom result is claimed. |
| TauCeti | `97a5b23586f9c42610765c701daedc7522a93c26` | Limited source search in `TauCeti/` found no memoization declaration to instantiate. No new dependency/build. |
| Optional arlib / Lax | Pins recorded in the G1 report and experiment manifests | Limited searches in their library sources did not identify the combined memo interface. Their checked source-cost pilots remain useful independently. |

Local clones used VM-local `/var/tmp/subtree-memo-clrs-audit` and
`/var/tmp/subtree-memo-afp-audit`; source/build caches were not placed on virtiofs.
These paths and temporary logs are disposable, not repository dependencies.

## CLRS-Lean: distinguish consistency, counting and execution

The first selected file is
[`Section_14_3_Elements_Of_Dynamic_Programming.lean`](https://github.com/tanktechnology/CLRS-Lean/blob/9352a92ba9b1d44ad1349f9e57ac31c858ec81b8/src/CLRSLean/FourthEdition/Chapter_14/Section_14_3_Elements_Of_Dynamic_Programming.lean).
Its namespace is `CLRS.Chapter15` despite the Chapter_14 path.
`MemoCacheConsistent correct cache` is exactly
`∀ s v, cache s = some v → v = correct s`; its elimination theorem is direct.
`distinctCacheStates_le_length` bounds a filtered supplied list's distinct
cached states. Neither theorem establishes how many expansions an evaluator
performed. The local `CacheOps.Sound` uses this standard consistency pattern;
it is not attributed as a new result.

The companion
[`Execution.lean`](https://github.com/tanktechnology/CLRS-Lean/blob/9352a92ba9b1d44ad1349f9e57ac31c858ec81b8/src/CLRSLean/FourthEdition/Chapter_14/Section_14_3_Elements_Of_Dynamic_Programming/Execution.lean)
does prove statements about actual executions. `buildLayers_correct` takes a
cell-step correctness premise for all previously correct rows.
`buildLayers_evaluatedStates_nodup` proves distinct emitted `(layer,index)`
events without assuming their distinctness, and `buildLayers_cellWrites_eq_events`
identifies writes with those events. This is a reusable bottom-up schedule
pattern. The missing adapter here is an adaptive top-down request interpreter
with arbitrary warm contents, repeated requests, sequential roots, and exact
root-plus-body accounting. Replacing the current algorithm by `buildLayers`
would require a separate schedule correspondence proof. The algorithm-specific
rod-cutting source was also inspected; it is not the requested generic theorem.

Printed axiom closures: `MemoCacheConsistent_eq` uses none;
`distinctCacheStates_le_length`, `buildLayers_correct` and
`buildLayers_evaluatedStates_nodup` use only
`propext`, `Classical.choice`, `Quot.sound`;
`buildLayers_cellWrites_eq_events` uses only `propext`.

## Isabelle: reusable memoization correctness, stronger preservation needed

The [Wimmer–Hu–Nipkow ITP 2018 paper](https://www21.in.tum.de/~nipkow/pubs/itp18dp.pdf)
was successfully retrieved for this follow-up. The earlier failed fetch remains
a historical record. Its state-monad memoization/correspondence and memory
parameterization inform the separation of a cache-free body from its handler;
they do not justify transferring a runtime bound from value equality.

In pinned [`state_monad/DP_CRelVS.thy`](https://github.com/isabelle-prover/mirror-afp-devel/blob/bda1576f4422c042210bb7cc8406ef1335dcdfb5/thys/Monad_Memo_DP/state_monad/DP_CRelVS.thy),
`state_mem_defs` parameterizes lookup/update, and `mem_correct` requires
`lookup_inv`/`update_inv` preservation. Its `lookup_correct` and `update_correct`
allow the resulting abstract partial map to be a **submap** of the old map or
the updated map. Thus these value-consistency laws allow forgetting entries;
they do not imply once-only expansion. Local immutable reads and
`CacheOps.write_other` equality are deliberately stronger. This is an additional
local requirement, not a correction to the upstream functional theorem.

[`state_monad/Memory.thy`](https://github.com/isabelle-prover/mirror-afp-devel/blob/bda1576f4422c042210bb7cc8406ef1335dcdfb5/thys/Monad_Memo_DP/state_monad/Memory.thy)
supplies default/RBT memory interpretations and memoized result correctness.
Its tracing lookup/update wrappers emit Missed/Found/Stored events and retain
memory correctness. The inspected statements do not directly establish this
campaign's root-plus-direct-request identity or its initially-absent expansion
bound. Those require a theorem about the selected interpreter and preservation
contract. `util/Tracing.thy` separately concerns printable tracing/erasure.

[`example/Min_Ed_Dist0.thy`](https://github.com/isabelle-prover/mirror-afp-devel/blob/bda1576f4422c042210bb7cc8406ef1335dcdfb5/thys/Monad_Memo_DP/example/Min_Ed_Dist0.thy)
provides independently specified edits, correctness/minimality, an index
recurrence and memoization examples. This is the conceptual reuse target for
the still-open unrelated client. No Isabelle theorem has been silently imported
as a Lean assumption. The [AFP entry](https://devel.isa-afp.org/entries/Monad_Memo_DP.html)
records the upstream distribution and license.

## Reproduction and retained scope

After checking out the pinned CLRS revision on local disk, create
`.lake/build/lib/lean/CLRSLean/FourthEdition/Chapter_14/Section_14_3_Elements_Of_Dynamic_Programming/`.
Inside this repository's `proofs`, use `lake env bash`, prefix that checkout's
`.lake/build/lib/lean` to `LEAN_PATH`, change to its `src/`, and invoke `lean -o`
for the two selected sources in dependency order. Then import the companion
and run `#check`/`#print axioms` on the five names above. This checks the
unchanged selected source under the main environment without changing a pin.
Local outputs were `/var/tmp/subtree-memo-clrs-build.log` and
`/var/tmp/subtree-memo-clrs-statements.log`.

The resulting local theory reuses native `EStateM`/Std.WP, finite-list induction,
Mathlib sums/cardinality and upstream cache-consistency patterns. Its combined
interpreter/exact-accounting theorem is a campaign synthesis over those ideas.
This audit does not close all G0 reconnaissance, W04's other interfaces, W05's
two full clients, upstream independent review, or any source/RAM/Rust runtime
adequacy obligation.
