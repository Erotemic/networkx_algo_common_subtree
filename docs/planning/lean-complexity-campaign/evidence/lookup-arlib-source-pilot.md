# Charged arlib source interpreter: 2026-11-16

Baseline: `ad4b368`. This is W03's charged arlib pilot over the **same four
generated source-model functions** as the native WP pilot, at their existing
operational C2 boundary. It does not complete G1, a RAM realization, or SRC-01/C3.
Main dependency pins and Rust/generated sources are unchanged.

## Executed computation and exact correspondence

[`ArlibSpike/SourceExecution.lean`](../../../../proofs/experiments/arlib_cost/ArlibSpike/SourceExecution.lean)
interprets the existing generated `Code` using `OptionT (Charged Coin Unit)`.
It is driven by the actual generated bodies, including their primitive actions,
selected branches, early returns, recursive calls and Box constructor calls.
It does not run the old interpreter inside a free `pure` and attach a final
annotation. Callee computations execute through the charged bind. Local
expression primitives pay the same explicit syntax-derived instruction/access
prices as the existing operational model.

The six currencies retain instruction/access work and the five packet counts
separately. Allocation counts are Box-creation counts; the currencies are not
summed into a hardware-time or allocator-time result. `charge` uses arlib's
existing `Charged.opMany`; bind and cost addition come from arlib. No new
resource monad, RAM, or generic verification framework is introduced.

All names below have prefix `ArlibSpike.SourceExecution`:

- `action_observe`: exact value and six-currency correspondence for an action
  under exact callee correspondence.
- `execute_observe`: exact correspondence for every generated syntax tree,
  including selected-arm returns and common continuations.
- `run_observe`: exact correspondence for every body map, function, input list
  and fuel. Its successful observation equals the original operational run,
  including the complete cost. This is stronger than value-only erasure.
- `source_run_agrees`: a successful operational run has the same charged result
  and every charged currency equals its operational counterpart.
- `program_spec`: transfers the existing syntax-proved instruction envelope.
- `lookup_spec`, `compare_spec`, `copy_spec`, `copyResult_spec`: the same
  first-hit/equality/copy values and complete packet vectors as the native pilot,
  plus the same `256 * events.units` modeled instruction envelope.
- `extra_compare_violates_old_budget`: interpreting the actual compiled source
  mutant returns `None` on empty input and records one comparison, violating
  the old zero-comparison budget.

Lookup permits arbitrary duplicate keys and returns the first hit. Cache
soundness is unnecessary for this exact packet contract: an oversized cached
witness remains in the actual copy count. Empty input, miss, first/last hits,
duplicate first hit, skipped right comparisons, early head mismatch, structural
equality, and oversized witness cases from `Tests/LookupSource.lean` transfer
through the universal correspondence theorem, without changing the input domain.
The comparison function is the same actual recursive scan as in the native leg.

## Reproduce and review

After configuring VM caches, from the repository root:

```bash
cd proofs/experiments/arlib_cost
lake build
lake env lean ArlibSpike/SourceExecution.lean
```

The complete optional build passes **3,781 jobs** under Lean 4.35.0 and arlib
`8d08f89a6d05c5e8368e91659bd6e117fbb74c4e`. All main dependency revisions remain
exactly equal to the main manifest. Eight printed endpoint axiom closures are
within `propext`, `Classical.choice`, `Quot.sound`; the general action, syntax
and fuel correspondence proofs need only `propext` and `Quot.sound`. The new
module has no linter warnings. Existing upstream legacy/deprecation warnings
are retained.

The fresh Mathlib fetch failed with `fetch-pack: invalid index-pack output`.
For this execution, each shared dependency's committed revision was compared
with the experiment manifest, then its existing ext4 checkout/build cache was
bind-mounted individually into the experiment. Both manifests remain unchanged.
Ordinary installations can fetch their own exact-pinned caches. These local
dependency mounts must also be removed before unmounting the experiment cache.
The local build log is `/var/tmp/subtree-arlib-pilot-build.log`.

Manual program review confirms that the interpreter definitions do not inspect
`Charged.val`, `Charged.cost`, decoded tallies, or the independent lookup answer.
`observe` is specification-only and noncomputable. All source calls compose
through the charged monad; local action and branch weights are charged explicitly.

## Preserved boundaries and next comparison

This is an exact **charged interpretation of the existing source-operation
model**, not an `ExactRealizes` theorem for arlib's RAM. No sealed RAM
representation, source-to-RAM compilation or memory-realization proof is claimed.
The raw expression primitives and immutable-reference snapshots retain the
original model's boundary. The Python reifier and its LLBC relationship remain
trusted. Structural source comparison and copy are traversed; native interpreter
execution time, heap aliasing, Rust field typing, allocator behavior, physical
space and stack exhaustion remain outside the conclusion.

Failure returns `none`; the charged computation can retain work before failure,
but the observation theorem erases that failing-run tally because the original
operational interpreter has no failure-cost result. All four public contracts
prove successful execution on represented inputs under explicit sufficient-fuel
premises. No unsupported-error runtime theorem follows. Space profiles are
neutral in this experiment; allocation *counts* are not occupancy proofs.

The native WP and charged arlib pilots now share computation, domain, result
specification, packet vector, instruction model and source mutation. Their C2
contracts are comparable. The Lax62 timed/IR pilot and the final semantic-boundary
decision remain W03 work. A future RAM realization must supply the representation
and primitive obligations; this charged correspondence cannot replace them.
