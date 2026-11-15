# Source-proved production choice materialization

The actual integer reconstruction helper introduced with the optimized ordered
isomorphism backend now has a Lean source contract:
`Rust.IsomorphismChoices.reconstruct_isomorphism_choices_spec`.
It safely terminates and returns exactly the token labels/order specified by
the independent arena forest in both inputs. Its premises are valid earlier
head/tail references, a valid optional root, and an output token count bounded
by `Usize.max`. No source success, expected output, optimum or repair certificate
is supplied. Shared choices expand at every occurrence, matching the source.

The source loop preserves an output-prefix/remaining-forest invariant. Each
iteration emits one token per side and decreases remaining output length;
the pending-task bound discharges actual reads, vector writes/pushes and cursor
arithmetic. The forest definition is well founded on choice indices and does
not duplicate the imperative work-stack loop.

## Removing an extraction gap

The previous extraction at `028727a` represented `Vec::pop` as an unmodeled
external declaration. That helper was explicitly unproved then; its extraction
alone did not establish pop behavior. The actual Rust helper now keeps a logical
active prefix of reusable vector slots, using supported reads/writes/pushes.
`IsomorphismChoiceStack.push_visit_spec` proves exact active-prefix preservation
for overwrite and append, including stale inactive slots. Regeneration removes
that external dependency. No pop specification/axiom was added, no generated
file was hand-edited, and dependency pins remain fixed.

The weighted score DP and public Python API are unchanged. This theorem
preserves the supplied arena's token labels; the production DP's construction
of a feasible/optimal arena from the original input, its memo/score refinement,
Python conversions and complete runtime/allocation proofs remain open.
It does not prove those labels lie within arbitrary original inputs without
the corresponding caller invariant. IEEE-754 stays outside initial scope.

## Executed checks and short performance check

- **3,732 main Lean jobs** and both existing Lean example suites pass.
- Pinned Charon/Aeneas regeneration `--check` passes.
- All **13 ordered-core Rust tests** pass, including invalid references,
  nested head/tail order and iterative 4,096-deep materialization.
- A fresh Rust+Cython Release wheel passes **234 installed Python tests,
  zero skips**, with native parity mandatory. Existing independent objectives,
  original-index witness checks and fractional/tie/root-mode tests remain active.

Normal wheel SHA256:
`08a09caf24e4241cb8399988ce60cb2b79e4a3d08a9cf60317ee833872229d31`.
The [environment artifact](2026-11-14-iso-choice-stack-environment.json) records
the measured extension/source hashes and exact comparison ratios. Portable
wheel validation and a comprehensive performance campaign were not repeated.

Because the stack implementation changed, one small installed Rust check uses
the same ten size-8/16 inputs per mode as the preceding milestone, **three
samples and one warmup**, with no concurrent compiler/tests. The four
`2026-11-14-iso-choice-stack-{eq,weighted}-{general,rooted}.json` files retain
all samples. Every objective equals the preceding Python/Cython/Rust-parity
measurement. This check measures only the updated Rust backend; the installed
test suite separately requires all native backends.

| Mode | Prior / current Rust median |
| --- | ---: |
| Equality, general | 1.05× |
| Equality, rooted | 1.07× |
| Fractional, general | 0.98× |
| Fractional, rooted | 1.11× |

Per-case ratios range 0.73–1.89×. Treat this as a noisy small regression check,
not a new general speedup; no rerun was made to smooth variance. The preceding
[choice-arena optimization measurements](2026-11-14-ordered-iso-choices.md)
remain historical evidence for `028727a`, including its separate peak-RSS
observation. No new memory observation was made for the cursor implementation.

## Subsequent actual constructor source proof

The production DP now uses `append_isomorphism_choice` for its existing
old-length/read-and-push operation. Its actual source theorem derives stable
old reference meanings, exact arena growth and new forest assembly. Actual
append and materialization compose; conditional original-coordinate bounds
are proved through both stages. The score DP and its arithmetic/control
comparisons are unchanged. An independent abstract affinity fold supplies the
head + tail + root score equation and old-score stability, without an f64
refinement claim. Full production DP/memo/provenance, parent feasibility,
optimality and resource refinement remain open.

The updated fixture exercises real appends and checks an old witness after
further construction. **13 ordered-core**, **234 required-native installed
Python tests**, **3,735 main Lean jobs**, both example suites and pinned
regeneration `--check` pass. The environment artifact's `construction_update`
records the fresh normal-wheel/source hashes. No new performance/memory run or
portable build was performed; the timing tables above remain evidence for the
earlier cursor-stack milestone.
