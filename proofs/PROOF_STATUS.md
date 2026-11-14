# Proof status (new development)

The user's local `cd proofs && lake build` is **reported to pass** after the
constructor-elaboration correction to `OrderedTree.lean`. Earlier failed builds
are superseded. The exact successful log, a fresh-checkout build, and
`#print axioms` output have not yet been captured here. These are provenance
and assurance follow-ups, not known compilation blockers.

The reported build covers the fresh Lean source on the project's pinned
Lean 4.35.0 / Mathlib version. Compilation checks elaborated definitions and
theorem terms as stated; it does not establish their agreement with the 2004
paper or verify the Rust algorithms.

| Declaration or deliverable | Status |
| --- | --- |
| `OrderedTree`, `edgeCount`, `leafCount` | Compiled in reported local build |
| `Context`, `Context.plug`, `ContractStep` | Compiled in reported local build |
| `Embeds`, `CommonEmbedding`, `IsMaximumCommon` | Compiled in reported local build; paper-level contraction convention still to establish |
| `ContractStep.edgeCount_decreases` | Lean theorem accepted in reported local build; axiom audit pending |
| `embeds_edgeCount_le` | Lean theorem accepted in reported local build; axiom audit pending |
| `isMaximumCommon_self` | Lean theorem accepted in reported local build; axiom audit pending |
| `encodeDyck` using Mathlib `DyckWord` | Compiled in reported local build |
| `encodeDyck_semilength` | Lean theorem accepted in reported local build; axiom audit pending |
| Tree/forest encoding bijection | Open |
| Contraction/sequence-containment equivalence | Open |
| Lozano-Valiente recurrence and independent optimum | Open |
| Actual-leaf-sensitive decomposition cardinality theorem | Open |
| Executable contraction oracle | Open |
| Aeneas Rust translation/refinement | Open |

## Next checks

From `proofs/`:

```bash
lake build
```

Preserve and commit the generated `lake-manifest.json` when appropriate, and
reproduce the build from a fresh checkout in CI. Audit theorem dependencies
using `#print axioms` on accepted public theorems, and record exact compiler
output and dependency revisions. Continue with independent small-tree
contraction tests and the mathematical tree/Dyck-word correspondence.

The passing foundation build closes the initial compilation blocker; it does
not close the paper's correctness and complexity proof obligations.
