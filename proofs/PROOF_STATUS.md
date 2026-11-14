# Proof status (new development)

All new Lean modules are original to the fresh development. The snapshot
used for this overlay has neither `lean` nor `lake`, and network installation
was unavailable. **Source authored; build and kernel acceptance not yet
checked.** Do not represent the statements below as machine-checked until
`lake build` succeeds in a clean installation.

| Declaration or deliverable | Status in this overlay |
| --- | --- |
| `OrderedTree`, `edgeCount`, `leafCount` | Authored, unbuilt |
| `ContractStep` at root and any depth | Authored, unbuilt |
| `Embeds`, `CommonEmbedding`, `IsMaximumCommon` | Authored, unbuilt |
| `ContractStep.edgeCount_decreases` | Proof term authored, unbuilt |
| `embeds_edgeCount_le` | Proof term authored, unbuilt |
| `isMaximumCommon_self` | Proof term authored, unbuilt |
| `encodeDyck` using Mathlib `DyckWord` | Authored, unbuilt |
| `encodeDyck_semilength` | Proof term authored, unbuilt |
| Forest/tree encoding bijection | Open |
| Contraction/sequence-containment equivalence | Open |
| Lozano-Valiente recurrence and optimum | Open |
| Leaf-sensitive decomposition cardinality theorem | Open |
| Executable contraction oracle | Open |
| Aeneas Rust translation/refinement | Open |

Build from `proofs/`:

```bash
lake update
lake exe cache get
lake build
```

After successful build, record dependency versions in `lake-manifest.json`
and audit the theorem dependencies with `#print axioms` on the accepted public
theorems. Do not introduce local axioms or placeholder proofs.
