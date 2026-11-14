# Lozano-Valiente (2004): modern Lean development

The development formalizes finite rooted ordered trees, edge contractions and
maximum common embedded subtrees independently of any algorithm. Its proofs
build on Lean 4.35.0 and Mathlib.

Modules in dependency order:

- `Paper2004/OrderedTree.lean`: ordered-tree and contraction-based problem specification.
- `Paper2004/BalancedSequence.lean`: recursive Dyck encoding and edge-count equation.
- `Paper2004/EncodingEquivalence.lean`: first-child/next-sibling binary-tree
  encoding, inverse decoding and two round-trip theorems. Reuses Mathlib's
  `DyckWord.ofTree_toTree` and `DyckWord.toTree_ofTree`.
- `Paper2004/ContractionSoundness.lean`: independent Dyck matching-pair deletion
  contexts and the forward map from operational tree contractions to sequence
  contractions.

The **reverse** sequence-to-tree contraction theorem is not yet proved.
The paper's dynamic program, complexity bound and Rust refinement are later
milestones; see `PROOF_STATUS.md` and the `docs/planning` roadmaps.

The previous two modules compiled in the maintainer's local environment. The
new round-trip and contraction modules are **authored, awaiting a `lake build`**.
This workspace does not import the historical v3-v6 proofs.

```bash
cd proofs
lake build
```

Only mark the new theorems as accepted after the above passes. No binary
assets or generated build products belong in the documentation overlay.
