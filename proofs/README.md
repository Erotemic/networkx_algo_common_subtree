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
- `Paper2004/ContractionCompleteness.lean`: forest decoding and its
  concatenation/nesting lemmas; lifting of Dyck-context deletions to tree-edge
  contractions; the two-way equivalence `embeds_iff_dyckEmbeds`.

The maintainer reports a successful local `lake build` for the first four
modules, including the encoding equivalence and forward contraction theorem.
`ContractionCompleteness.lean` is **authored but not yet compiled** in this
execution environment. Its new proof claims depend on a successful local build.

The contraction equivalence covers the explicitly defined `DyckEmbeds`
relation. Reconciling that relation with the exact paper containment
conventions, then proving the dynamic program, complexity bound and Rust
refinement, remain later milestones. See `PROOF_STATUS.md` and `docs/planning`.
This workspace does not import the historical v3-v6 proofs.

```bash
cd proofs
lake build
```

Only mark the new theorems as accepted after the above passes. No binary
assets or generated build products belong in the documentation overlay.
