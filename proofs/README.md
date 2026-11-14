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

The maintainer reports a successful Lean 4.35.0 `lake build` for all five
mathematical modules before the module-system conversion. This overlay migrates
all six library source files to the `module` system, preserves their public
exports and fixes the reported tactic warnings. The migrated build still needs
a local check; see `PROOF_STATUS.md` for the distinction.

The contraction equivalence covers the explicitly defined `DyckEmbeds`
relation. Reconciling that relation with the exact paper containment
conventions, then proving the dynamic program, complexity bound and Rust
refinement, remain later milestones. See `PROOF_STATUS.md` and `docs/planning`.
This workspace does not import the historical v3-v6 proofs.

```bash
cd proofs
lake build
lake env lean ModuleImportSmoke.lean
```

The smoke test imports only the umbrella `SubtreeProofs` module and checks
that key declarations remain accessible to downstream code. Report new module
errors or warnings before marking the migration complete. No binary
assets or generated build products belong in the documentation overlay.
