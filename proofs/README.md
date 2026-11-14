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
- `Paper2004/PaperContainment.lean`: literal recursive Definition 2,
  soundness relative to `DyckEmbeds`, concatenation and length lemmas.

The maintainer reported successful builds of the contraction correspondence
and accepted the module-system migration. The new `PaperContainment.lean`
module is proposed work awaiting its first local build; see
`PROOF_STATUS.md` for declaration-level status.

The contraction equivalence covers the explicitly defined `DyckEmbeds`
relation. `PaperContainment.lean` now also records the literal recursive
relation printed in Definition 2 and proves (subject to kernel verification)
that it implies `DyckEmbeds`. An independent checker detects a disagreement
in the reverse direction already at three edges. The paper's own Example 2
agrees with the operational deletion results. See
`docs/planning/lozano_valiente_2004_containment_definition_audit.md`.
The DP, complexity bound and Rust refinement remain future work. See `PROOF_STATUS.md` and `docs/planning`.
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

Independent finite comparison (Python 3 standard library only):

```bash
python3 proofs/checks/check_printed_containment.py
python3 proofs/checks/check_tree_contraction_oracle.py
```

This checker tests the printed recursive definition and the closure of
matched-pair deletions separately; it is not used to define either Lean
relation.

The second checker enumerates rooted ordered trees directly from child
forests, contracts edges by splicing children, and compares only the resulting
encodings with independent balanced-word pair deletion. All trees up to six
edges agree in the shipped executable check; the comparison has not been
formalized in Lean yet.
