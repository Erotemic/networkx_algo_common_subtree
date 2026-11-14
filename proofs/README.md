# Lozano-Valiente 2004: fresh formalization

This is the new Lean 4 development for maximum common embedded subtrees of
finite, rooted, **ordered** trees, with the historical proof attempts excluded.
The plan is in `../docs/planning/lozano_valiente_2004_verified_rust_lean.md`.

The first definitions in `SubtreeProofs/Paper2004/OrderedTree.lean` model
ordered children and operational edge contraction at arbitrary depth, with
a fixed root and splicing at the contracted edge. `Embeds` is the reflexive
transitive closure of that operation. `IsMaximumCommon` is defined directly
on trees and scores edges. The specification never refers to balanced
sequences or a dynamic program.

`SubtreeProofs/Paper2004/BalancedSequence.lean` uses Mathlib's `DyckWord`
for the standard balanced-sequence encoding and the relationship between
semilength and edge count. The full contraction/sequence correspondence is
the next mathematical proof milestone.

Pinned dependency target: Lean 4.35.0 / Mathlib `v4.35.0`, a stable release.
A lockfile has not yet been generated. The source was authored in an environment
without Lean/Lake and requires its first compilation pass. See
`PROOF_STATUS.md` for precise verification state.

```bash
cd proofs
lake update
lake exe cache get
lake build
```

This work does not depend on TauCeti or Aeneas yet. Mathlib supplies Dyck
words, the relation closure, and elementary tactics. TauCeti and Aeneas will
be introduced only at boundaries where their features are required.
