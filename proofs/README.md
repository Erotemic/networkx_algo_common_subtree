# subtree_proofs

NOTE: This is an WORK IN PROGRESS experiment to see how hard it is to get a
formalization of these proofs. Seems kinda hard for some cases. It is NOT
COMPLETE.

Lean workspace for formalization experiments around ordered-tree common-subtree results.

## Layout

- `SubtreeProofs/Lib/`
  - Reusable helper lemmas that are not specific to one proof attempt.
  - Current seed module: `SubtreeProofs/Lib/NatIneq.lean`.
- `SubtreeProofs/RuntimeUtils.lean`
  - Backward-compatible shim re-exporting generic helpers for older files.
- `SubtreeProofs/Lozano-v3.lean` ... `SubtreeProofs/Lozano-v6.lean`
  - Historical and current proof attempts, kept for reference.
- `SubtreeProofs/LozanoValiente2004*.lean`
  - Earlier companion developments.

## Goal for `Lib`

Keep `Lib` lemmas written in a style that is easy to upstream to mathlib:
- neutral namespaces
- no dependency on paper-specific datatypes
- concise statements with reusable proof patterns
