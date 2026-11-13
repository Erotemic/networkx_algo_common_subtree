# Common subtree verification (fresh start)

This directory is reserved for the new Lean 4 formalization of Lozano and
Valiente (2004), and the proofs relating the new Rust implementation to its
mathematical specification through Charon/Aeneas.

The previous proof modules, experiments, runtime scaffolding and handoff notes
have been retired from the active tree. Their Git history remains available;
they are not imports or dependencies of the new proof development.

**Plan:** [`../docs/planning/lozano_valiente_2004_verified_rust_lean.md`](../docs/planning/lozano_valiente_2004_verified_rust_lean.md)

The initial proof workspace is deliberately empty. W0 will establish a
working pinned Lake/Mathlib configuration, and W1 will introduce independent
ordered-tree and edge-contraction definitions. Do not infer that the presence
of the existing `lean-toolchain` file certifies a working Lean build.

The accepted final development will contain no unproved local axioms, `sorry`
or `admit` in the critical proof chain. Generated Aeneas Lean is to be derived
reproducibly from the maintained Rust source, never repaired manually.
