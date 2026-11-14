# Lozano-Valiente proof status

## Compiled development (maintainer-reported, before module conversion)

The maintainer confirmed that `lake build` succeeded with Lean 4.35.0 after
applying the `ContractionCompleteness.lean` overlay and the prior parser fixes.
All five mathematical modules passed a local build using the pre-migration
file format. A new `module`-system build is required after the migration
included with this overlay. Clean-checkout CI and the explicit axiom report
are still pending.

| Module / theorem | Status | Main result |
| --- | --- | --- |
| `OrderedTree` definitions and contraction lemmas | Compiled locally | Independent rooted, ordered, root-preserving edge-contraction relation |
| `BalancedSequence.encodeDyck_semilength` | Compiled locally | Dyck semilength counts tree edges |
| `EncodingEquivalence.decodeDyck_encodeDyck` | Compiled locally | Ordered tree decode/encode round trip |
| `EncodingEquivalence.encodeDyck_decodeDyck` | Compiled locally | Dyck word encode/decode round trip |
| `ContractionSoundness.contractStep_encodeDyck` | Compiled locally | Tree contraction induces pair deletion |
| `ContractionSoundness.embeds_encodeDyck` | Compiled locally | Soundness for contraction closure |

## Converse development (compiled locally before module conversion)

`ContractionCompleteness.lean` introduces a decoded forest and a one-step
forest contraction relation, then builds the converse and its consequences.
The maintainer reports that these proofs passed `lake build` before the
module-system migration. The migrated declarations are awaiting a fresh build.

| Theorem | Status | Claim |
| --- | --- | --- |
| `encodeForestDyck_decodeForestDyck` | Compiled before migration | Forest decode/encode right inverse |
| `decodeForestDyck_encodeForestDyck` | Compiled before migration | Forest decode/encode left inverse |
| `decodeForestDyck_add` | Compiled before migration | Dyck concatenation becomes forest concatenation |
| `decodeForestDyck_nest` | Compiled before migration | Dyck nesting becomes a single child |
| `ForestContractStep.atRoot` | Compiled before migration | Every forest contraction lifts to a rooted tree contraction |
| `dyckContext_decodeForest_contract` | Compiled before migration | Pair deletion under a Dyck context is a forest contraction |
| `dyckContractStep_decodeDyck` | Compiled before migration | Single-step completeness |
| `dyckEmbeds_decodeDyck` | Compiled before migration | Closure completeness |
| `embeds_iff_dyckEmbeds` | Compiled before migration | Full equivalence on ordered trees |
| `dyckEmbeds_iff_decodedEmbeds` | Compiled before migration | Full equivalence on arbitrary Dyck words |

## Beyond the bridge

| Target | Status |
| --- | --- |
| Agreement with every containment/annotation convention of the 2004 paper | Open |
| Independent small-tree contraction oracle | Open |
| Paper's DP recurrence and optimality/witness correctness | Open |
| True-leaf-sensitive combinatorial complexity result | Open |
| Rust/Aeneas translation and refinement | Open |

The module-system migration adds `module` headers, explicit `public import`
edges, and `@[expose] public section` to preserve exported declaration
visibility and definitional reduction while leaving theorem statements intact.
The proof-only `Mathlib.Tactic` import stays private. This first migration
pass uses exposed public sections; minimize exports and exposure only after
the compiled API has been checked. It also removes the reported `simpa` and
unused-simplifier-argument warnings.

The pre-migration project compiled. The migrated project is **build pending**.
Do not mark the module-system migration as verified until the commands below
succeed without errors or warnings.

## Local verification

```bash
cd proofs
lake build
lake env lean ModuleImportSmoke.lean
```

After a successful build, audit the public theorems:

```bash
cat > /tmp/lozano-axioms.lean <<'LEAN'
module

import SubtreeProofs.Paper2004.ContractionCompleteness
#print axioms SubtreeProofs.Paper2004.OrderedTree.decodeDyck_encodeDyck
#print axioms SubtreeProofs.Paper2004.OrderedTree.encodeDyck_decodeDyck
#print axioms SubtreeProofs.Paper2004.OrderedTree.contractStep_encodeDyck
#print axioms SubtreeProofs.Paper2004.OrderedTree.embeds_encodeDyck
#print axioms SubtreeProofs.Paper2004.OrderedTree.dyckContractStep_decodeDyck
#print axioms SubtreeProofs.Paper2004.OrderedTree.embeds_iff_dyckEmbeds
LEAN
lake env lean /tmp/lozano-axioms.lean
```

Record the module-system build result and axiom report before declaring this
migration complete. The next mathematical target is agreement with the paper's
exact containment relation and an independent tiny-tree contraction oracle.
