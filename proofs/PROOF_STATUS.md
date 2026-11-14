# Lozano-Valiente proof status

## Compiled foundation (maintainer-reported)

The maintainer confirmed that `lake build` succeeded with Lean 4.35.0 after
applying the latest `EncodingEquivalence.lean` and `ContractionSoundness.lean`
parser fixes. Thus the ordered-tree foundation, balanced-sequence encoding,
encoding round trips and forward tree-to-Dyck contraction proofs have passed a
local build. Clean-checkout CI and the explicit axiom report are still pending.

| Module / theorem | Status | Main result |
| --- | --- | --- |
| `OrderedTree` definitions and contraction lemmas | Compiled locally | Independent rooted, ordered, root-preserving edge-contraction relation |
| `BalancedSequence.encodeDyck_semilength` | Compiled locally | Dyck semilength counts tree edges |
| `EncodingEquivalence.decodeDyck_encodeDyck` | Compiled locally | Ordered tree decode/encode round trip |
| `EncodingEquivalence.encodeDyck_decodeDyck` | Compiled locally | Dyck word encode/decode round trip |
| `ContractionSoundness.contractStep_encodeDyck` | Compiled locally | Tree contraction induces pair deletion |
| `ContractionSoundness.embeds_encodeDyck` | Compiled locally | Soundness for contraction closure |

## New converse development (awaiting local compilation)

`ContractionCompleteness.lean` is a new module in this overlay. It introduces
an independently decoded forest and a one-step forest contraction relation,
then builds the converse and its consequences. The following are **authored
proofs, not yet kernel-checked in this environment**.

| Theorem | Status | Claim |
| --- | --- | --- |
| `encodeForestDyck_decodeForestDyck` | Build pending | Forest decode/encode right inverse |
| `decodeForestDyck_encodeForestDyck` | Build pending | Forest decode/encode left inverse |
| `decodeForestDyck_add` | Build pending | Dyck concatenation becomes forest concatenation |
| `decodeForestDyck_nest` | Build pending | Dyck nesting becomes a single child |
| `ForestContractStep.atRoot` | Build pending | Every forest contraction lifts to a rooted tree contraction |
| `dyckContext_decodeForest_contract` | Build pending | Pair deletion under a Dyck context is a forest contraction |
| `dyckContractStep_decodeDyck` | Build pending | Single-step completeness |
| `dyckEmbeds_decodeDyck` | Build pending | Closure completeness |
| `embeds_iff_dyckEmbeds` | Build pending | Full equivalence on ordered trees |
| `dyckEmbeds_iff_decodedEmbeds` | Build pending | Full equivalence on arbitrary Dyck words |

## Beyond the bridge

| Target | Status |
| --- | --- |
| Agreement with every containment/annotation convention of the 2004 paper | Open |
| Independent small-tree contraction oracle | Open |
| Paper's DP recurrence and optimality/witness correctness | Open |
| True-leaf-sensitive combinatorial complexity result | Open |
| Rust/Aeneas translation and refinement | Open |

No `sorry`, `admit` or new `axiom` is intentionally used in the new module.
Successful compilation, rather than that source inspection, is the acceptance
criterion for its proof statements.

## Local verification

```bash
cd proofs
lake build
```

After a successful build, audit the public theorems:

```bash
cat > /tmp/lozano-axioms.lean <<'LEAN'
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

Record the build result and axiom report before treating the new converse
theorems as verified. The next mathematical target is agreement with the paper's
exact containment relation and an independent tiny-tree contraction oracle.
