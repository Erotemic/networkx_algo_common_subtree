# Lozano-Valiente proof status

The pre-existing `OrderedTree.lean` and `BalancedSequence.lean` foundation was
reported to compile with Lean 4.35.0 / Mathlib `v4.35.0` after the earlier
constructor-resolution fix. Its accepted mathematical semantics remain under
review against the original paper.

## Next development: encoding and one-way contraction correspondence

The new files below have been authored as a single additive increment. **They
have not yet been compiled in this execution environment**. Their proof status
must be upgraded only after the maintainer runs `lake build` successfully.

| File and theorem | Status | Claim |
| --- | --- | --- |
| `EncodingEquivalence.toBinaryForest_fromBinaryForest` | Authored; build pending | Binary forest round trip |
| `EncodingEquivalence.fromBinaryTree_toBinaryTree` | Authored; build pending | Ordered tree round trip |
| `EncodingEquivalence.fromBinaryForest_toBinaryForest` | Authored; build pending | Ordered forest round trip |
| `EncodingEquivalence.encodeDyck_eq_ofTree_toBinaryTree` | Authored; build pending | Existing recursive encoding agrees with Mathlib's binary encoding |
| `EncodingEquivalence.decodeDyck_encodeDyck` | Authored; build pending | Decode after encode returns the original tree |
| `EncodingEquivalence.encodeDyck_decodeDyck` | Authored; build pending | Encode after decode returns the original word |
| `EncodingEquivalence.orderedTreeEquivDyck` | Authored; build pending | Bijection of rooted ordered trees and Dyck words |
| `EncodingEquivalence.edgeCount_decodeDyck` | Authored; build pending | Decode preserves semilength as edge count |
| `ContractionSoundness.encodeDyck_context_plug` | Authored; build pending | Tree context and balanced-word context substitution agree |
| `ContractionSoundness.contractStep_encodeDyck` | Authored; build pending | One tree edge contraction removes a matching Dyck pair |
| `ContractionSoundness.embeds_encodeDyck` | Authored; build pending | Every tree contraction sequence gives a sequence contraction |
| Dyck contraction => tree contraction | Open | Completeness direction |
| Full paper-specific balanced containment equivalence | Open | Establish and compare exact containment conventions |
| DP optimality and witness correctness | Open | Compare against independent tree optimum |
| Actual-leaf-sensitive complexity theorem | Open | Prove corrected combinatorial bound and cost model |
| Rust/Aeneas refinement | Open | Verified executable source |

No `sorry`, `admit`, or new `axiom` is used in the authored files. That textual
check is not a substitute for the Lean kernel's acceptance of the proofs.

## Local verification

```bash
cd proofs
lake build
```

After a successful build, audit the public theorems:

```bash
cat > /tmp/lozano-axioms.lean <<'LEAN'
import SubtreeProofs.Paper2004.ContractionSoundness
#print axioms SubtreeProofs.Paper2004.OrderedTree.decodeDyck_encodeDyck
#print axioms SubtreeProofs.Paper2004.OrderedTree.encodeDyck_decodeDyck
#print axioms SubtreeProofs.Paper2004.OrderedTree.contractStep_encodeDyck
#print axioms SubtreeProofs.Paper2004.OrderedTree.embeds_encodeDyck
LEAN
lake env lean /tmp/lozano-axioms.lean
```

Record the exact build result and axiom report before treating this increment
as verified. The inverse contraction theorem is the next mathematical target.
