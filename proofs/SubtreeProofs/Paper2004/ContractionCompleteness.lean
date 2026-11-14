module

public import SubtreeProofs.Paper2004.ContractionSoundness
public import SubtreeProofs.Paper2004.OrderedForest

/-!
# Completeness of ordered-tree contraction under Dyck encoding

The existing `ContractStep` and `DyckContractStep` relations are specified
independently. This file proves the reverse direction of the encoding bridge:
every matching-pair deletion in a Dyck context is an ordinary edge contraction
in the decoded ordered tree.

It is useful to work with forests because `DyckWord` encodes the children of
an implicit root. Deleting a pair from a forest either splices a child into its
parent's forest or contracts an edge strictly inside one child. Both are
realizable as tree contractions.

The equivalence here concerns the explicit `DyckContractStep` definition from
`ContractionSoundness`. Correspondence with all conventions in the 2004 paper
(e.g. label/annotation matching and the LCS containment relation) remains a
separate obligation.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004
namespace OrderedTree

/-- Decode a Dyck word as an ordered forest, without the implicit root. -/
def decodeForestDyck (word : DyckWord) : List OrderedTree :=
  fromBinaryForest word.toTree

/-- The forest encoding and decoding are right inverses. -/
@[simp] theorem encodeForestDyck_decodeForestDyck (word : DyckWord) :
    encodeForestDyck (decodeForestDyck word) = word := by
  unfold decodeForestDyck
  rw [encodeForestDyck_eq_ofTree_toBinaryForest,
    toBinaryForest_fromBinaryForest, DyckWord.ofTree_toTree]

/-- The forest encoding and decoding are left inverses. -/
@[simp] theorem decodeForestDyck_encodeForestDyck (forest : List OrderedTree) :
    decodeForestDyck (encodeForestDyck forest) = forest := by
  unfold decodeForestDyck
  rw [encodeForestDyck_eq_ofTree_toBinaryForest,
    DyckWord.toTree_ofTree, fromBinaryForest_toBinaryForest]

/-- Two forests with the same Dyck encoding are equal. -/
theorem encodeForestDyck_injective : Function.Injective encodeForestDyck := by
  intro first second h
  have hh := congrArg decodeForestDyck h
  simpa only [decodeForestDyck_encodeForestDyck] using hh

/-- Concatenation of balanced words corresponds to forest concatenation. -/
@[simp] theorem decodeForestDyck_add (first second : DyckWord) :
    decodeForestDyck (first + second) =
      decodeForestDyck first ++ decodeForestDyck second := by
  apply encodeForestDyck_injective
  simp only [encodeForestDyck_append, encodeForestDyck_decodeForestDyck]

/-- Nesting adds one tree around a decoded forest. -/
@[simp] theorem decodeForestDyck_nest (word : DyckWord) :
    decodeForestDyck word.nest =
      [OrderedTree.node (decodeForestDyck word)] := by
  apply encodeForestDyck_injective
  calc
    encodeForestDyck (decodeForestDyck word.nest) = word.nest := by
      rw [encodeForestDyck_decodeForestDyck]
    _ = encodeForestDyck [OrderedTree.node (decodeForestDyck word)] := by
      change word.nest =
        (encodeForestDyck (decodeForestDyck word)).nest + 0
      rw [encodeForestDyck_decodeForestDyck, add_zero]

/-- The ordinary tree decoder attaches a root to the decoded forest. -/
theorem decodeDyck_eq_node_decodeForestDyck (word : DyckWord) :
    decodeDyck word = OrderedTree.node (decodeForestDyck word) := rfl

/-- Removing an enclosing Dyck pair inside an arbitrary Dyck context becomes
one operational edge contraction in the decoded forest. -/
theorem dyckContext_decodeForest_contract (ctx : DyckContext)
    (interior : DyckWord) :
    ForestContractStep
      (decodeForestDyck (ctx.plug interior.nest))
      (decodeForestDyck (ctx.plug interior)) := by
  induction ctx with
  | hole =>
      simpa only [DyckContext.plug, decodeForestDyck_nest,
        List.nil_append, List.append_nil, children] using
        (ForestContractStep.splice [] []
          (.node (decodeForestDyck interior)))
  | siblings leftWords suffix inner ih =>
      simpa only [DyckContext.plug, decodeForestDyck_add] using
        (ForestContractStep.append_right (decodeForestDyck suffix)
          (ForestContractStep.append_left (decodeForestDyck leftWords) ih))
  | nested inner ih =>
      simpa only [DyckContext.plug, decodeForestDyck_nest] using ih.nest

/-- Completeness for one step: deleting a matching Dyck pair corresponds
to contracting a real edge in the decoded rooted, ordered tree. -/
theorem dyckContractStep_decodeDyck {before after : DyckWord}
    (step : DyckContractStep before after) :
    ContractStep (decodeDyck before) (decodeDyck after) := by
  rcases step with ⟨ctx, interior, hBefore, hAfter⟩
  rw [hBefore, hAfter]
  simpa only [decodeDyck_eq_node_decodeForestDyck] using
    (dyckContext_decodeForest_contract ctx interior).atRoot

/-- Completeness for any finite sequence of balanced-word contractions. -/
theorem dyckEmbeds_decodeDyck {small large : DyckWord}
    (h : DyckEmbeds small large) :
    Embeds (decodeDyck small) (decodeDyck large) := by
  unfold DyckEmbeds at h
  unfold Embeds
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprefix hstep ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (dyckContractStep_decodeDyck hstep))

/-- Main semantic correspondence: a tree is obtainable by edge contractions
if and only if its Dyck word is obtainable by matching-pair deletions. -/
theorem embeds_iff_dyckEmbeds {small large : OrderedTree} :
    Embeds small large ↔
      DyckEmbeds (encodeDyck small) (encodeDyck large) := by
  constructor
  · exact embeds_encodeDyck
  · intro h
    have decoded := dyckEmbeds_decodeDyck h
    simpa only [decodeDyck_encodeDyck] using decoded

/-- The same semantic correspondence, stated on arbitrary Dyck words. -/
theorem dyckEmbeds_iff_decodedEmbeds {small large : DyckWord} :
    DyckEmbeds small large ↔
      Embeds (decodeDyck small) (decodeDyck large) := by
  constructor
  · exact dyckEmbeds_decodeDyck
  · intro h
    have encoded := embeds_encodeDyck h
    simpa only [encodeDyck_decodeDyck] using encoded

end OrderedTree
end SubtreeProofs.Paper2004

end
