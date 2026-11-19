module

public import SubtreeProofs.Paper2004.EncodingEquivalence

/-!
# One-step contraction is sound under the Dyck encoding

The tree-side relation `ContractStep` was defined without any reference to
sequences. Here we define a separate, syntactic one-hole context for Dyck
words. Contracting a represented edge means removing its enclosing matching
pair while retaining the word inside that pair.

We prove that every operational tree contraction induces such a Dyck-word
contraction, including contractions below the root. The converse is a distinct
proof obligation; it is not assumed here.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004
namespace OrderedTree

/-- A Dyck-word context with exactly one balanced-word hole. Nested contexts
allow a matching pair to be removed at arbitrary depth. -/
inductive DyckContext where
  | hole : DyckContext
  | siblings (leftWords suffix : DyckWord) (inner : DyckContext) : DyckContext
  | nested (inner : DyckContext) : DyckContext

namespace DyckContext

/-- Replace the hole with a Dyck word. -/
def plug : DyckContext -> DyckWord -> DyckWord
  | .hole, word => word
  | .siblings leftWords suffix inner, word =>
      leftWords + (plug inner word) + suffix
  | .nested inner, word => (plug inner word).nest

/-- Insert one Dyck context into the hole of another. -/
def compose : DyckContext -> DyckContext -> DyckContext
  | .hole, inner => inner
  | .siblings leftWords suffix outer, inner =>
      .siblings leftWords suffix (compose outer inner)
  | .nested outer, inner => .nested (compose outer inner)

/-- Plugging into composed contexts is ordinary substitution. -/
theorem plug_compose (outer inner : DyckContext) (word : DyckWord) :
    (outer.compose inner).plug word = outer.plug (inner.plug word) := by
  induction outer with
  | hole => rfl
  | siblings leftWords suffix tail ih =>
      change leftWords + (tail.compose inner).plug word + suffix =
        leftWords + tail.plug (inner.plug word) + suffix
      rw [ih]
  | nested tail ih =>
      change ((tail.compose inner).plug word).nest =
        (tail.plug (inner.plug word)).nest
      rw [ih]

end DyckContext

/-- Delete one enclosing matching pair from a Dyck word, leaving the word
inside it in the same location. The context is explicitly restricted to
balanced concatenations and nested balanced words. -/
def DyckContractStep (before after : DyckWord) : Prop :=
  ∃ (ctx : DyckContext) (interior : DyckWord),
    before = ctx.plug (interior.nest) ∧ after = ctx.plug interior

/-- Sequence contraction closure, defined without reference to tree embeddings. -/
def DyckEmbeds (small large : DyckWord) : Prop :=
  Relation.ReflTransGen DyckContractStep large small

/-- Forest encoding respects concatenation. -/
theorem encodeForestDyck_append (first second : List OrderedTree) :
    encodeForestDyck (first ++ second) =
      encodeForestDyck first + encodeForestDyck second := by
  induction first with
  | nil => simp [encodeForestDyck]
  | cons child rest ih =>
      simp only [List.cons_append, encodeForestDyck]
      rw [ih]
      simp only [add_assoc]

/-- Encode a tree context as a balanced-word context. -/
def encodeTreeContext : Context -> DyckContext
  | .hole => .hole
  | .under left right inner =>
      .siblings (encodeForestDyck left) (encodeForestDyck right)
        (.nested (encodeTreeContext inner))

/-- Tree context substitution commutes with the Dyck-word encoding. -/
theorem encodeDyck_context_plug (ctx : Context) (tree : OrderedTree) :
    encodeDyck (ctx.plug tree) =
      (encodeTreeContext ctx).plug (encodeDyck tree) := by
  induction ctx with
  | hole => rfl
  | under left right inner ih =>
      simp only [Context.plug, encodeDyck, encodeTreeContext,
        DyckContext.plug, encodeForestDyck_append,
        encodeForestDyck, add_zero, ih, add_assoc]

/-- A single edge at the root contributes a matching pair around its child's
Dyck word, with the sibling forests on either side. -/
theorem encodeDyck_root_before (left right : List OrderedTree)
    (child : OrderedTree) :
    encodeDyck (.node (left ++ [child] ++ right)) =
      encodeForestDyck left + (encodeDyck child).nest +
        encodeForestDyck right := by
  simp [encodeDyck, encodeForestDyck_append, encodeForestDyck, add_assoc]

/-- Contracting that root edge splices the child's contents into the same
position, so the enclosing matching pair disappears. -/
theorem encodeDyck_root_after (left right : List OrderedTree)
    (child : OrderedTree) :
    encodeDyck (.node (left ++ children child ++ right)) =
      encodeForestDyck left + encodeDyck child +
        encodeForestDyck right := by
  cases child with
  | node grandchildren =>
      simp [encodeDyck, children, encodeForestDyck_append, add_assoc]

/-- Every operational tree contraction gives a valid matching-pair deletion in
the balanced-sequence representation. -/
theorem contractStep_encodeDyck {before after : OrderedTree}
    (step : ContractStep before after) :
    DyckContractStep (encodeDyck before) (encodeDyck after) := by
  rcases step with ⟨ctx, left, right, child, hBefore, hAfter⟩
  let rootCtx : DyckContext :=
    .siblings (encodeForestDyck left) (encodeForestDyck right) .hole
  refine ⟨(encodeTreeContext ctx).compose rootCtx, encodeDyck child, ?_, ?_⟩
  · calc
      encodeDyck before =
          (encodeTreeContext ctx).plug
            (encodeDyck (.node (left ++ [child] ++ right))) := by
              rw [hBefore, encodeDyck_context_plug]
      _ = (encodeTreeContext ctx).plug
            (rootCtx.plug ((encodeDyck child).nest)) := by
              rw [encodeDyck_root_before]
              rfl
      _ = ((encodeTreeContext ctx).compose rootCtx).plug
            ((encodeDyck child).nest) := by
              rw [DyckContext.plug_compose]
  · calc
      encodeDyck after =
          (encodeTreeContext ctx).plug
            (encodeDyck (.node (left ++ children child ++ right))) := by
              rw [hAfter, encodeDyck_context_plug]
      _ = (encodeTreeContext ctx).plug
            (rootCtx.plug (encodeDyck child)) := by
              rw [encodeDyck_root_after]
              rfl
      _ = ((encodeTreeContext ctx).compose rootCtx).plug
            (encodeDyck child) := by
              rw [DyckContext.plug_compose]

/-- Operational tree embeddings map to balanced-sequence contractions.
This is the soundness direction; completeness remains open. -/
theorem embeds_encodeDyck {small large : OrderedTree}
    (h : Embeds small large) :
    DyckEmbeds (encodeDyck small) (encodeDyck large) := by
  unfold Embeds at h
  unfold DyckEmbeds
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprefix hstep ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (contractStep_encodeDyck hstep))

end OrderedTree
end SubtreeProofs.Paper2004

end
