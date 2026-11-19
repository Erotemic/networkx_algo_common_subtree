module

public import SubtreeProofs.Rust.SourceQueryLoanOrigins

/-! Moving an inline field retains its stack root. Complete bounded native
query loans and preserved original callers therefore discharge the physical
move guard without restricting aliases with owned data below that stack root. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem locatePath_inline_root {memory : Memory} {cell moved : Cell} {pointer target : Pointer}
    {path : List Projection} (inlinePath : Projection.deref ∉ path)
    (located : locatePath memory cell pointer path = some (moved, target)) : target.root = pointer.root := by
  induction path generalizing cell pointer with
  | nil => cases located; rfl
  | cons first rest ih =>
    have tail : Projection.deref ∉ rest := fun member => inlinePath (List.mem_cons_of_mem _ member)
    cases first with
    | deref => exact False.elim (inlinePath (by simp))
    | field variant index =>
      cases cell with
      | boolean _ | number _ | shared _ | owned _ => simp [locatePath] at located
      | node kind tag cells =>
        simp only [locatePath] at located
        split at located
        next allowed =>
          cases selected : cells[index]? with
          | none => simp only [selected, bind, Option.bind] at located; cases located
          | some child =>
            have next : locatePath memory child (pointer.field index) rest = some (moved, target) := by
              simpa only [selected, bind, Option.bind] using located
            exact (ih tail next).trans rfl
        next => cases located

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def InlinePlace : Place → Prop
  | .local _ => True
  | .field parent _ _ => InlinePlace parent
  | .deref _ => False

theorem InlinePlace.path {place : Place} (h : InlinePlace place) : Projection.deref ∉ (splitPlace place).2 := by
  induction place with
  | «local» _ => simp [splitPlace]
  | deref _ => cases h
  | field parent variant index ih =>
    simpa only [splitPlace, List.mem_append, List.mem_singleton, not_or, reduceCtorEq, not_false_eq_true, and_true] using ih h

theorem locate_inline_root {world : World} {roots : Roots} {place : Place} {moved : Cell} {target : Pointer}
    (inlinePlace : InlinePlace place) (located : Storage.locate world roots place = some (moved, target)) :
    ∃ binding, roots (splitPlace place).1 = some binding ∧ target.root = binding.address := by
  cases hb : roots (splitPlace place).1 with
  | none => simp only [Storage.locate, hb, bind, Option.bind] at located; cases located
  | some binding =>
    cases memory : world.memory[binding.address]? with
    | none => simp only [Storage.locate, hb, memory, bind, Option.bind] at located; cases located
    | some cell =>
      have route : locatePath world.memory cell ⟨binding.address, []⟩ (splitPlace place).2 = some (moved, target) := by
        simpa only [Storage.locate, hb, memory, bind, Option.bind] using located
      exact ⟨binding, rfl, locatePath_inline_root inlinePlace.path route⟩

def InlineOperand : Operand → Prop
  | .move place => InlinePlace place
  | _ => True

def InlineExpr : Expr → Prop
  | .use op => InlineOperand op
  | .address _ => True
  | .aggregate _ _ ops => ∀ op ∈ ops, InlineOperand op
  | .less left right => InlineOperand left ∧ InlineOperand right

theorem allowed_inline_from_query_origins {before world : World} {active : Activation} {callers : List Activation}
    {previous current suspended : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    (closed : ClosedOutside [1, 2] active.state) (queries : QueryOrigins world active before.memory.length)
    (scanned : Scanned world active current) (callerView : Callers world callers suspended)
    {op : Operand} (inlineOp : InlineOperand op) : Allowed world active.roots (current.loans ++ suspended.reads) op := by
  cases op with
  | copy _ | number _ | boolean _ => trivial
  | move place =>
    intro cell pointer located forbidden
    obtain ⟨binding, hb, same⟩ := locate_inline_root inlineOp located
    have fresh := h.fresh _ binding hb
    rw [same] at forbidden
    rcases List.mem_append.mp forbidden with currentLoan | oldRead
    · have bound := Inventory.loans_below_queries scanned.inventory closed queries binding.address currentLoan
      omega
    · have bound := h.previousCallers.preserved_read_bound h.beforeWellFormed h.kept callerView binding.address oldRead
      omega

end SubtreeProofs.Rust.SourceEval.Addressed
