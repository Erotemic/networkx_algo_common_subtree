import Arlib.Computation.Queue
import Arlib.Computation.Dict
import Arlib.Computation.Std
import SubtreeProofs.Paper2004.MemoizedDynamicProgram
import Mathlib.Tactic

/-! An isolated experiment. Counts table pops and whole Dyck-key comparisons;
these comparisons are abstract operations, not constant-time RAM instructions.
Queue input encoding is an external boundary. No space/ownership claim is made.
-/
namespace ArlibSpike
open Arlib.Computation
open SubtreeProofs.Paper2004.OrderedTree

inductive LookupOp where
  | dequeue | enqueue | isEmpty | keyEq
  deriving DecidableEq

instance : Fintype LookupOp := Fintype.ofList
  [.dequeue, .enqueue, .isEmpty, .keyEq] (by intro o; cases o <;> simp)

instance lookupQueueOps : QueueOps LookupOp where
  charge
    | .dequeue => .dequeue
    | .enqueue => .enqueue
    | .isEmpty => .isEmpty
  charge_injective := by intro a b h; cases a <;> cases b <;> cases h <;> rfl

@[simp] theorem lookup_charge (o : QueueOp) :
    QueueOps.charge (κ := LookupOp) o = match o with
      | .dequeue => LookupOp.dequeue
      | .enqueue => LookupOp.enqueue
      | .isEmpty => LookupOp.isEmpty := by
  cases o <;> rfl

instance : QueueCells (MemoKey × Nat) Unit := ⟨()⟩

namespace Interface
/-- One abstract key comparison, as counted by the existing memoFind. The cost
of comparing the structural Dyck words themselves is a separate obligation. -/
def equalKey (a b : MemoKey) : Charged LookupOp Unit Bool :=
  Charged.op .keyEq (decide (a = b))
end Interface

namespace Program
/-- A charged scan over sealed table storage. Fuel is externally supplied;
there is no raw list, specification lookup, cost read or noncomputable view. -/
def find (fuel : Nat) (key : MemoKey) (table : Queue (MemoKey × Nat)) :
    Charged LookupOp Unit (Option Nat) :=
  match fuel with
  | 0 => pure none
  | fuel + 1 => do
    let (entry, rest) ← Queue.dequeue table
    match entry with
    | none => pure none
    | some (stored, value) =>
      let equal ← Interface.equalKey key stored
      if equal then pure (some value) else find fuel key rest
end Program

/-- Exact output equality with the repository's existing computation, including
arbitrary duplicate keys and early termination at the first match. -/
theorem find_value (key : MemoKey) (table : MemoTable) :
    (Program.find (table.length + 1) key (Queue.ofList table)).val = (memoFind key table).1 := by
  induction table with
  | nil => simp [Program.find, Queue.val_dequeue, memoLookup]
  | cons entry rest ih =>
    rcases entry with ⟨stored, value⟩
    by_cases he : key = stored
    · simp [Program.find, Queue.val_dequeue, Interface.equalKey, memoFind, he]
    · simpa [Program.find, Queue.val_dequeue, Interface.equalKey, memoFind, he] using ih

/-- Recorded comparison count equals the counter returned by actual memoFind. -/
theorem find_comparisons (key : MemoKey) (table : MemoTable) :
    (Program.find (table.length + 1) key (Queue.ofList table)).cost .keyEq = (memoFind key table).2 := by
  induction table with
  | nil => simp [Program.find, Queue.val_dequeue, Queue.cost_dequeue, queueOpcode, CostVec.one, memoFind]
  | cons entry rest ih =>
    rcases entry with ⟨stored, value⟩
    by_cases he : key = stored
    · simp [Program.find, Queue.val_dequeue, Queue.cost_dequeue, queueOpcode,
        Interface.equalKey, memoFind, he, CostVec.one]
    · simpa [Program.find, Queue.val_dequeue, Queue.cost_dequeue, queueOpcode,
        Interface.equalKey, memoFind, he, CostVec.one, Nat.add_comm] using ih

/-- The original table-length bound transfers to this operation-bearing program. -/
theorem find_comparisons_le (key : MemoKey) (table : MemoTable) :
    (Program.find (table.length + 1) key (Queue.ofList table)).cost .keyEq ≤ table.length := by
  rw [find_comparisons]
  exact memoFind_comparisons key table

/-- Exhaustion performs one final empty pop; a hit stops before it. -/
theorem find_pops_le (key : MemoKey) (table : MemoTable) :
    (Program.find (table.length + 1) key (Queue.ofList table)).cost .dequeue ≤ table.length + 1 := by
  induction table with
  | nil => simp [Program.find, Queue.val_dequeue, Queue.cost_dequeue, queueOpcode, CostVec.one]
  | cons entry rest ih =>
    rcases entry with ⟨stored, value⟩
    by_cases he : key = stored
    · simp [Program.find, Queue.val_dequeue, Queue.cost_dequeue, queueOpcode,
        Interface.equalKey, he, CostVec.one]
    · simpa [Program.find, Queue.val_dequeue, Queue.cost_dequeue, queueOpcode,
        Interface.equalKey, he, CostVec.one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using Nat.succ_le_succ ih

theorem find_unused_cost (key : MemoKey) (table : MemoTable) (o : LookupOp)
    (heq : o ≠ .keyEq) (hpop : o ≠ .dequeue) :
    (Program.find (table.length + 1) key (Queue.ofList table)).cost o = 0 := by
  induction table with
  | nil => simp [Program.find, Queue.val_dequeue, Queue.cost_dequeue, queueOpcode, CostVec.one, hpop]
  | cons entry rest ih =>
    rcases entry with ⟨stored, value⟩
    by_cases he : key = stored
    · simp [Program.find, Queue.val_dequeue, Queue.cost_dequeue, queueOpcode,
        Interface.equalKey, he, CostVec.one, heq, hpop]
    · simpa [Program.find, Queue.val_dequeue, Queue.cost_dequeue, queueOpcode,
        Interface.equalKey, he, CostVec.one, heq, hpop] using ih

/-- Nonvacuous bound on all operations recorded by the sealed scan. -/
theorem find_steps_le (key : MemoKey) (table : MemoTable) :
    Charged.steps (Rate.unit LookupOp)
      (Program.find (table.length + 1) key (Queue.ofList table)) ≤ 2 * table.length + 1 := by
  have hc := find_comparisons_le key table
  have hp := find_pops_le key table
  have he := find_unused_cost key table .enqueue (by decide) (by decide)
  have hi := find_unused_cost key table .isEmpty (by decide) (by decide)
  have hu : (Finset.univ : Finset LookupOp) = {.dequeue, .enqueue, .isEmpty, .keyEq} := by decide
  simp only [Charged.steps, CostVec.steps, Rate.unit_cost, one_mul]
  rw [hu]
  simp [he, hi]
  omega

/-- A first-entry hit performs exactly one key comparison and one pop,
regardless of the length of the unused suffix. -/
theorem find_hit (key : MemoKey) (value : Nat) (rest : MemoTable) :
    (Program.find (rest.length + 2) key (Queue.ofList ((key, value) :: rest))).val = some value ∧
    (Program.find (rest.length + 2) key (Queue.ofList ((key, value) :: rest))).cost .keyEq = 1 ∧
    (Program.find (rest.length + 2) key (Queue.ofList ((key, value) :: rest))).cost .dequeue = 1 := by
  simp [Program.find, Queue.val_dequeue, Queue.cost_dequeue, queueOpcode, Interface.equalKey, CostVec.one]

end ArlibSpike
