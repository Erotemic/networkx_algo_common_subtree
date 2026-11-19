module

public import SubtreeProofs.Paper2004.AffinityIsomorphismDP
public import Std.Data.HashMap.Lemmas
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

/-! Executable exact-rational memoization of the independent ordered-isomorphism
recurrences. Proof fields are erased by Lean's compiler. Keys retain complete
original-identity forests, so hash collisions cannot alias distinct queries. -/

@[expose] public section

namespace SubtreeProofs.Paper2004.AnnotatedIso.RationalSolver

deriving instance Hashable for BinaryTree

abbrev Input := Word Nat
abbrev Witness := Word (Nat × Nat)
abbrev Key := Bool × Input × Input

instance : BEq Input := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq Input where
  eq_of_beq h := of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl

def reference (affinity : Nat → Nat → ℚ) (any : Bool) (left right : Input) : Witness :=
  if any then AffinityDP.anywhere affinity left right else AffinityDP.level affinity left right

structure Cache (affinity : Nat → Nat → ℚ) where
  entries : Std.HashMap Key Witness
  sound : ∀ any left right output, entries[(any,left,right)]? = some output →
    output = reference affinity any left right

def Cache.empty (affinity : Nat → Nat → ℚ) : Cache affinity :=
  ⟨∅, by intros; simp_all⟩

def Cache.store {affinity : Nat → Nat → ℚ} (cache : Cache affinity)
    (any : Bool) (left right : Input) (output : Witness)
    (h : output = reference affinity any left right) : Cache affinity :=
  ⟨cache.entries.insert (any,left,right) output, by
    intro mode l r value hLookup
    rw [Std.HashMap.getElem?_insert] at hLookup
    split at hLookup
    · rename_i hKey
      have hKeys : (any,left,right) = (mode,l,r) := by simpa using hKey
      cases hKeys
      cases Option.some.inj hLookup
      exact h
    · exact cache.sound mode l r value hLookup⟩

abbrev Certified (affinity : Nat → Nat → ℚ) (any : Bool) (left right : Input) :=
  { output : Witness // output = reference affinity any left right }

/-- The executable memoized algorithm carries only erased correctness evidence.
There is no assumed input cache or supplied optimum certificate at the public API. -/
def run (affinity : Nat → Nat → ℚ) (any : Bool) (left right : Input)
    (cache : Cache affinity) : Certified affinity any left right × Cache affinity :=
  match hLookup : cache.entries[(any,left,right)]? with
  | some output => (⟨output, cache.sound any left right output hLookup⟩,cache)
  | none =>
    let computed : Certified affinity any left right × Cache affinity :=
      match left, right with
      | .nil, _ => (⟨.nil, by cases any <;> simp [reference, AffinityDP.level, AffinityDP.anywhere]⟩,cache)
      | .node _ _ _, .nil => (⟨.nil, by cases any <;> simp [reference, AffinityDP.level, AffinityDP.anywhere]⟩,cache)
      | .node a lh lt, .node b rh rt =>
        if hAny : any then
          let (x,c1) := run affinity true lh (.node b rh rt) cache
          let (y,c2) := run affinity true lt (.node b rh rt) c1
          let (z,c3) := run affinity true (.node a lh lt) rh c2
          let (w,c4) := run affinity true (.node a lh lt) rt c3
          let (lvl,c5) := run affinity false (.node a lh lt) (.node b rh rt) c4
          let output := AffinityDP.choose affinity lvl.val
            (AffinityDP.choose affinity (AffinityDP.choose affinity x.val y.val)
              (AffinityDP.choose affinity z.val w.val))
          (⟨output, by
            simp only [output, x.property, y.property, z.property, w.property, lvl.property,
              reference, hAny, Bool.false_eq_true, ↓reduceIte, AffinityDP.anywhere]⟩,c5)
        else
          let (x,c1) := run affinity false (.node a lh lt) rt cache
          let (y,c2) := run affinity false lt (.node b rh rt) c1
          let base := AffinityDP.choose affinity x.val y.val
          if hPositive : 0 < affinity a b then
            let (head,c3) := run affinity false lh rh c2
            let (tail,c4) := run affinity false lt rt c3
            let output := AffinityDP.choose affinity base (.node (a,b) head.val tail.val)
            (⟨output, by
              simp only [output, base, x.property, y.property, head.property, tail.property,
                reference, hAny, Bool.false_eq_true, ↓reduceIte, AffinityDP.level, hPositive]⟩,c4)
          else
            (⟨base, by
              simp only [base, x.property, y.property, reference, hAny, Bool.false_eq_true,
                ↓reduceIte, AffinityDP.level, hPositive]⟩,c2)
    (computed.1, computed.2.store any left right computed.1.val computed.1.property)
termination_by (left.numNodes + right.numNodes, if any then 1 else 0)
decreasing_by all_goals simp_all [BinaryTree.numNodes]; omega

def solve (affinity : Nat → Nat → ℚ) (rooted : Bool) (left right : Input) : Witness :=
  (run affinity (!rooted) left right (Cache.empty affinity)).1.val

theorem solve_eq (affinity : Nat → Nat → ℚ) (rooted : Bool) (left right : Input) :
    solve affinity rooted left right =
      if rooted then AffinityDP.level affinity left right else AffinityDP.anywhere affinity left right := by
  have h := (run affinity (!rooted) left right (Cache.empty affinity)).1.property
  cases rooted <;> exact h

/-- The compiled solver returns an independently feasible, globally maximum
original-identity witness for either root policy, for every rational affinity. -/
theorem solve_correct (affinity : Nat → Nat → ℚ) (rooted : Bool) (left right : Input) :
    if rooted then IsMaximumLevel affinity (solve affinity rooted left right) left right
    else IsMaximumAny affinity (solve affinity rooted left right) left right := by
  rw [solve_eq]
  cases rooted
  · exact AffinityDP.anywhere_correct affinity left right
  · exact AffinityDP.level_correct affinity left right

def solveResult (affinity : Nat → Nat → ℚ) (rooted : Bool) (left right : Input) : Witness × ℚ :=
  let witness := solve affinity rooted left right
  (witness, score affinity witness)

/-- Complete exact score, original-order and independent optimum contract of
the function called by the native executable. No cache invariant is a premise. -/
theorem solveResult_correct (affinity : Nat → Nat → ℚ) (rooted : Bool) (left right : Input) :
    let result := solveResult affinity rooted left right
    (if rooted then IsMaximumLevel affinity result.1 left right
      else IsMaximumAny affinity result.1 left right) ∧
    result.2 = score affinity result.1 ∧
    ((vertices result.1).map Prod.fst).Sublist (vertices left) ∧
    ((vertices result.1).map Prod.snd).Sublist (vertices right) := by
  have h := solve_correct affinity rooted left right
  have hAny : AnyWitness affinity (solve affinity rooted left right) left right := by
    cases rooted
    · exact h.1
    · exact h.1.any
  exact ⟨h, rfl, hAny.original_order⟩

theorem solve_unique_endpoints (affinity : Nat → Nat → ℚ) (rooted : Bool) (left right : Input)
    (hLeft : (vertices left).Nodup) (hRight : (vertices right).Nodup) :
    ((vertices (solve affinity rooted left right)).map Prod.fst).Nodup ∧
    ((vertices (solve affinity rooted left right)).map Prod.snd).Nodup := by
  have h := solve_correct affinity rooted left right
  apply AnyWitness.unique_endpoints (affinity := affinity) (left := left) (right := right) _ hLeft hRight
  cases rooted
  · exact h.1
  · exact h.1.any

end SubtreeProofs.Paper2004.AnnotatedIso.RationalSolver
