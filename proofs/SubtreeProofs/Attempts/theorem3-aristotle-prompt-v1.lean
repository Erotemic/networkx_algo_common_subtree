/-
GOAL (missing proof piece):
  Prove the tree-leaf analogue of Lemma 7 needed to make Theorem 3 unconditional.

Context:
  BSeq is the inductive datatype of balanced sequences from Lozano–Valiente 2004.
  S : BSeq → Finset BSeq is the paper’s auxiliary family used to bound |D[x]|.
  semilen x = |x| is the number of annotation pairs (edges).
  treeLeavesOfSeq is the *actual tree leaf count* for the tree encoded by x, as opposed
  to the Section-2 helper leaves recurrence ℓ(λ)=1, ℓ(0x1y)=ℓ(x)+ℓ(y).

Hard part:
  forestLeavesOfSeq nil = 0 breaks the paper proof’s “both parts ≥ 1” pattern,
  so we likely need a careful case split on the tail y=nil vs y≠nil.

TASK FOR ARISTOTLE:
  1) Try to prove the target theorem `lemma7_tree` below.
  2) If the exact statement is false, produce a counterexample and propose the smallest
     slack version that still implies the same Big-O for Theorem 3 (constant-factor/additive slack is OK).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic  -- for omega/linarith/etc

namespace Lozano

/-- Balanced sequences: `cons x y` represents `0 x 1 y`. -/
inductive BSeq : Type
  | nil : BSeq
  | cons : BSeq → BSeq → BSeq
deriving DecidableEq, Repr

namespace BSeq

/-- Concatenation (siblings concatenate). -/
def append : BSeq → BSeq → BSeq
  | nil,      t => t
  | cons x y, t => cons x (append y t)

instance : HAdd BSeq BSeq BSeq := ⟨append⟩

/-- semilength / number of edges `|x|`. -/
def semilen : BSeq → Nat
  | nil      => 0
  | cons x y => semilen x + semilen y + 1

@[simp] theorem semilen_nil : semilen nil = 0 := rfl
@[simp] theorem semilen_cons (x y : BSeq) :
    semilen (cons x y) = semilen x + semilen y + 1 := rfl

end BSeq

open BSeq

/-
Tree/forest leaf counts induced by the encoding-view split:
  nil is a tree leaf (treeLeaves=1) but an empty forest (forestLeaves=0).
  cons corresponds to "tree head + forest tail".
-/
def leavesPairOfSeq : BSeq → Nat × Nat
  | BSeq.nil => (1, 0)
  | BSeq.cons x y =>
      let px := leavesPairOfSeq x
      let py := leavesPairOfSeq y
      (px.1 + py.2, px.1 + py.2)

def treeLeavesOfSeq (s : BSeq) : Nat := (leavesPairOfSeq s).1
def forestLeavesOfSeq (s : BSeq) : Nat := (leavesPairOfSeq s).2

@[simp] theorem treeLeaves_nil : treeLeavesOfSeq BSeq.nil = 1 := by rfl
@[simp] theorem forestLeaves_nil : forestLeavesOfSeq BSeq.nil = 0 := by rfl

/-- Useful rewrite for cons. -/
@[simp] theorem treeLeaves_cons (x y : BSeq) :
    treeLeavesOfSeq (BSeq.cons x y) = treeLeavesOfSeq x + forestLeavesOfSeq y := by
  simp [treeLeavesOfSeq, forestLeavesOfSeq, leavesPairOfSeq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem forestLeaves_cons (x y : BSeq) :
    forestLeavesOfSeq (BSeq.cons x y) = treeLeavesOfSeq (BSeq.cons x y) := by
  simp [treeLeavesOfSeq, forestLeavesOfSeq, leavesPairOfSeq]

/-
We treat the rest of the development as axioms (already proved in our codebase),
to let Aristotle focus on the missing lemma proof.

R and S are the paper’s auxiliary families:
  R[λ]={λ}, R[0x1y]={0x1y} ∪ R[xy]
  S[λ]={λ}, S[0x1y]=R[x] ∪ S[xy]
and Lemma 5: S[xy] ⊆ S[x] ∪ S[y].

We only need: (1) a cardinal bound for R, and (2) the Lemma 5 inclusion, packaged
into a simple 3-set cardinal inequality for S(cons x y).
-/
constant R : BSeq → Finset BSeq
constant S : BSeq → Finset BSeq

/-- Fact 2 (paper): |R[x]| = |x| + 1. (If you only have ≤, you can weaken this axiom.) -/
axiom R_card : ∀ x : BSeq, (R x).card = BSeq.semilen x + 1

/-- Lemma 5 (paper): S(x+y) ⊆ S(x) ∪ S(y). -/
axiom lemma5 : ∀ x y : BSeq, (S (x + y) : Set BSeq) ⊆ (S x ∪ S y : Finset BSeq)

/-- The definitional recurrence for S (paper): S(cons x y) = R(x) ∪ S(x+y). -/
axiom S_cons_def : ∀ x y : BSeq, S (BSeq.cons x y) = R x ∪ S (x + y)

/--
Convenience bound derived from S_cons_def + lemma5 + card(union) ≤ sum(card):
You can assume this directly to avoid Finset boilerplate in the main proof.
-/
axiom S_cons_card_le (x y : BSeq) :
  (S (BSeq.cons x y)).card ≤ (R x).card + (S x).card + (S y).card

/-- Tree leaves are positive. -/
axiom treeLeaves_pos : ∀ x : BSeq, 1 ≤ treeLeavesOfSeq x

/-
TARGET (missing piece):
Tree-leaf analogue of Lemma 7:
  |S[x]| ≤ |x| * treeLeaves(x) + 1
where |x| = semilen x.
-/
theorem lemma7_tree (x : BSeq) :
    (S x).card ≤ BSeq.semilen x * treeLeavesOfSeq x + 1 := by
  -- Aristotle: fill this proof.
  -- Hint: structural induction on x; in cons-case do `cases y` to separate y=nil vs y=cons _ _.
  -- Use S_cons_card_le, R_card, IHs, and simp on semilen/treeLeaves/forestLeaves.
  sorry

/-
If lemma7_tree is false:
  (a) give a concrete counterexample, and
  (b) propose the smallest slack variant that still implies the same Big-O for Theorem 3, e.g.
      (S x).card ≤ semilen x * (treeLeavesOfSeq x + 1) + 1
   or constant-factor slack C * semilen x * treeLeavesOfSeq x + C'.
-/

end Lozano
