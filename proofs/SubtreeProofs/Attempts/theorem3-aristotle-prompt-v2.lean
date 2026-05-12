/-
ARISTOTLE TASK: Prove the missing tree-leaf analogue of Lemma 7.

IMPORTANT:
- The target theorem IS TRUE. Do NOT search for counterexamples.
- Do NOT introduce computational "R_comp"/"S_comp" or #eval checks.
- Work in the axiomatic context below (treat already-proved results as axioms).
- Focus on finding a clean proof, likely by strong induction on `semilen`.

High-level idea:
- For x = cons u v, split on v = nil vs v ≠ nil.
- v ≠ nil behaves like the paper proof using leaf additivity.
- v = nil is the degenerate case (forestLeaves nil = 0). Fix it using:
    card (R u \ S u) ≤ treeLeavesOfSeq u
  so that:
    card (S (cons u nil)) = card (R u ∪ S u) ≤ card (S u) + card (R u \ S u)
                         ≤ card (S u) + treeLeavesOfSeq u
  which matches the desired bound exactly.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open scoped Classical
open scoped Nat

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
Tree/forest leaves induced by encoding-view split:
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

@[simp] theorem treeLeaves_nil : treeLeavesOfSeq BSeq.nil = 1 := rfl
@[simp] theorem forestLeaves_nil : forestLeavesOfSeq BSeq.nil = 0 := rfl

@[simp] theorem treeLeaves_cons (x y : BSeq) :
    treeLeavesOfSeq (BSeq.cons x y) = treeLeavesOfSeq x + forestLeavesOfSeq y := by
  simp [treeLeavesOfSeq, forestLeavesOfSeq, leavesPairOfSeq,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem forestLeaves_cons (x y : BSeq) :
    forestLeavesOfSeq (BSeq.cons x y) = treeLeavesOfSeq (BSeq.cons x y) := by
  simp [treeLeavesOfSeq, forestLeavesOfSeq, leavesPairOfSeq]

/-
Already-proved helper facts (treat as axioms to save space/time).
These were found/used by prior attempts and are safe to assume here.
-/
axiom add_nil (x : BSeq) : x + BSeq.nil = x
axiom semilen_append (x y : BSeq) :
  BSeq.semilen (x + y) = BSeq.semilen x + BSeq.semilen y

axiom forestLeaves_add (x y : BSeq) :
  forestLeavesOfSeq (x + y) = forestLeavesOfSeq x + forestLeavesOfSeq y

axiom treeLeaves_eq_forestLeaves_of_ne_nil (x : BSeq) (hx : x ≠ BSeq.nil) :
  treeLeavesOfSeq x = forestLeavesOfSeq x

axiom treeLeaves_add_of_ne_nil (x y : BSeq) (hx : x ≠ BSeq.nil) :
  treeLeavesOfSeq (x + y) = treeLeavesOfSeq x + forestLeavesOfSeq y

/-
Context for the paper’s auxiliary families R and S.
We include the “full” definitional equations (as axioms) so Aristotle can prove
set-difference/intersection lemmas if needed, but without redoing boilerplate.
-/
class LozanoContextFull where
  R : BSeq → Finset BSeq
  S : BSeq → Finset BSeq

  -- Definitions of R and S (paper):
  R_nil : R BSeq.nil = {BSeq.nil}
  R_cons : ∀ x y, R (BSeq.cons x y) = insert (BSeq.cons x y) (R (x + y))

  S_nil : S BSeq.nil = {BSeq.nil}
  S_cons_def : ∀ x y, S (BSeq.cons x y) = R x ∪ S (x + y)

  -- Lemma 5 (paper): S(x+y) ⊆ S(x) ∪ S(y)
  lemma5 : ∀ x y : BSeq, (S (x + y) : Set BSeq) ⊆ (S x ∪ S y : Finset BSeq)

  -- Fact 2 (paper): |R[x]| = |x| + 1
  R_card : ∀ x : BSeq, (R x).card = BSeq.semilen x + 1

  -- Positivity of treeLeaves
  treeLeaves_pos : ∀ x : BSeq, 1 ≤ treeLeavesOfSeq x

export LozanoContextFull (R S R_nil R_cons S_nil S_cons_def lemma5 R_card treeLeaves_pos)

/-
Convenience derived lemma for the general (non-degenerate) cons case:
S(cons x y) ⊆ R x ∪ S x ∪ S y  (from S_cons_def + lemma5).
We assume its card-bound form to avoid Finset boilerplate.
-/
axiom S_cons_card_le [LozanoContextFull] (x y : BSeq) :
  (S (BSeq.cons x y)).card ≤ (R x).card + (S x).card + (S y).card

/-
Key algebra lemma (already found): the inequality needed in the v≠nil case.
-/
theorem lemma7_algebra (a b tu tv : Nat) (htu : 1 ≤ tu) (htv : 1 ≤ tv) :
    a + a * tu + b * tv + 3 ≤ (a + b + 1) * (tu + tv) + 1 := by
  nlinarith

/-
NEW INTERMEDIATE LEMMA (the missing lever for the v = nil degeneracy):

Prove that R contributes at most `treeLeavesOfSeq x` *new* elements beyond S.
This makes the v=nil case of Lemma 7 go through cleanly via:
  card (R x ∪ S x) ≤ card (S x) + card (R x \ S x).

Aristotle: Please prove this lemma first (likely by strong induction on semilen).
-/
theorem R_diff_S_card_le_treeLeaves [LozanoContextFull] (x : BSeq) :
    (R x \ S x).card ≤ treeLeavesOfSeq x := by
  -- Aristotle: prove this.
  -- Hints:
  -- * Strong induction on `BSeq.semilen x`.
  -- * Use R_nil/R_cons, S_nil/S_cons_def, lemma5, add_nil, semilen_append, and leaf lemmas.
  -- * In cons-case, split on the tail to handle y=nil vs y≠nil if needed.
  sorry

/-
TARGET THEOREM (missing piece):

Tree-leaf analogue of Lemma 7:
  |S[x]| ≤ |x| * treeLeaves(x) + 1
where |x| = semilen x.
-/
theorem lemma7_tree [LozanoContextFull] (x : BSeq) :
    (S x).card ≤ BSeq.semilen x * treeLeavesOfSeq x + 1 := by
  -- Aristotle: prove this.
  -- Strong induction on semilen x is recommended.
  -- In cons-case `x = cons u v`:
  --   * If v = nil:
  --       use S_cons_def + add_nil to rewrite S(cons u nil) = R u ∪ S u
  --       then card ≤ card(S u) + card(R u \ S u)
  --       then apply IH + R_diff_S_card_le_treeLeaves.
  --   * If v ≠ nil:
  --       use S_cons_card_le, R_card, IH(u), IH(v),
  --       and rewrite treeLeaves(cons u v) = treeLeaves u + treeLeaves v
  --       (since v ≠ nil ⇒ forestLeaves v = treeLeaves v),
  --       then finish with lemma7_algebra.
  sorry

end Lozano
