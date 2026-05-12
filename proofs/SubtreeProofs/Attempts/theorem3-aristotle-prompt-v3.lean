import Mathlib

open scoped Classical
open scoped Nat

namespace Lozano

set_option autoImplicit false

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

@[simp] theorem treeLeaves_nil : treeLeavesOfSeq BSeq.nil = 1 := rfl
@[simp] theorem forestLeaves_nil : forestLeavesOfSeq BSeq.nil = 0 := rfl

/-- Useful rewrite for cons. -/
@[simp] theorem treeLeaves_cons (x y : BSeq) :
    treeLeavesOfSeq (BSeq.cons x y) = treeLeavesOfSeq x + forestLeavesOfSeq y := by
  simp [treeLeavesOfSeq, forestLeavesOfSeq, leavesPairOfSeq,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem forestLeaves_cons (x y : BSeq) :
    forestLeavesOfSeq (BSeq.cons x y) = treeLeavesOfSeq (BSeq.cons x y) := by
  simp [treeLeavesOfSeq, forestLeavesOfSeq, leavesPairOfSeq]

/- ============================================================
  Aristotle progress (kept as full proofs with the same names)
  ============================================================ -/

/-- Prove `x + nil = x` for BSeq. -/
@[simp] theorem add_nil (x : BSeq) : x + BSeq.nil = x := by
  induction x with
  | nil =>
      rfl
  | cons a b ih_a ih_b =>
      -- Turn the IH for `b + nil = b` into an `append` fact.
      have hb : BSeq.append b BSeq.nil = b := by
        -- `b + nil` is definitional equal to `append b nil` via the HAdd instance.
        simpa using ih_b
      -- Now finish by unfolding append at the top level.
      change BSeq.append (BSeq.cons a b) BSeq.nil = BSeq.cons a b
      -- `append (cons a b) nil = cons a (append b nil)`
      simp [BSeq.append, hb]


theorem semilen_append (x y : BSeq) :
    BSeq.semilen (x + y) = BSeq.semilen x + BSeq.semilen y := by
      -- We can prove this by induction on $x$.
      induction' x with x ih;
      · -- By definition of addition for BSeqs, we have BSeq.nil + y = y.
        have h_add_nil : BSeq.nil + y = y := by
          exact (congrArg (HAdd.hAdd nil) ∘ fun a => a) rfl;
        rw [ h_add_nil, BSeq.semilen_nil, zero_add ];
      · -- By definition of semilen, we have:
        have h_semilen_cons : ∀ x y : BSeq, (x.cons y).semilen = x.semilen + y.semilen + 1 := by
          exact fun x y => semilen_cons x y;
        convert h_semilen_cons x ( ih + y ) using 1;
        linarith [ h_semilen_cons x ih ]

theorem forestLeaves_add (x y : BSeq) :
    forestLeavesOfSeq (x + y) = forestLeavesOfSeq x + forestLeavesOfSeq y := by
      -- By definition of forestLeavesOfSeq, we have that forestLeavesOfSeq (x + y) = forestLeavesOfSeq x + forestLeavesOfSeq y.
      induction' x with x ih generalizing y;
      · aesop;
      · -- By definition of forestLeavesOfSeq, we have forestLeavesOfSeq (x.cons ih + y) = forestLeavesOfSeq (x.cons (ih + y)).
        have h_def : forestLeavesOfSeq (x.cons ih + y) = forestLeavesOfSeq (x.cons (ih + y)) := by
          congr;
        simp_all +decide [ ] ; ring!;

theorem treeLeaves_eq_forestLeaves_of_ne_nil (x : BSeq) (h : x ≠ BSeq.nil) :
    treeLeavesOfSeq x = forestLeavesOfSeq x := by
  cases x with
  | nil => cases h rfl
  | cons a b =>
      simp [treeLeaves_cons, forestLeaves_cons]

private theorem append_ne_nil {x : BSeq} (hx : x ≠ BSeq.nil) (y : BSeq) : x + y ≠ BSeq.nil := by
  cases x with
  | nil => cases hx rfl
  | cons a b =>
      intro h
      cases h  -- cons ≠ nil

/-- Prove `treeLeaves_add_of_ne_nil` using `forestLeaves_add`. -/
theorem treeLeaves_add_of_ne_nil (x y : BSeq) (hx : x ≠ BSeq.nil) :
    treeLeavesOfSeq (x + y) = treeLeavesOfSeq x + forestLeavesOfSeq y := by
  have hxy : x + y ≠ BSeq.nil := append_ne_nil hx y
  calc
    treeLeavesOfSeq (x + y)
        = forestLeavesOfSeq (x + y) := by
            -- use non-nil: treeLeaves = forestLeaves
            simpa [treeLeaves_eq_forestLeaves_of_ne_nil (x + y) hxy]
    _   = forestLeavesOfSeq x + forestLeavesOfSeq y := by
            simpa [forestLeaves_add]
    _   = treeLeavesOfSeq x + forestLeavesOfSeq y := by
            -- rewrite forestLeaves x to treeLeaves x (since x ≠ nil)
            have hx' : treeLeavesOfSeq x = forestLeavesOfSeq x :=
              treeLeaves_eq_forestLeaves_of_ne_nil x hx
            -- hx' : treeLeaves x = forestLeaves x
            -- so forestLeaves x = treeLeaves x by symmetry
            simpa [hx'.symm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Algebra lemma used in the non-degenerate cons-case. -/
theorem lemma7_algebra (a b tu tv : Nat) (htu : 1 ≤ tu) (htv : 1 ≤ tv) :
    a + a * tu + b * tv + 3 ≤ (a + b + 1) * (tu + tv) + 1 := by
  nlinarith

/-
Original prompt axioms, bundled as a class (same content as “axioms”, just packaged).
-/
class LozanoContext where
  R : BSeq → Finset BSeq
  S : BSeq → Finset BSeq
  R_card : ∀ x : BSeq, (R x).card = BSeq.semilen x + 1
  lemma5 : ∀ x y : BSeq, (S (x + y) : Set BSeq) ⊆ (S x ∪ S y : Finset BSeq)
  S_cons_def : ∀ x y : BSeq, S (BSeq.cons x y) = R x ∪ S (x + y)
  S_cons_card_le : ∀ x y : BSeq,
    (S (BSeq.cons x y)).card ≤ (R x).card + (S x).card + (S y).card
  treeLeaves_pos : ∀ x : BSeq, 1 ≤ treeLeavesOfSeq x

export LozanoContext (R S R_card lemma5 S_cons_def S_cons_card_le treeLeaves_pos)

/-
TARGET (missing piece). Aristotle should prove this.
-/
theorem lemma7_tree [LozanoContext] (x : BSeq) :
    (S x).card ≤ BSeq.semilen x * treeLeavesOfSeq x + 1 := by
  -- Aristotle: prove the theorem (strong induction on semilen recommended).
  sorry

end Lozano
