module

public import SubtreeProofs.Rust.MatchingCostConstruction
public import SubtreeProofs.Rust.AssignmentEntrypoint
import Mathlib.Tactic

/-!
# Actual dummy matrix representation and accepted assignment input

Exact views proved for the source matrix builder imply its physical row count,
square shape and every integer cell value. The actual assignment API therefore
accepts the constructed matrix under the adapter's checked dimension bounds.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.MatchingMatrixRepresentation

open MatchingCostSpecification MatchingCostConstruction

private theorem mapped_get {A B : Type*} [Inhabited A] [Inhabited B] (f : A → B) (values : List A)
    (index : Nat) (hi : index < values.length) : (values.map f)[index]! = f values[index]! := by
  rw [getElem!_pos (values.map f) index (by simpa only [List.length_map] using hi),getElem!_pos values index hi]
  simp only [List.getElem_map]

private theorem range_mapped_get {B : Type*} [Inhabited B] (f : Nat → B) (width index : Nat) (hi : index < width) :
    ((List.range width).map f)[index]! = f index := by
  rw [mapped_get f (List.range width) index (by simpa only [List.length_range] using hi)]
  rw [getElem!_pos (List.range width) index (by simpa only [List.length_range] using hi)]
  simp only [List.getElem_range]

def Built (weights : Slice (alloc.vec.Vec (Option I64))) (left dimension : Usize) (cost : alloc.vec.Vec (alloc.vec.Vec I64)) : Prop :=
  cost.val.map (fun row => row.val.map IScalar.val) = matrixValues weights left.val dimension.val dimension.val

theorem built_length (weights : Slice (alloc.vec.Vec (Option I64))) (left dimension : Usize)
    (cost : alloc.vec.Vec (alloc.vec.Vec I64)) (h : Built weights left dimension cost) : cost.length = dimension.val := by
  have hh := congrArg List.length h
  simpa only [List.length_map,matrixValues_length] using hh

theorem built_row (weights : Slice (alloc.vec.Vec (Option I64))) (left dimension : Usize)
    (cost : alloc.vec.Vec (alloc.vec.Vec I64)) (h : Built weights left dimension cost) (row : Nat) (hr : row < dimension.val) :
    (cost.val[row]!).val.map IScalar.val = rowValues weights left.val row dimension.val := by
  have hlen := built_length weights left dimension cost h
  have hb : row < cost.val.length := by change row < cost.length; omega
  have hh := congrArg (fun rows : List (List ℤ) => rows[row]!) h
  rw [mapped_get (fun row : alloc.vec.Vec I64 => row.val.map IScalar.val) cost.val row hb] at hh
  simpa only [matrixValues,range_mapped_get _ dimension.val row hr] using hh

theorem built_row_length (weights : Slice (alloc.vec.Vec (Option I64))) (left dimension : Usize)
    (cost : alloc.vec.Vec (alloc.vec.Vec I64)) (h : Built weights left dimension cost) (row : Nat) (hr : row < dimension.val) :
    (cost.val[row]!).length = dimension.val := by
  have hh := congrArg List.length (built_row weights left dimension cost h row hr)
  simpa only [List.length_map,rowValues_length] using hh

theorem built_cell (weights : Slice (alloc.vec.Vec (Option I64))) (left dimension : Usize)
    (cost : alloc.vec.Vec (alloc.vec.Vec I64)) (h : Built weights left dimension cost) (row col : Nat)
    (hr : row < dimension.val) (hc : col < dimension.val) :
    (cost.val[row]!).val[col]!.val = costAt weights left.val row col := by
  have hrow := built_row weights left dimension cost h row hr
  have hlen := built_row_length weights left dimension cost h row hr
  have hb : col < (cost.val[row]!).val.length := by change col < (cost.val[row]!).length; omega
  have hh := congrArg (fun values : List ℤ => values[col]!) hrow
  rw [mapped_get IScalar.val (cost.val[row]!).val col hb] at hh
  simpa only [rowValues,range_mapped_get _ dimension.val col hc] using hh

theorem built_square (weights : Slice (alloc.vec.Vec (Option I64))) (left dimension : Usize)
    (cost : alloc.vec.Vec (alloc.vec.Vec I64)) (h : Built weights left dimension cost) :
    AssignmentValidation.Square (alloc.vec.Vec.deref cost) := by
  apply (AssignmentValidation.square_iff_index (alloc.vec.Vec.deref cost)).mpr
  intro row hr
  have hlen := built_length weights left dimension cost h
  have hi : row < dimension.val := by
    simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length,hlen] using hr
  have hh := built_row_length weights left dimension cost h row hi
  simpa only [alloc.vec.Vec.deref,Slice.from_val,Slice.length,alloc.vec.Vec.length,hlen] using hh

/-- The actual constructed matrix is admitted by the complete verified
assignment API. This is derived from actual contents and checked dimensions. -/
theorem built_admissible (weights : Slice (alloc.vec.Vec (Option I64))) (left dimension : Usize)
    (cost : alloc.vec.Vec (alloc.vec.Vec I64)) (h : Built weights left dimension cost)
    (hn : dimension.val ≤ U32.max) (hextent : dimension.val < Usize.max) :
    AssignmentEntrypoint.Admissible (alloc.vec.Vec.deref cost) := by
  have hlen := built_length weights left dimension cost h
  refine ⟨?_,?_,built_square weights left dimension cost h⟩
  · simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length,hlen] using hn
  · simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length,hlen] using hextent

end SubtreeProofs.Rust.MatchingMatrixRepresentation

end
