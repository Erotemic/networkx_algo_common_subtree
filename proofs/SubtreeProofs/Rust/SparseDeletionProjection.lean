module

public import SubtreeProofs.Rust.SparseDeletionVertices
public import SubtreeProofs.Rust.SparseCutSelection
import Mathlib.Tactic

/-!
# Actual sparse-deletion matrix and potential projections

A common selected-read loop covers the actual source row, matrix and potential
builders. Its callback is the actual checked source read, with every selected
index bounded. Contents are preserved in the supplied original-index order;
no allocation-capacity or runtime interpretation is asserted.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseDeletion

theorem mapped_get {T V : Type*} [Inhabited T] [Inhabited V]
    (view : T → V) (values : List T) (index : Nat) (hi : index < values.length) :
    (values.map view)[index]! = view values[index]! := by
  rw [getElem!_pos (values.map view) index (by simpa only [List.length_map] using hi),
    getElem!_pos values index hi]
  simp only [List.getElem_map]


/-- The common body of the three actual selected-read builders. -/
def gatherBody {T : Type*} (vertices : Slice Usize) (read : Usize → Result T)
    (state : alloc.vec.Vec T × Usize) :
    Result (ControlFlow (alloc.vec.Vec T × Usize) (alloc.vec.Vec T)) := do
  if state.2 < Slice.len vertices then
    let vertex ← Slice.index_usize vertices state.2
    let value ← read vertex
    let result ← alloc.vec.Vec.push state.1 value
    let next ← state.2 + 1#usize
    ok (cont (result,next))
  else ok (done state.1)

/-- A represented selected-read loop terminates and returns the exact sequence
of independent model values. Its callbacks must establish their own safety. -/
theorem gather_spec {T V : Type*} (view : T → V) (model : Usize → V)
    (vertices : Slice Usize) (read : Usize → Result T)
    (hRead : ∀ vertex ∈ vertices.val, read vertex ⦃ value => view value = model vertex ⦄) :
    loop (gatherBody vertices read) (alloc.vec.Vec.new T, 0#usize) ⦃ result =>
      result.val.map view = vertices.val.map model ⦄ := by
  apply loop.spec_decr_nat (fun state => vertices.length-state.2.val)
    (fun state => state.2.val ≤ vertices.length ∧
      state.1.val.map view = (vertices.val.take state.2.val).map model)
    _ _ _ ?_ (by simp)
  rintro ⟨result,index⟩ ⟨hIndex,hPrefix⟩
  unfold gatherBody
  dsimp only
  split
  · rename_i hlt
    have hLen := Slice.len_val vertices
    have hi : index.val < vertices.length := by scalar_tac
    apply WP.spec_bind (Slice.index_usize_spec vertices index hi)
    intro vertex hVertex
    have hm : vertex ∈ vertices.val := by rw [hVertex]; exact List.getElem_mem hi
    apply WP.spec_bind (hRead vertex hm)
    intro value hValue
    have hResultLength : result.val.length = index.val := by
      have h := congrArg List.length hPrefix
      simpa only [List.length_map,List.length_take,Nat.min_eq_left hIndex] using h
    apply WP.spec_bind (alloc.vec.Vec.push_spec result value (by rw [hResultLength]; scalar_tac))
    intro updated hUpdated
    apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    intro next hNext
    simp only [WP.spec_ok]
    refine ⟨⟨by scalar_tac,?_⟩,by scalar_tac⟩
    have hn : next.val = index.val+1 := by scalar_tac
    rw [hUpdated,List.map_append,List.map_singleton,hPrefix,hn,
      List.take_succ_eq_append_getElem hi,List.map_append,List.map_singleton,hValue,hVertex]
  · rename_i hnot
    have he : index.val = vertices.length := by have hl := Slice.len_val vertices; scalar_tac
    exact (WP.spec_ok _).mpr (by simpa only [he,List.take_length] using hPrefix)

/-- Actual optional-cost row projection retains precisely the selected original
columns, in order, including forbidden entries and repeated selections. -/
theorem project_row_spec (values : Slice (Option I64)) (vertices : Slice Usize)
    (hBounds : ∀ vertex ∈ vertices.val, vertex.val < values.length) :
    sparse_deletion.project_row values vertices ⦃ result =>
      result.val = vertices.val.map (fun vertex => values.val[vertex.val]!) ⦄ := by
  unfold sparse_deletion.project_row sparse_deletion.project_row_loop
  apply WP.spec_mono (gather_spec id (fun vertex => values.val[vertex.val]!) vertices
    (Slice.index_usize values) ?_)
  · intro result hResult
    simpa only [List.map_id] using hResult
  · intro vertex hv
    apply WP.spec_mono (Slice.index_usize_spec values vertex (hBounds vertex hv))
    intro value hValue
    simpa only [id_eq,getElem!_pos values.val vertex.val (hBounds vertex hv)] using hValue

/-- Actual signed-potential projection reads the same original coordinates as
the cost projection, without modifying their exact integer values. -/
theorem project_potentials_spec (values : Slice I128) (vertices : Slice Usize)
    (hBounds : ∀ vertex ∈ vertices.val, vertex.val < values.length) :
    sparse_deletion.project_potentials values vertices ⦃ result =>
      result.val = vertices.val.map (fun vertex => values.val[vertex.val]!) ⦄ := by
  unfold sparse_deletion.project_potentials sparse_deletion.project_potentials_loop
  apply WP.spec_mono (gather_spec id (fun vertex => values.val[vertex.val]!) vertices
    (Slice.index_usize values) ?_)
  · intro result hResult
    simpa only [List.map_id] using hResult
  · intro vertex hv
    apply WP.spec_mono (Slice.index_usize_spec values vertex (hBounds vertex hv))
    intro value hValue
    simpa only [id_eq,getElem!_pos values.val vertex.val (hBounds vertex hv)] using hValue

/-- The actual nested builder projects both axes of the original square
optional-cost matrix; every source read and checked increment succeeds. -/
theorem project_cost_spec (cost : Slice (alloc.vec.Vec (Option I64))) (vertices : Slice Usize)
    (hSquare : SparseCut.Square cost)
    (hBounds : ∀ vertex ∈ vertices.val, vertex.val < cost.length) :
    sparse_deletion.project_cost cost vertices ⦃ result =>
      result.val.map alloc.vec.Vec.val = vertices.val.map (fun row =>
        vertices.val.map (fun column => (cost.val[row.val]!).val[column.val]!)) ⦄ := by
  unfold sparse_deletion.project_cost sparse_deletion.project_cost_loop
  have hBody : (fun state : alloc.vec.Vec (alloc.vec.Vec (Option I64)) × Usize =>
      sparse_deletion.project_cost_loop.body cost vertices state.1 state.2) =
      gatherBody vertices (fun row => do
        let values ← Slice.index_usize cost row
        sparse_deletion.project_row (alloc.vec.Vec.deref values) vertices) := by
    funext state
    simp only [sparse_deletion.project_cost_loop.body,gatherBody,Std.bind_assoc]
  rw [hBody]
  apply gather_spec alloc.vec.Vec.val
    (fun row => vertices.val.map (fun column => (cost.val[row.val]!).val[column.val]!))
    vertices (fun row => do
      let values ← Slice.index_usize cost row
      sparse_deletion.project_row (alloc.vec.Vec.deref values) vertices)
  intro row hr
  apply WP.spec_bind (Slice.index_usize_spec cost row (hBounds row hr))
  intro values hValues
  have he : values = cost.val[row.val]! := by
    simpa only [getElem!_pos cost.val row.val (hBounds row hr)] using hValues
  apply WP.spec_mono (project_row_spec (alloc.vec.Vec.deref values) vertices ?_)
  · intro result hResult
    simpa only [alloc.vec.Vec.deref,Slice.from_val,he] using hResult
  · intro column hc
    have hl := hSquare row.val (hBounds row hr)
    simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,he,alloc.vec.Vec.length,hl]
      using hBounds column hc

/-- The projected source matrix has one row for every supplied vertex. -/
theorem projected_length (cost : Slice (alloc.vec.Vec (Option I64))) (vertices : Slice Usize)
    (output : alloc.vec.Vec (alloc.vec.Vec (Option I64)))
    (h : output.val.map alloc.vec.Vec.val = vertices.val.map (fun row =>
      vertices.val.map (fun column => (cost.val[row.val]!).val[column.val]!))) :
    output.length = vertices.length := by
  have hh := congrArg List.length h
  simpa only [List.length_map] using hh

/-- Exact row contents follow from the source nested builder's representation. -/
theorem projected_row (cost : Slice (alloc.vec.Vec (Option I64))) (vertices : Slice Usize)
    (output : alloc.vec.Vec (alloc.vec.Vec (Option I64)))
    (h : output.val.map alloc.vec.Vec.val = vertices.val.map (fun row =>
      vertices.val.map (fun column => (cost.val[row.val]!).val[column.val]!)))
    (row : Nat) (hr : row < vertices.length) :
    (output.val[row]!).val = vertices.val.map (fun column =>
      (cost.val[vertices.val[row]!.val]!).val[column.val]!) := by
  have hl := projected_length cost vertices output h
  have hi : row < output.val.length := by change row < output.length; omega
  have hh := congrArg (fun rows : List (List (Option I64)) => rows[row]!) h
  rw [mapped_get alloc.vec.Vec.val output.val row hi,mapped_get _ vertices.val row hr] at hh
  exact hh

/-- Even repeated selections produce a square projected matrix with the
correct selected width. This supplies the actual augmentation shape premise. -/
theorem projected_square (cost : Slice (alloc.vec.Vec (Option I64))) (vertices : Slice Usize)
    (output : alloc.vec.Vec (alloc.vec.Vec (Option I64)))
    (h : output.val.map alloc.vec.Vec.val = vertices.val.map (fun row =>
      vertices.val.map (fun column => (cost.val[row.val]!).val[column.val]!))) :
    SparseCut.Square (alloc.vec.Vec.deref output) := by
  have hl := projected_length cost vertices output h
  unfold SparseCut.Square
  intro row hr
  have hi : row < vertices.length := by
    simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,← hl] using hr
  have hh := congrArg List.length (projected_row cost vertices output h row hi)
  have hRowLength : (output.val[row]!).length = vertices.length := by
    simpa only [List.length_map] using hh
  simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val] using hRowLength.trans hl.symm

end SubtreeProofs.Rust.SparseDeletion

end
