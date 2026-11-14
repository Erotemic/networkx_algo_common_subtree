module

public import SubtreeProofs.Rust.SparseCutSelection
public import SubtreeProofs.Rust.AssignmentArithmetic
import Mathlib.Tactic

/-! # Independent candidate minima and frames for the actual sparse row scan -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseCut

abbrev Entry := (Nat × Nat) × ℤ

def cutEntry (cut : sparse.SparseCut) : Entry := ((cut.row.val,cut.column.val),cut.delta.val)

def bestEntries : Option sparse.SparseCut → List Entry
  | none => []
  | some cut => [cutEntry cut]

/-- Minimum value and an actual original-coordinate attaining candidate. -/
def BestAmong (best : Option sparse.SparseCut) (candidates : List Entry) : Prop :=
  toMinimum best = (candidates.map Prod.snd).minimum ∧
    ∀ cut, best = some cut → cutEntry cut ∈ candidates

/-- Any supplied accumulator is the minimum of its own singleton/empty frame. -/
theorem bestAmong_self (best : Option sparse.SparseCut) : BestAmong best (bestEntries best) := by
  cases best <;> simp [BestAmong,bestEntries,toMinimum,cutEntry]

/-- Actual selection appends precisely the new candidate to an arbitrary
previous minimum frame, preserving both attained coordinates and exact slack. -/
theorem select_cut_best_spec (previous : Option sparse.SparseCut) (candidate : sparse.SparseCut)
    (candidates : List Entry) (hp : BestAmong previous candidates) :
    sparse.select_cut previous candidate ⦃ result => BestAmong (some result) (candidates++[cutEntry candidate]) ⦄ := by
  apply WP.spec_mono (select_cut_spec previous candidate)
  rintro result ⟨hMin,hOriginal⟩
  refine ⟨?_,?_⟩
  · simp only [List.map_append,List.map_cons,List.map_nil,List.minimum_concat]
    rw [← hp.1]
    exact hMin
  · intro output hOutput
    cases Option.some.inj hOutput
    rcases hOriginal with hPrevious | rfl
    · exact List.mem_append_left _ (hp.2 result hPrevious.symm)
    · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Replacing an earlier minimum frame by its complete candidate list leaves
the resulting minimum unchanged and preserves an original attaining entry. -/
theorem BestAmong.replace_frame {best output : Option sparse.SparseCut} {prior fresh : List Entry}
    (hp : BestAmong best prior) (hq : BestAmong output (bestEntries best++fresh)) : BestAmong output (prior++fresh) := by
  have hFrame : ((bestEntries best).map Prod.snd).minimum = (prior.map Prod.snd).minimum :=
    (bestAmong_self best).1.symm.trans hp.1
  refine ⟨?_,?_⟩
  · have hh := hq.1
    rw [List.map_append,List.minimum_append,hFrame] at hh
    simpa only [List.map_append,List.minimum_append] using hh
  · intro chosen hChosen
    rcases List.mem_append.mp (hq.2 chosen hChosen) with hOld | hFresh
    · cases best with
      | none => simp only [bestEntries,List.not_mem_nil] at hOld
      | some previous =>
        have he : cutEntry chosen = cutEntry previous := List.mem_singleton.mp hOld
        rw [he]
        exact List.mem_append_left _ (hp.2 previous rfl)
    · exact List.mem_append_right _ hFresh

/-- One independently enumerated allowed edge of a row. The optional cost and
selection flag are taken from the original input views; the scan is not used. -/
def rowEntry (cost : Slice (Option I64)) (potential : I128) (columns : Slice I128)
    (selected : Slice Bool) (row column : Nat) : Option Entry :=
  if selected.val[column]! then none else
    (cost.val[column]!).map (fun value => ((row,column),value.val-potential.val-columns.val[column]!.val))

/-- Enumerate all actual allowed candidates in a row prefix, independently of
which candidate the imperative source scan currently keeps. -/
def rowCandidates (cost : Slice (Option I64)) (potential : I128) (columns : Slice I128)
    (selected : Slice Bool) (row upto : Nat) : List Entry :=
  (List.range upto).filterMap (rowEntry cost potential columns selected row)

@[simp] theorem rowCandidates_zero (cost : Slice (Option I64)) (potential : I128) (columns : Slice I128)
    (selected : Slice Bool) (row : Nat) : rowCandidates cost potential columns selected row 0 = [] := rfl

/-- Increasing the actual loop frontier appends exactly its one optional edge. -/
theorem rowCandidates_succ (cost : Slice (Option I64)) (potential : I128) (columns : Slice I128)
    (selected : Slice Bool) (row column : Nat) :
    rowCandidates cost potential columns selected row (column+1) =
      rowCandidates cost potential columns selected row column ++ (rowEntry cost potential columns selected row column).toList := by
  simp only [rowCandidates,List.range_succ,List.filterMap_append,List.filterMap_cons,List.filterMap_nil]
  cases rowEntry cost potential columns selected row column <;> rfl

/-- The dimension/u64-weight envelope from the exact assignment algorithm fits
comfortably inside i128; the row primitive states that numeric frame explicitly. -/
def potentialBound : ℤ := 2^96

end SubtreeProofs.Rust.SparseCut

end
