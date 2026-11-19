module

public import SubtreeProofs.Rust.SourceHeapHelperWorld

/-! Successful actual readback supplies its own finite depth bound. Increasing
only the ghost budget preserves the exact packet and complete read list. No
execution work or source fuel is charged for this proof-only observation. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

mutual
  theorem snapshot_depth (fuel : Nat) {memory : Memory} {cell : Cell} {value : Value} {reads : List Nat}
      (h : snapshot fuel memory cell = some (value, reads)) : valueDepth value ≤ fuel := by
    cases fuel with
    | zero => cases h
    | succ fuel =>
      cases cell with
      | boolean b | number b =>
        simp only [snapshot, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [valueDepth]
        omega
      | node kind tag cells =>
        cases hs : snapshotFields fuel memory cells with
        | none => simp [snapshot_node, hs] at h
        | some pair =>
          rcases pair with ⟨values, used⟩
          simp only [snapshot_node, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Nat.add_le_add_right (snapshotFields_depth fuel hs) 1
      | shared pointer =>
        cases hr : read memory pointer with
        | none => simp [snapshot, hr] at h
        | some child =>
          cases hs : snapshot fuel memory child with
          | none => simp [snapshot, hr, hs] at h
          | some pair =>
            rcases pair with ⟨inner, used⟩
            simp only [snapshot, hr, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Nat.add_le_add_right (snapshot_depth fuel hs) 1
      | owned address =>
        cases hr : memory[address]? with
        | none => simp [snapshot, hr] at h
        | some child =>
          cases hs : snapshot fuel memory child with
          | none => simp [snapshot, hr, hs] at h
          | some pair =>
            rcases pair with ⟨inner, used⟩
            simp only [snapshot, hr, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Nat.add_le_add_right (snapshot_depth fuel hs) 1
  termination_by (fuel, sizeOf cell)

  theorem snapshotFields_depth (fuel : Nat) {memory : Memory} {cells : List Cell} {values : List Value} {reads : List Nat}
      (h : snapshotFields fuel memory cells = some (values, reads)) : fieldsDepth values ≤ fuel := by
    cases cells with
    | nil => cases h; exact Nat.zero_le _
    | cons first rest =>
      cases hf : snapshot fuel memory first with
      | none => simp [snapshotFields_cons, hf] at h
      | some pair =>
        rcases pair with ⟨value, used⟩
        cases hr : snapshotFields fuel memory rest with
        | none => simp [snapshotFields_cons, hf, hr] at h
        | some pair =>
          rcases pair with ⟨tail, more⟩
          simp only [snapshotFields_cons, hf, hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Nat.max_le.mpr ⟨snapshot_depth fuel hf, snapshotFields_depth fuel hr⟩
  termination_by (fuel, sizeOf cells)
end

theorem snapshot_enlarge {small large : Nat} (bound : small ≤ large)
    {memory : Memory} {cell : Cell} {value : Value} {reads : List Nat}
    (h : snapshot small memory cell = some (value, reads)) : snapshot large memory cell = some (value, reads) :=
  (snapshot_spec small h).snapshot large ((snapshot_depth small h).trans bound)

theorem snapshotFields_enlarge {small large : Nat} (bound : small ≤ large)
    {memory : Memory} {cells : List Cell} {values : List Value} {reads : List Nat}
    (h : snapshotFields small memory cells = some (values, reads)) : snapshotFields large memory cells = some (values, reads) :=
  (snapshotFields_spec small h).snapshot large ((snapshotFields_depth small h).trans bound)

namespace Storage

theorem readPacket_depth {budget : Nat} {world : World} {cell : Cell} {packet : SourceEval.Addressed.ValueCell}
    (h : readPacket budget world cell = some packet) : valueDepth packet.2 ≤ budget := by
  unfold readPacket at h
  cases hs : snapshot budget world.memory cell with
  | none => simp [hs] at h
  | some pair =>
    rcases pair with ⟨value, used⟩
    simp only [hs, Bind.bind, Option.bind] at h
    split at h
    next live => cases h; exact snapshot_depth budget hs
    next => cases h

theorem readPacket_enlarge {small large : Nat} (bound : small ≤ large)
    {world : World} {cell : Cell} {packet : SourceEval.Addressed.ValueCell}
    (h : readPacket small world cell = some packet) : readPacket large world cell = some packet := by
  obtain ⟨hc, readable⟩ := readPacket_spec h
  rcases packet with ⟨raw, value⟩
  cases hc
  exact readPacket_complete readable large ((readPacket_depth h).trans bound)

end Storage
end SubtreeProofs.Rust.LookupSource.Partial.Addressed
