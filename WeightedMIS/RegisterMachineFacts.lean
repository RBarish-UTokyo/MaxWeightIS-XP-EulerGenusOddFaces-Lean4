module

public import WeightedMIS.RegisterMachine
public import WeightedMIS.PointerCallTrees

/-! # Uniformity and trace authenticity for finite register programs -/

@[expose] public section

namespace WeightedMIS.RegisterMachine

open WeightedMIS.PointerMemory

theorem Value.moves_exec (h : Heap) (v : Value) : HeapExec h v.moves h := by
  cases v with
  | pointer p => exact .cons (.copyPointer h p) (HeapExec.cons (.copyPointer h p) (.nil h))
  | flag b => exact .cons (.copyFlag h b) (HeapExec.cons (.copyFlag h b) (.nil h))

theorem moves_exec (h : Heap) (vs : List Value) : HeapExec h (moves vs) h := by
  induction vs with
  | nil => exact .nil h
  | cons v vs ih => exact (v.moves_exec h).append ih

theorem decodedMoves_exec (h : Heap) (c : Cell) : HeapExec h (decodedMoves c) h :=
  (((decoded c).1.moves_exec h).append ((decoded c).2.1.moves_exec h)).append ((decoded c).2.2.moves_exec h)

/-- Every interpreted program trace is an actual sequence of heap instructions;
register-transfer events preserve the heap and are independently bit-charged. -/
theorem Exec.heap_exec {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {result : Run (List Value)} (he : Exec code h regs command result) :
    HeapExec h result.trace result.heap := by
  induction he with
  | ret => exact .cons (.control _) (moves_exec _ _)
  | copy rest ih => exact (HeapExec.cons (.control _) (Value.moves_exec _ _)).append ih
  | @allocate h regs dst expr c next result evaluated rest ih =>
    simpa only [withEvents, Program.allocate, List.append_assoc] using
      (HeapExec.cons (.control h) ((moves_exec h (values regs expr.args)).append
        ((allocate_exec h c).append (Value.moves_exec (h ++ [c]) (.pointer h.length))))).append ih
  | @load h regs address p c first second bit branches result evaluated loaded rest ih =>
    have hl : HeapExec h [Event.load p (some c)] h := by
      rw [← loaded]
      exact load_exec h p
    exact (HeapExec.cons (.control h) ((Value.moves_exec h (.pointer p)).append
      (hl.append (decodedMoves_exec h c)))).append ih
  | branch evaluated rest ih => exact (HeapExec.cons (.control _) (Value.moves_exec _ _)).append ih
  | call body rest ihbody ihrest => exact (HeapExec.cons (.control _) (moves_exec _ _)).append (ihbody.append ihrest)

/-- The fixed code and initial state determine the entire result, including its
heap and charged trace. A short execution cannot be selected by an oracle. -/
theorem Exec.deterministic {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {first second : Run (List Value)}
    (hf : Exec code h regs command first) (hs : Exec code h regs command second) : first = second := by
  induction hf generalizing second with
  | ret => cases hs; rfl
  | copy rest ih =>
    cases hs with
    | copy rest' => cases ih rest'; rfl
  | allocate evaluated rest ih =>
    cases hs with
    | allocate evaluated' rest' =>
      cases Option.some.inj (evaluated.symm.trans evaluated')
      cases ih rest'
      rfl
  | load evaluated loaded rest ih =>
    cases hs with
    | load evaluated' loaded' rest' =>
      cases Value.pointer.inj (evaluated.symm.trans evaluated')
      cases Option.some.inj (loaded.symm.trans loaded')
      cases ih rest'
      rfl
  | branch evaluated rest ih =>
    cases hs with
    | branch evaluated' rest' =>
      cases Value.flag.inj (evaluated.symm.trans evaluated')
      cases ih rest'
      rfl
  | call body rest ihbody ihrest =>
    cases hs with
    | call body' rest' =>
      cases ihbody body'
      cases ihrest rest'
      rfl

end WeightedMIS.RegisterMachine
