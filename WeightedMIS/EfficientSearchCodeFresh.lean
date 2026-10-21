module

public import WeightedMIS.EfficientSearchCodeRelax

/-! # Compilation of settling and expanding a vertex -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.RegisterCode

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine

variable {p : ℕ} {code : Code p}

theorem freshEval_compile {insert lookup relax fresh : Fin p}
    (hfresh : code fresh = freshBody insert lookup relax)
    (compileInsert : ∀ {h : Heap} {key a tree : Ptr} {result : Run (Option Ptr)},
      InsertEval h key a tree result →
      Within code h (initialRegisters [.pointer key, .pointer a, .pointer tree]) (code insert)
        (pointerOutput result.value) result.heap (100 * result.trace.length))
    (compileLookup : ∀ {h : Heap} {key tree : Ptr} {result : Run (Option Ptr)},
      LookupEval h key tree result →
      Within code h (initialRegisters [.pointer key, .pointer tree]) (code lookup)
        (pointerOutput result.value) result.heap (100 * result.trace.length))
    (compileRelax : ∀ {h : Heap} {vertex path distance edges queue : Ptr} {result : Run (Option (Ptr × Bool))},
      Pointer.RelaxEval h vertex path distance edges queue result →
      Within code h (initialRegisters [.pointer vertex, .pointer path, .pointer distance,
        .pointer edges, .pointer queue]) (code relax)
        (queueOutput result.value) result.heap (100 * result.trace.length))
    {h : Heap} {graph vertex path distance queue settled : Ptr} {result : Run (Option Pointer.FreshValue)}
    (he : Pointer.FreshEval h graph vertex path distance queue settled result) :
    Within code h (initialRegisters [.pointer graph, .pointer vertex, .pointer path,
      .pointer distance, .pointer queue, .pointer settled]) (code fresh)
      (freshOutput result.value) result.heap (100 * result.trace.length) := by
  cases he with
  | @expand newSettled edges inserted outgoing expanded insertion insertValue lookupEval lookupValue relaxEval =>
    obtain ⟨out, overflow, outValue⟩ := relaxEval_value_some relaxEval
    let regs := initialRegisters [.pointer graph, .pointer vertex, .pointer path,
      .pointer distance, .pointer queue, .pointer settled]
    let storedRegs := Function.update regs 6 (.pointer h.length)
    let insertedRegs := bindResults storedRegs [7] [.pointer newSettled]
    let outgoingRegs := bindResults insertedRegs [8] [.pointer edges]
    let finalRegs := bindResults outgoingRegs [9, 10] [.pointer out, .flag overflow]
    have hret : Within code expanded.heap finalRegs (.ret [r 9, r 7, r 10])
        [.pointer out, .pointer newSettled, .flag overflow] expanded.heap 7 := by
      simpa [finalRegs, outgoingRegs, insertedRegs, r, values, Atom.eval, bindResults,
        Function.update_apply] using Within.ret code expanded.heap finalRegs [r 9, r 7, r 10]
    have hr := compileRelax relaxEval
    rw [outValue] at hr
    have hrc := Within.call (regs := outgoingRegs) (procedure := relax)
      (arguments := [r 1, r 2, r 3, r 8, r 4]) (results := [9, 10])
      (by simpa [outgoingRegs, insertedRegs, storedRegs, regs, r, values, Atom.eval,
          initialRegisters, bindResults, Function.update_apply, queueOutput] using hr) hret
    have hl := compileLookup lookupEval
    rw [lookupValue] at hl
    have hlc := Within.call (regs := insertedRegs) (procedure := lookup)
      (arguments := [r 1, r 0]) (results := [8])
      (by simpa [insertedRegs, storedRegs, regs, r, values, Atom.eval,
          initialRegisters, bindResults, Function.update_apply, pointerOutput] using hl) hrc
    have hi := compileInsert insertion
    rw [insertValue] at hi
    have hic := Within.call (regs := storedRegs) (procedure := insert)
      (arguments := [r 1, r 6, r 5]) (results := [7])
      (by simpa [storedRegs, regs, r, values, Atom.eval, initialRegisters,
          Function.update_apply, pointerOutput, Pointer.storeSettled, Program.allocate] using hi) hlc
    have hall := Within.allocate (regs := regs) (dst := 6) (expr := .pair (r 3) (r 2))
      (c := .pair distance path)
      (by simp [regs, r, CellExpr.eval, Atom.eval, initialRegisters, Value.asPointer])
      (by simpa [storedRegs, Pointer.storeSettled, Program.allocate] using hic)
    rw [hfresh]
    simp only [outValue, Option.map_some, freshOutput]
    apply hall.mono
    simp only [List.length_cons, List.length_nil, List.length_append,
      Pointer.storeSettled, Program.allocate, CellExpr.args]
    omega

end WeightedMIS.EfficientSearch.RegisterCode
