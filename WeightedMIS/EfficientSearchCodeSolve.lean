module

public import WeightedMIS.EfficientSearchCodeSearch
public import WeightedMIS.EfficientSearchPointerSolve

/-! # Compilation of initialization and total search -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.RegisterCode

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine

variable {p : ℕ} {code : Code p}

theorem solveEval_compile {insert search entry : Fin p} (hentry : code entry = solveBody insert search)
    (compileInsert : ∀ {h : Heap} {key a tree : Ptr} {result : Run (Option Ptr)},
      InsertEval h key a tree result →
      Within code h (initialRegisters [.pointer key, .pointer a, .pointer tree]) (code insert)
        (pointerOutput result.value) result.heap (100 * result.trace.length))
    (compileSearch : ∀ {h : Heap} {graph queue settled : Ptr} {result : Run (Option Pointer.SearchRecord)},
      Pointer.SearchEval h graph queue settled result →
      Within code h (initialRegisters [.pointer graph, .pointer queue, .pointer settled]) (code search)
        (searchOutput result.value) result.heap (100 * result.trace.length))
    {h : Heap} {graph source zeroKey : Ptr} {result : Run (Option Pointer.SearchRecord)}
    (he : Pointer.SolveEval h graph source zeroKey result) :
    Within code h (initialRegisters [.pointer graph, .pointer source, .pointer zeroKey]) (code entry)
      (searchOutput result.value) result.heap (100 * result.trace.length) := by
  cases he with
  | @solve queue initialized result initial value searchEval =>
    cases initial with
    | @start inserted insertion =>
      obtain ⟨status, outQueue, outSettled, hout⟩ := searchEval_output searchEval
      let regs := initialRegisters [.pointer graph, .pointer source, .pointer zeroKey]
      let storedRegs := Function.update regs 3 (.pointer h.length)
      let queueRegs := bindResults storedRegs [4] [.pointer queue]
      let finalRegs := bindResults queueRegs [5, 6, 7] [.flag status, .pointer outQueue, .pointer outSettled]
      have hret : Within code result.heap finalRegs (.ret [r 5, r 6, r 7])
          [.flag status, .pointer outQueue, .pointer outSettled] result.heap 7 := by
        simpa [finalRegs, r, values, Atom.eval, bindResults, Function.update_apply] using
          Within.ret code result.heap finalRegs [r 5, r 6, r 7]
      have hs := compileSearch searchEval
      rw [hout] at hs
      have hsc := Within.call (regs := queueRegs) (procedure := search)
        (arguments := [r 0, r 4, .null]) (results := [5, 6, 7])
        (by simpa [queueRegs, storedRegs, regs, r, values, Atom.eval, initialRegisters,
            bindResults, Function.update_apply] using hs) hret
      have hi := compileInsert insertion
      change inserted.value = some queue at value
      rw [value] at hi
      have hic := Within.call (regs := storedRegs) (procedure := insert)
        (arguments := [r 2, r 3, .null]) (results := [4])
        (by simpa [storedRegs, regs, r, values, Atom.eval, initialRegisters, pointerOutput,
            Function.update_apply, Pointer.storeCandidate, Program.allocate] using hi) hsc
      have hall := Within.allocate (regs := regs) (dst := 3) (expr := .pair (r 1) .null)
        (c := .pair source 0)
        (by simp [regs, r, CellExpr.eval, Atom.eval, initialRegisters, Value.asPointer])
        (by simpa [storedRegs, Pointer.storeCandidate, Program.allocate] using hic)
      rw [hentry]
      change Within _ _ _ _ (searchOutput result.value) _ _
      rw [hout]
      apply hall.mono
      simp only [sequenceRuns, List.length_append, List.length_cons, List.length_nil,
        Pointer.storeCandidate, Program.allocate, CellExpr.args]
      omega

end WeightedMIS.EfficientSearch.RegisterCode
