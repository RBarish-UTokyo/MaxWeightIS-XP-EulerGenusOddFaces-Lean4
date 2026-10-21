module

public import WeightedMIS.EfficientSearchCodeBasic
public import WeightedMIS.PointerCallTrees

/-! # Compilation of one weighted outgoing edge -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.RegisterCode

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine

variable {p : ℕ} {code : Code p}

theorem pushEval_compile {add extend insert push : Fin p}
    (hpush : code push = pushBody add extend insert) (hextend : code extend = extendBody)
    (compileAdd : ∀ {h : Heap} {ap bp : Ptr} {carry : Bool} {result : Run (Ptr × Bool)},
      AddEval h ap bp carry result →
      Within code h (initialRegisters [.pointer ap, .pointer bp, .flag carry]) (code add)
        [.pointer result.value.1, .flag result.value.2] result.heap (10 * result.trace.length))
    (compileInsert : ∀ {h : Heap} {key a tree : Ptr} {result : Run (Option Ptr)},
      InsertEval h key a tree result →
      Within code h (initialRegisters [.pointer key, .pointer a, .pointer tree]) (code insert)
        (pointerOutput result.value) result.heap (100 * result.trace.length))
    {h : Heap} {vertex path distance arc queue : Ptr} {result : Run (Option (Ptr × Bool))}
    (he : Pointer.PushEdgeEval h vertex path distance arc queue result) :
    Within code h (initialRegisters [.pointer vertex, .pointer path, .pointer distance,
      .pointer arc, .pointer queue]) (code push) (queueOutput result.value) result.heap
      (100 * result.trace.length) := by
  cases he with
  | @push target weightLabel weight label added inserted arcCell weightCell addition insertion =>
    obtain ⟨out, hout⟩ := insertion.value_some
    let initial := initialRegisters [.pointer vertex, .pointer path, .pointer distance,
      .pointer arc, .pointer queue]
    let loadedArc := loadRegisters initial 5 6 7 (.pair target weightLabel)
    let loadedWeight := loadRegisters loadedArc 8 9 7 (.pair weight label)
    let addedRegs := bindResults loadedWeight [10, 11] [.pointer added.value.1, .flag added.value.2]
    let candidate := Pointer.extendCandidate vertex path arc target added.heap
    let candidateRegs := bindResults addedRegs [12] [.pointer candidate.value]
    let finalRegs := bindResults candidateRegs [13] [.pointer out]
    have hret : Within code inserted.heap finalRegs (.ret [r 13, r 11])
        [.pointer out, .flag added.value.2] inserted.heap 5 := by
      simpa [finalRegs, candidateRegs, addedRegs, bindResults, r, values, Atom.eval,
        Function.update_apply] using Within.ret code inserted.heap finalRegs [r 13, r 11]
    have hins := compileInsert insertion
    rw [hout] at hins
    have hic := Within.call (procedure := insert) (arguments := [r 10, r 12, r 4]) (results := [13])
      (regs := candidateRegs)
      (by simpa [candidateRegs, addedRegs, loadedWeight, loadedArc, initial, candidate, pointerOutput,
          r, values, Atom.eval, initialRegisters, loadRegisters, decoded, bindResults,
          Function.update_apply] using hins) hret
    have hext := extendBody_correct code added.heap
      (initialRegisters [.pointer vertex, .pointer path, .pointer arc, .pointer target])
      vertex path arc target (by simp [initialRegisters]) (by simp [initialRegisters])
      (by simp [initialRegisters]) (by simp [initialRegisters])
    rw [← hextend] at hext
    have hec := Within.call (procedure := extend) (arguments := [r 0, r 1, r 3, r 5]) (results := [12])
      (regs := addedRegs)
      (by simpa [addedRegs, loadedWeight, loadedArc, initial, candidate, r, values, Atom.eval,
          initialRegisters, loadRegisters, decoded, bindResults, Function.update_apply] using hext) hic
    have hac := Within.call (procedure := add) (arguments := [r 2, r 8, .flag false]) (results := [10, 11])
      (regs := loadedWeight)
      (by simpa [loadedWeight, loadedArc, initial, r, values, Atom.eval, initialRegisters,
          loadRegisters, decoded, Function.update_apply] using compileAdd addition) hec
    have hwc := Within.load (regs := loadedArc) (address := r 6) (first := 8) (second := 9) (bit := 7)
      (branches := onlyPair (.call add [r 2, r 8, .flag false] [10, 11]
        (.call extend [r 0, r 1, r 3, r 5] [12]
          (.call insert [r 10, r 12, r 4] [13] (.ret [r 13, r 11])))))
      (by simp [loadedArc, r, Atom.eval, loadRegisters, decoded, Function.update_apply]) weightCell
      (by simpa [onlyPair, Cases.select, loadedWeight] using hac)
    have hwhole := Within.load (regs := initial) (address := r 3) (first := 5) (second := 6) (bit := 7)
      (branches := onlyPair (.load (r 6) 8 9 7 (onlyPair
        (.call add [r 2, r 8, .flag false] [10, 11]
          (.call extend [r 0, r 1, r 3, r 5] [12]
            (.call insert [r 10, r 12, r 4] [13] (.ret [r 13, r 11])))))))
      (by simp [initial, r, Atom.eval, initialRegisters]) arcCell
      (by simpa [onlyPair, Cases.select, loadedArc] using hwc)
    rw [hpush]
    simp only [hout, Option.map_some, queueOutput]
    apply hwhole.mono
    simp only [List.length_cons, List.length_nil, List.length_append, Program.load,
      Pointer.extendCandidate, Pointer.storeRawArc, Pointer.storeTraceCons, Pointer.storeCandidate,
      Program.allocate]
    omega

end WeightedMIS.EfficientSearch.RegisterCode
