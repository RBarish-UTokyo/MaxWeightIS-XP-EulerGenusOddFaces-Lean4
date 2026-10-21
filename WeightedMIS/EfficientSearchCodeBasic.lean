module

public import WeightedMIS.EfficientSearchCode
public import WeightedMIS.EfficientSearchCodeBounds
public import WeightedMIS.EfficientSearchPointerEvaluation

/-! # Correctness of finite code for records and list inspections -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.RegisterCode

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine

variable {p : ℕ} (code : Code p)

theorem extendBody_correct (h : Heap) (regs : Registers) (vertex path arc target : Ptr)
    (h0 : regs 0 = .pointer vertex) (h1 : regs 1 = .pointer path)
    (h2 : regs 2 = .pointer arc) (h3 : regs 3 = .pointer target) :
    Within code h regs extendBody
      [.pointer (Pointer.extendCandidate vertex path arc target h).value]
      (Pointer.extendCandidate vertex path arc target h).heap 27 := by
  simp only [extendBody, Pointer.extendCandidate, Pointer.storeRawArc, Pointer.storeTraceCons,
    Pointer.storeCandidate, Program.allocate]
  apply Within.allocate (budget := 19) (c := .pair vertex arc)
    (by simp [r, CellExpr.eval, Atom.eval, h0, h2, Value.asPointer])
  apply Within.allocate (budget := 11) (c := .cons h.length path)
    (by simp [r, CellExpr.eval, Atom.eval, Function.update_apply, h1, Value.asPointer])
  apply Within.allocate (budget := 3) (c := .pair target (h ++ [Cell.pair vertex arc]).length)
    (by simp [r, CellExpr.eval, Atom.eval, Function.update_apply, h3, Value.asPointer])
  convert Within.ret code _ _ [r 6] using 1 <;> simp [r, values, Atom.eval, Function.update_apply]

theorem readPairBody_correct (h : Heap) (regs : Registers) (pointer a b : Ptr)
    (h0 : regs 0 = .pointer pointer) (hc : h[pointer]? = some (.pair a b)) :
    Within code h regs readPairBody [.pointer a, .pointer b] h 15 := by
  unfold readPairBody
  apply Within.load (budget := 5) (by simpa [r, Atom.eval] using h0) hc
  simpa [onlyPair, Cases.select, r, values, Atom.eval, loadRegisters, decoded,
    Function.update_apply] using Within.ret code h (loadRegisters regs 1 2 3 (.pair a b)) [r 1, r 2]

theorem emptyList_code_nil (h : Heap) (regs : Registers) (pointer : Ptr)
    (h2 : regs 2 = .pointer pointer) (hc : h[pointer]? = some .nil) :
    Within code h regs (.load (r 2) 3 4 5
      (listCases (.ret [.flag true]) (.ret [.flag false]))) [.flag true] h 13 := by
  apply Within.load (budget := 3) (by simpa [r, Atom.eval] using h2) hc
  simpa [listCases, Cases.select, values, Atom.eval] using
    Within.ret code h (loadRegisters regs 3 4 5 .nil) [.flag true]

theorem emptyList_code_cons (h : Heap) (regs : Registers) (pointer a tail : Ptr)
    (h2 : regs 2 = .pointer pointer) (hc : h[pointer]? = some (.cons a tail)) :
    Within code h regs (.load (r 2) 3 4 5
      (listCases (.ret [.flag true]) (.ret [.flag false]))) [.flag false] h 13 := by
  apply Within.load (budget := 3) (by simpa [r, Atom.eval] using h2) hc
  simpa [listCases, Cases.select, values, Atom.eval] using
    Within.ret code h (loadRegisters regs 3 4 5 (.cons a tail)) [.flag false]

def pairOutput : Option (Ptr × Ptr) → List Value
  | none => []
  | some (a, b) => [.pointer a, .pointer b]

def queueOutput : Option (Ptr × Bool) → List Value
  | none => []
  | some (q, overflow) => [.pointer q, .flag overflow]

def freshOutput : Option Pointer.FreshValue → List Value
  | none => []
  | some (q, s, overflow) => [.pointer q, .pointer s, .flag overflow]

def searchOutput : Option Pointer.SearchRecord → List Value
  | none => []
  | some result => [.flag (result.status == .overflow), .pointer result.queue, .pointer result.settled]

def flagOutput : Option Bool → List Value
  | none => []
  | some value => [.flag value]

def pointerOutput : Option Ptr → List Value
  | none => []
  | some value => [.pointer value]

theorem readPairEval_compile {h : Heap} {pointer : Ptr} {result : Run (Option (Ptr × Ptr))}
    (he : Pointer.ReadPairEval h pointer result) :
    Within code h (initialRegisters [.pointer pointer]) readPairBody
      (pairOutput result.value) result.heap 15 := by
  cases he with
  | pair hc =>
    exact readPairBody_correct code h _ _ _ _ (by simp [initialRegisters]) hc

theorem emptyListEval_code {h : Heap} {pointer : Ptr} {result : Run (Option Bool)}
    (he : Pointer.EmptyListEval h pointer result) (regs : Registers)
    (h2 : regs 2 = .pointer pointer) :
    Within code h regs (.load (r 2) 3 4 5
      (listCases (.ret [.flag true]) (.ret [.flag false])))
      (flagOutput result.value) result.heap 13 := by
  cases he with
  | nil hc => exact emptyList_code_nil code _ _ _ h2 hc
  | cons hc => exact emptyList_code_cons code _ _ _ _ _ h2 hc

theorem lookupEmptyEval_compile {lookup : Fin p}
    (compileLookup : ∀ {h : Heap} {key tree : Ptr} {result : Run (Option Ptr)},
      LookupEval h key tree result →
      Within code h (initialRegisters [.pointer key, .pointer tree]) (code lookup)
        (pointerOutput result.value) result.heap (100 * result.trace.length))
    {h : Heap} {key tree : Ptr} {result : Run (Option Bool)}
    (he : Pointer.LookupEmptyEval h key tree result) :
    Within code h (initialRegisters [.pointer key, .pointer tree]) (lookupEmptyBody lookup)
      (flagOutput result.value) result.heap (100 * result.trace.length) := by
  cases he with
  | @inspect items looked checked hlook hfound hcheck =>
    have hc := compileLookup hlook
    rw [hfound] at hc
    have hi := emptyListEval_code code hcheck
      (bindResults (initialRegisters [.pointer key, .pointer tree]) [2] [.pointer items])
      (by simp [bindResults])
    have all := Within.call (procedure := lookup) (arguments := [r 0, r 1])
      (results := [2]) (by simpa [r, values, Atom.eval, initialRegisters, pointerOutput] using hc) hi
    apply all.mono
    cases hcheck <;> simp [sequenceRuns, readBefore, Program.load] <;> omega

end WeightedMIS.EfficientSearch.RegisterCode
