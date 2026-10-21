module

public import WeightedMIS.EfficientSearchCodeFresh

/-! # Compositional register continuations for the search loop -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.RegisterCode

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine

variable {p : ℕ} {code : Code p}

def popOutput (original : Ptr) : PopValue → List Value
  | none => [.flag false, .pointer 0, .pointer 0, .pointer original]
  | some (key, a, tree) => [.flag true, .pointer key, .pointer a, .pointer tree]

def popRegs (graph queue settled distance candidate tail : Ptr) : Registers :=
  bindResults (initialRegisters [.pointer graph, .pointer queue, .pointer settled]) [3, 4, 5, 6]
    [.flag true, .pointer distance, .pointer candidate, .pointer tail]

def readRegs (graph queue settled distance candidate tail vertex path : Ptr) : Registers :=
  bindResults (popRegs graph queue settled distance candidate tail) [7, 8] [.pointer vertex, .pointer path]

def knownRegs (graph queue settled distance candidate tail vertex path : Ptr) (empty : Bool) : Registers :=
  bindResults (readRegs graph queue settled distance candidate tail vertex path) [9] [.flag empty]

theorem searchTail_compile {self : Fin p} {h final : Heap} {regs : Registers}
    {graph queue settled outQueue outSettled : Ptr} {status : Bool} {queueAtom settledAtom : Atom} {budget : ℕ}
    (h0 : regs 0 = .pointer graph) (hq : queueAtom.eval regs = .pointer queue)
    (hs : settledAtom.eval regs = .pointer settled)
    (body : Within code h (initialRegisters [.pointer graph, .pointer queue, .pointer settled])
      (code self) [.flag status, .pointer outQueue, .pointer outSettled] final budget) :
    Within code h regs (searchTail self queueAtom settledAtom)
      [.flag status, .pointer outQueue, .pointer outSettled] final (budget + 14) := by
  have hret : Within code final
      (bindResults regs [13, 14, 15] [.flag status, .pointer outQueue, .pointer outSettled])
      (.ret [r 13, r 14, r 15]) [.flag status, .pointer outQueue, .pointer outSettled] final 7 := by
    simpa [bindResults, r, values, Atom.eval, Function.update_apply] using Within.ret code final
      (bindResults regs [13, 14, 15] [.flag status, .pointer outQueue, .pointer outSettled]) [r 13, r 14, r 15]
  have hargs : values regs [r 0, queueAtom, settledAtom] =
      [.pointer graph, .pointer queue, .pointer settled] := by
    change [regs 0, queueAtom.eval regs, settledAtom.eval regs] = _
    rw [h0, hq, hs]
  have hc := Within.call (regs := regs) (procedure := self)
    (arguments := [r 0, queueAtom, settledAtom]) (results := [13, 14, 15])
    (by simpa only [hargs] using body) hret
  convert hc using 1 <;> simp [searchTail] <;> omega

theorem search_found_prefix {pop read lookupEmpty fresh self : Fin p}
    {h poppedHeap readHeap knownHeap final : Heap}
    {graph queue settled distance candidate tail vertex path : Ptr} {empty : Bool}
    {outputs : List Value} {popBudget readBudget knownBudget restBudget : ℕ}
    (popCall : Within code h (initialRegisters [.pointer queue]) (code pop)
      [.flag true, .pointer distance, .pointer candidate, .pointer tail] poppedHeap popBudget)
    (readCall : Within code poppedHeap (initialRegisters [.pointer candidate]) (code read)
      [.pointer vertex, .pointer path] readHeap readBudget)
    (knownCall : Within code readHeap (initialRegisters [.pointer vertex, .pointer settled]) (code lookupEmpty)
      [.flag empty] knownHeap knownBudget)
    (rest : Within code knownHeap (knownRegs graph queue settled distance candidate tail vertex path empty)
      (if empty then freshSearchBody fresh self else searchTail self (r 6) (r 2)) outputs final restBudget) :
    Within code h (initialRegisters [.pointer graph, .pointer queue, .pointer settled])
      (searchBody pop read lookupEmpty fresh self) outputs final
      (popBudget + readBudget + knownBudget + restBudget + 17) := by
  have hb := Within.branch (regs := knownRegs graph queue settled distance candidate tail vertex path empty)
    (test := r 9) (b := empty)
    (by simp [knownRegs, r, Atom.eval, bindResults]) rest
  have hkc := Within.call (regs := readRegs graph queue settled distance candidate tail vertex path)
    (procedure := lookupEmpty) (arguments := [r 7, r 2]) (results := [9])
    (by simpa [readRegs, popRegs, r, values, Atom.eval, initialRegisters, bindResults, Function.update_apply]
        using knownCall) hb
  have hrc := Within.call (regs := popRegs graph queue settled distance candidate tail)
    (procedure := read) (arguments := [r 5]) (results := [7, 8])
    (by simpa [popRegs, r, values, Atom.eval, initialRegisters, bindResults, Function.update_apply]
        using readCall) hkc
  have hbpop := Within.branch (regs := popRegs graph queue settled distance candidate tail)
    (test := r 3) (b := true) (yes := foundSearchBody read lookupEmpty fresh self)
    (no := .ret [.flag false, r 1, r 2])
    (by simp [popRegs, r, Atom.eval, bindResults]) (by simpa [foundSearchBody] using hrc)
  have hpc := Within.call (regs := initialRegisters [.pointer graph, .pointer queue, .pointer settled])
    (procedure := pop) (arguments := [r 1]) (results := [3, 4, 5, 6])
    (by simpa [r, values, Atom.eval, initialRegisters] using popCall) hbpop
  convert hpc using 1 <;> simp [searchBody] <;> omega

end WeightedMIS.EfficientSearch.RegisterCode
