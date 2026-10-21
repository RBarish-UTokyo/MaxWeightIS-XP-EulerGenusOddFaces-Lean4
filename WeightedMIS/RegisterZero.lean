module

public import WeightedMIS.RegisterShift

/-! # Constructing a zero word by following a represented word's actual shape -/

@[expose] public section

namespace WeightedMIS.RegisterZero

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def zeroBody (self : Fin p) : Command p :=
  .load (.register 0) 3 15 4 (RegisterAdder.nilBitCases
    (.ret [.register 0])
    (.call self [.register 3] [7]
      (.allocate 9 (.bit (.flag false) (.register 7)) (.ret [.register 9]))))

theorem compiled (code : Code p) (self : Fin p) (body : code self = zeroBody self)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap : Ptr} {a : Bits n} (ha : BitsAt h ap a) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (Bits.zero n) ∧ out.length = h.length + n ∧
      Within code h (initialRegisters [.pointer ap]) (code self)
        [.pointer result] out (24 * n + 13) := by
  induction a generalizing h ap with
  | nil =>
    cases ha with
    | nil hac =>
      refine ⟨h, ap, .refl h, hh, .nil hac, by simp, ?_⟩
      rw [body]
      let regs := initialRegisters [Value.pointer ap]
      let loaded := loadRegisters regs 3 15 4 Cell.nil
      have last : Within code h loaded (.ret [.register 0]) [.pointer ap] h 3 := by
        simpa [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters] using
          Within.ret code h loaded [.register 0]
      exact Within.load (address := .register 0) (first := 3) (second := 15) (bit := 4)
        (branches := RegisterAdder.nilBitCases (.ret [.register 0])
          (.call self [.register 3] [7]
            (.allocate 9 (.bit (.flag false) (.register 7)) (.ret [.register 9]))))
        (by simp [Atom.eval, regs, initialRegisters]) hac last
  | @cons n bit tail ih =>
    cases ha with
    | @cons _ atail _ _ _ hac hat =>
      obtain ⟨mid, tp, hext, hvalid, hrep, hlen, hchild⟩ := ih hh hat
      have alloc := allocate_bit hvalid false hrep
      refine ⟨mid ++ [.bit false tp], mid.length, hext.trans alloc.1.1,
        alloc.1.2.1, alloc.2, ?_, ?_⟩
      · simp [hlen, Nat.add_assoc]
      · rw [body]
        let regs := initialRegisters [Value.pointer ap]
        let loaded := loadRegisters regs 3 15 4 (.bit bit atail)
        let ready := bindResults loaded [7] [Value.pointer tp]
        have last : Within code (mid ++ [.bit false tp])
            (Function.update ready 9 (.pointer mid.length)) (.ret [.register 9])
            [.pointer mid.length] (mid ++ [.bit false tp]) 3 := by
          simpa [values, Atom.eval] using Within.ret code (mid ++ [.bit false tp])
            (Function.update ready 9 (.pointer mid.length)) [.register 9]
        have halloc := Within.allocate (dst := 9) (expr := .bit (.flag false) (.register 7))
          (by simp [CellExpr.eval, Atom.eval, ready, bindResults, Value.asFlag, Value.asPointer]) last
        have hargs : values loaded [.register 3] = [.pointer atail] := by
          simp [values, Atom.eval, loaded, loadRegisters, decoded]
        have hcall := Within.call (procedure := self) (arguments := [.register 3])
          (results := [7]) (regs := loaded) (by simpa only [hargs] using hchild) halloc
        have hload := Within.load (address := .register 0) (first := 3) (second := 15) (bit := 4)
          (branches := RegisterAdder.nilBitCases (.ret [.register 0])
            (.call self [.register 3] [7]
              (.allocate 9 (.bit (.flag false) (.register 7)) (.ret [.register 9]))))
          (by simp [Atom.eval, regs, initialRegisters]) hac hcall
        exact hload.mono (by simp [CellExpr.args]; omega)

end WeightedMIS.RegisterZero
