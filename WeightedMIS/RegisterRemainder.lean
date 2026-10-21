module

public import WeightedMIS.RegisterDivisionWrapper
public import WeightedMIS.BinaryGCD

/-! # Original-width remainder from closed binary division -/

@[expose] public section

namespace WeightedMIS.RegisterDivision

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

/-- Procedure identifiers for the concrete binary division implementation. -/
structure Procedures (p : ℕ) where
  zero : Fin p
  cmp : Fin p
  aux : Fin p
  shift : Fin p
  snoc : Fin p
  sub : Fin p
  complement : Fin p
  add : Fin p
  divide : Fin p

/-- Every referenced identifier contains its explicitly specified finite body. -/
def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  code d.zero = RegisterZero.zeroBody d.zero ∧
  code d.cmp = RegisterComparator.comparatorBody d.cmp ∧
  code d.aux = auxBody d.aux d.shift d.cmp d.sub ∧
  code d.shift = RegisterShift.shiftInBody d.snoc ∧
  code d.snoc = RegisterShift.snocBody d.snoc ∧
  code d.sub = RegisterSubtractor.subtractorBody d.complement d.add ∧
  code d.complement = RegisterComplement.complementBody d.complement ∧
  code d.add = RegisterAdder.adderBody d.add ∧
  code d.divide = divideBody d.zero d.cmp d.aux

theorem remainder_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap dp : Ptr} {a den : Bits n}
    (ha : BitsAt h ap a) (hd : BitsAt h dp den) :
    ∃ out : Heap, ∃ rp : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out rp (Bits.remainder a den).1 ∧
      Within code h (initialRegisters [.pointer ap, .pointer dp]) (remainderBody d.divide)
        [.pointer rp] out (400 * (n + 1) ^ 2 + 18) := by
  rcases hm with ⟨hz, hc, hx, hs, hsn, hsu, hco, had, hdv⟩
  obtain ⟨out, qp, rp, hext, hvalid, hqr, hrr, hde⟩ :=
    divide_compiled code d.zero d.cmp d.aux d.shift d.snoc d.sub d.complement d.add
      hz hc hx hs hsn hsu hco had hh ha hd
  rw [← hdv] at hde
  cases heq : (Bits.divide a den).2.1 with
  | cons bit tail =>
      rw [heq] at hrr
      cases hrr with
      | @cons _ tp _ _ _ hcell htail =>
        refine ⟨out, tp, hext, hvalid, ?_, ?_⟩
        · simpa [Bits.remainder, heq, Bits.low] using htail
        · let regs := initialRegisters [Value.pointer ap, .pointer dp]
          let returned := bindResults regs [2, 3] [Value.pointer qp, .pointer rp]
          let loaded := loadRegisters returned 4 15 5 (.bit bit tp)
          have last : Within code out loaded (.ret [.register 4]) [.pointer tp] out 3 := by
            simpa [loaded, loadRegisters, decoded, values, Atom.eval] using
              Within.ret code out loaded [.register 4]
          have hload := Within.load (address := .register 3) (first := 4) (second := 15) (bit := 5)
            (branches := RegisterAdder.nilBitCases .fail (.ret [.register 4]))
            (by simp [Atom.eval, returned, bindResults]) hcell last
          have hargs : values regs [.register 0, .register 1] = [.pointer ap, .pointer dp] := by
            simp [regs, initialRegisters, values, Atom.eval]
          have hcall := Within.call (procedure := d.divide) (arguments := [.register 0, .register 1])
            (results := [2, 3]) (regs := regs) (returned := [.pointer qp, .pointer rp])
            (by simpa only [hargs] using hde) hload
          exact hcall.mono (by simp only [List.length_cons, List.length_nil]; omega)

end WeightedMIS.RegisterDivision
