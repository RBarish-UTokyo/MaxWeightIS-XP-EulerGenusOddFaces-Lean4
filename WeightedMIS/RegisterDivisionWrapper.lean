module

public import WeightedMIS.RegisterDivision
public import WeightedMIS.RegisterZero

/-! # Complete fixed-width binary division in closed register code -/

@[expose] public section

namespace WeightedMIS.RegisterDivision

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def nonzeroBody (aux : Fin p) : Command p :=
  .allocate 5 (.bit (.flag false) (.register 1))
    (.allocate 6 (.bit (.flag false) (.register 2))
      (.call aux [.register 5, .register 0, .register 6] [7, 8]
        (.ret [.register 7, .register 8])))

def zeroBody : Command p :=
  .allocate 5 (.bit (.flag false) (.register 0)) (.ret [.register 2, .register 5])

def divideBody (zero cmp aux : Fin p) : Command p :=
  .call zero [.register 1] [2]
    (.call cmp [.register 1, .register 2] [3, 4]
      (.branch (.register 4) zeroBody (nonzeroBody aux)))

theorem zero_within (code : Code p) (h : Heap) (regs : Registers) (ap zp : Ptr)
    (ha : regs 0 = .pointer ap) (hz : regs 2 = .pointer zp) :
    Within code h regs zeroBody [.pointer zp, .pointer h.length]
      (h ++ [.bit false ap]) 13 := by
  have last : Within code (h ++ [.bit false ap])
      (Function.update regs 5 (.pointer h.length)) (.ret [.register 2, .register 5])
      [.pointer zp, .pointer h.length] (h ++ [.bit false ap]) 5 := by
    simpa [values, Atom.eval, hz] using
      Within.ret code (h ++ [.bit false ap])
        (Function.update regs 5 (.pointer h.length)) [.register 2, .register 5]
  have halloc := Within.allocate (dst := 5) (expr := .bit (.flag false) (.register 0))
    (by simp [CellExpr.eval, Atom.eval, ha, Value.asPointer, Value.asFlag]) last
  simpa [zeroBody, CellExpr.args] using halloc

/-- Complete long division, including the zero-divisor convention and actual
construction of the extra-bit remainder workspace. -/
theorem divide_compiled (code : Code p) (zero cmp aux shift snoc sub complement add : Fin p)
    (hzero : code zero = RegisterZero.zeroBody zero)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (haux : code aux = auxBody aux shift cmp sub)
    (hshift : code shift = RegisterShift.shiftInBody snoc)
    (hsnoc : code snoc = RegisterShift.snocBody snoc)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hcomp : code complement = RegisterComplement.complementBody complement)
    (hadd : code add = RegisterAdder.adderBody add)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap dp : Ptr} {a den : Bits n}
    (ha : BitsAt h ap a) (hd : BitsAt h dp den) :
    ∃ out : Heap, ∃ qp rp : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out qp (Bits.divide a den).1 ∧ BitsAt out rp (Bits.divide a den).2.1 ∧
      Within code h (initialRegisters [.pointer ap, .pointer dp]) (divideBody zero cmp aux)
        [.pointer qp, .pointer rp] out (400 * (n + 1) ^ 2) := by
  obtain ⟨zh, zp, hzext, hzvalid, hzrep, hzlen, hze⟩ :=
    RegisterZero.compiled code zero hzero hh hd
  have had := ha.mono hzext
  have hdd := hd.mono hzext
  have hce := RegisterComparator.compiled code cmp hcmp hdd hzrep
  let comparison := (Bits.compare den (Bits.zero n)).1
  let regs := initialRegisters [Value.pointer ap, .pointer dp]
  let zeroed := bindResults regs [2] [Value.pointer zp]
  let compared := bindResults zeroed [3, 4] (RegisterComparator.flags comparison)
  have ha0 : compared 0 = .pointer ap := by
    simp [compared, zeroed, regs, bindResults, RegisterComparator.flags, initialRegisters]
  have hd1 : compared 1 = .pointer dp := by
    simp [compared, zeroed, regs, bindResults, RegisterComparator.flags, initialRegisters]
  have hz2 : compared 2 = .pointer zp := by
    simp [compared, zeroed, bindResults, RegisterComparator.flags]
  have hc4 : compared 4 = .flag (decide (comparison = .eq)) := by
    simp [compared, bindResults, RegisterComparator.flags]
  obtain ⟨out, qp, rp, hext, hvalid, hqr, hrr, hbranch⟩ :
      ∃ out : Heap, ∃ qp rp : Ptr, Extends zh out ∧ Valid out ∧
        BitsAt out qp (Bits.divide a den).1 ∧ BitsAt out rp (Bits.divide a den).2.1 ∧
        Within code zh compared (.branch (.register 4) zeroBody (nonzeroBody aux))
          [.pointer qp, .pointer rp] out (200 * (n + 2) * n + 46) := by
    by_cases heq : comparison = .eq
    · have alloc := allocate_bit hzvalid false had
      have hzcode := zero_within code zh compared ap zp ha0 hz2
      have hbr := Within.branch (b := true) (test := .register 4)
        (yes := zeroBody) (no := nonzeroBody aux)
        (by simpa [Atom.eval, heq] using hc4) hzcode
      refine ⟨zh ++ [.bit false ap], zp, zh.length, alloc.1.1, alloc.1.2.1, ?_, ?_,
        hbr.mono (by omega)⟩
      · simpa [Bits.divide, comparison, heq, Program.allocate] using hzrep.mono alloc.1.1
      · simpa [Bits.divide, comparison, heq, Program.allocate] using alloc.2
    · have denAlloc := allocate_bit hzvalid false hdd
      let dh := zh ++ [.bit false dp]
      have hzdh := hzrep.mono denAlloc.1.1
      have zeroAlloc := allocate_bit denAlloc.1.2.1 false hzdh
      let rh := dh ++ [.bit false zp]
      have hadr := had.mono (denAlloc.1.1.trans zeroAlloc.1.1)
      have hddr := denAlloc.2.mono zeroAlloc.1.1
      have hzrr : BitsAt rh dh.length (Bits.zero (n + 1)) := by
        simpa [Bits.zero, Program.allocate, rh, dh] using zeroAlloc.2
      obtain ⟨out, qp, rp, hx, hv, hqr, hrr, child⟩ :=
        aux_compiled code aux shift snoc cmp sub complement add haux hshift hsnoc hcmp hsub hcomp hadd
          zeroAlloc.1.2.1 hddr hadr hzrr
      let denRegs := Function.update compared 5 (Value.pointer zh.length)
      let remRegs := Function.update denRegs 6 (Value.pointer dh.length)
      let ready := bindResults remRegs [7, 8] [Value.pointer qp, .pointer rp]
      have last : Within code out ready (.ret [.register 7, .register 8])
          [.pointer qp, .pointer rp] out 5 := by
        simpa [ready, bindResults, values, Atom.eval] using
          Within.ret code out ready [.register 7, .register 8]
      have hargs : values remRegs [.register 5, .register 0, .register 6] =
          [.pointer zh.length, .pointer ap, .pointer dh.length] := by
        simp [remRegs, denRegs, values, Atom.eval, ha0]
      have hcall := Within.call (procedure := aux)
        (arguments := [.register 5, .register 0, .register 6]) (results := [7, 8])
        (regs := remRegs) (returned := [.pointer qp, .pointer rp])
        (by simpa only [hargs, Program.allocate] using child) last
      have hallocR := Within.allocate (dst := 6) (expr := .bit (.flag false) (.register 2))
        (c := .bit false zp) (regs := denRegs) (h := dh)
        (by simp [CellExpr.eval, Atom.eval, denRegs, hz2, Value.asPointer, Value.asFlag]) hcall
      have hallocD := Within.allocate (dst := 5) (expr := .bit (.flag false) (.register 1))
        (c := .bit false dp) (regs := compared) (h := zh)
        (by simp [CellExpr.eval, Atom.eval, hd1, Value.asPointer, Value.asFlag]) hallocR
      have hbr := Within.branch (b := false) (test := .register 4)
        (yes := zeroBody) (no := nonzeroBody aux)
        (by simpa [Atom.eval, heq] using hc4) hallocD
      refine ⟨out, qp, rp, denAlloc.1.1.trans (zeroAlloc.1.1.trans hx), hv, ?_, ?_, ?_⟩
      · simpa [Bits.divide, comparison, heq, Bits.zero] using hqr
      · simpa [Bits.divide, comparison, heq, Bits.zero] using hrr
      · exact hbr.mono (by simp only [List.length_cons, List.length_nil, CellExpr.args]; nlinarith)
  refine ⟨out, qp, rp, hzext.trans hext, hvalid, hqr, hrr, ?_⟩
  have hargsC : values zeroed [.register 1, .register 2] = [.pointer dp, .pointer zp] := by
    simp [zeroed, regs, bindResults, values, Atom.eval, initialRegisters]
  have hcallC := Within.call (procedure := cmp) (arguments := [.register 1, .register 2])
    (results := [3, 4]) (regs := zeroed) (returned := RegisterComparator.flags comparison)
    (by simpa only [hargsC] using hce) hbranch
  have hargsZ : values regs [.register 1] = [.pointer dp] := by
    simp [regs, values, Atom.eval, initialRegisters]
  have hcallZ := Within.call (procedure := zero) (arguments := [.register 1]) (results := [2])
    (regs := regs) (returned := [.pointer zp]) (by simpa only [hargsZ] using hze) hcallC
  exact hcallZ.mono (by simp only [List.length_cons, List.length_nil]; nlinarith)

/-- Discard the extra leading bit of the returned remainder. -/
def remainderBody (divide : Fin p) : Command p :=
  .call divide [.register 0, .register 1] [2, 3]
    (.load (.register 3) 4 15 5 (RegisterAdder.nilBitCases .fail (.ret [.register 4])))

end WeightedMIS.RegisterDivision
