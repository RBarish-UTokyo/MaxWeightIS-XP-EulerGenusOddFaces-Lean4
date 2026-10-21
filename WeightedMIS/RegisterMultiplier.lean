module

public import WeightedMIS.RegisterShift
public import WeightedMIS.RegisterZero

/-!
# Fixed finite multiplication code

Horner multiplication reads each multiplier bit, shifts the represented
accumulator, conditionally adds the multiplicand, and recurses on the actual
tail. The program uses only the already compiled shift and Boolean adder.
-/

@[expose] public section

namespace WeightedMIS.RegisterMultiplier

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def recur (self : Fin p) (acc : Atom) : Command p :=
  .call self [.register 0, .register 3, acc] [8] (.ret [.register 8])

def afterShift (self add : Fin p) : Command p :=
  .branch (.register 4)
    (.call add [.register 5, .register 0, .flag false] [6, 7] (recur self (.register 6)))
    (recur self (.register 5))

def multiplyAccBody (self shift add : Fin p) : Command p :=
  .load (.register 1) 3 15 4 (RegisterAdder.nilBitCases
    (.ret [.register 2])
    (.call shift [.register 2, .flag false] [5] (afterShift self add)))

theorem recur_compiled (code : Code p) (self : Fin p) (acc : Atom)
    {h out : Heap} {regs : Registers} {ap bp cp rp : Ptr} {budget : ℕ}
    (ha : regs 0 = .pointer ap) (hb : regs 3 = .pointer bp)
    (hc : acc.eval regs = .pointer cp)
    (child : Within code h (initialRegisters [.pointer ap, .pointer bp, .pointer cp])
      (code self) [.pointer rp] out budget) :
    Within code h regs (recur self acc) [.pointer rp] out (budget + 10) := by
  have last : Within code out (bindResults regs [8] [.pointer rp])
      (.ret [.register 8]) [.pointer rp] out 3 := by
    simpa [values, Atom.eval, bindResults] using
      Within.ret code out (bindResults regs [8] [.pointer rp]) [.register 8]
  have hargs : values regs [.register 0, .register 3, acc] =
      [.pointer ap, .pointer bp, .pointer cp] := by
    simp only [values, List.map_cons, List.map_nil, Atom.eval, ha, hb]
    exact congrArg (fun v => [Value.pointer ap, .pointer bp, v]) hc
  have call := Within.call (procedure := self)
    (arguments := [.register 0, .register 3, acc]) (results := [8])
    (by simpa only [hargs] using child) last
  exact call.mono (by simp; omega)

theorem shiftIn_false {n : ℕ} (a : Bits n) : Bits.shiftIn a false = Bits.shift a := by
  cases a <;> rfl

theorem compiled (code : Code p) (self shift snoc add : Fin p)
    (hm : code self = multiplyAccBody self shift add)
    (hs : code shift = RegisterShift.shiftInBody snoc)
    (hn : code snoc = RegisterShift.snocBody snoc)
    (ha : code add = RegisterAdder.adderBody add)
    {n m : ℕ} {h : Heap} (hh : Valid h) {ap bp cp : Ptr}
    {a : Bits n} {b : Bits m} {acc : Bits n}
    (hap : BitsAt h ap a) (hbp : BitsAt h bp b) (hcp : BitsAt h cp acc) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (Bits.multiplyAcc a b acc).1 ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp, .pointer cp])
        (code self) [.pointer result] out ((136 * n + 80) * m + 13) := by
  induction b generalizing h ap bp cp acc with
  | nil =>
    cases hbp with
    | nil hbc =>
      refine ⟨h, cp, .refl h, hh, hcp, ?_⟩
      rw [hm]
      let regs := initialRegisters [Value.pointer ap, .pointer bp, .pointer cp]
      have last : Within code h (loadRegisters regs 3 15 4 .nil)
          (.ret [.register 2]) [.pointer cp] h 3 := by
        simpa [values, Atom.eval, regs, loadRegisters, decoded, initialRegisters] using
          Within.ret code h (loadRegisters regs 3 15 4 .nil) [.register 2]
      exact Within.load (address := .register 1) (first := 3) (second := 15) (bit := 4)
        (branches := RegisterAdder.nilBitCases (.ret [.register 2])
          (.call shift [.register 2, .flag false] [5] (afterShift self add)))
        (by simp [Atom.eval, regs, initialRegisters]) hbc last
  | @cons m bit tail ih =>
    cases hbp with
    | @cons _ btail _ _ _ hbc hbt =>
      obtain ⟨mid, sp, ext, valid, rep, cells, shiftRun⟩ :=
        RegisterShift.shiftIn_compiled code snoc hn hh hcp false
      rw [shiftIn_false] at rep
      let regs := initialRegisters [Value.pointer ap, .pointer bp, .pointer cp]
      let loaded := loadRegisters regs 3 15 4 (.bit bit btail)
      let shifted := bindResults loaded [5] [Value.pointer sp]
      have hargs : values loaded [.register 2, .flag false] =
          [.pointer cp, .flag false] := by
        simp [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters]
      have shiftCall : Within code h (initialRegisters (values loaded [.register 2, .flag false]))
          (code shift) [.pointer sp] mid (26 * n + 13) := by
        simpa only [hargs, hs] using shiftRun
      have hshift0 : shifted 0 = .pointer ap := by
        simp [shifted, loaded, regs, bindResults, loadRegisters, decoded, initialRegisters]
      have hshift3 : shifted 3 = .pointer btail := by
        simp [shifted, loaded, regs, bindResults, loadRegisters, decoded, initialRegisters]
      have hshift4 : shifted 4 = .flag bit := by
        simp [shifted, loaded, regs, bindResults, loadRegisters, decoded, initialRegisters]
      have hshift5 : shifted 5 = .pointer sp := by simp [shifted, bindResults]
      have continuation : ∃ out : Heap, ∃ result : Ptr,
          Extends mid out ∧ Valid out ∧
          BitsAt out result (Bits.multiplyAcc a (.cons bit tail) acc).1 ∧
          Within code mid shifted (afterShift self add) [.pointer result] out
            ((136 * n + 80) * m + 110 * n + 63) := by
        cases bit with
        | false =>
          obtain ⟨out, result, hext, hvalid, hresult, hrun⟩ :=
            ih valid (hap.mono ext) (hbt.mono ext) rep
          have recurRun := recur_compiled code self (.register 5)
            hshift0 hshift3 (by simpa [Atom.eval] using hshift5) hrun
          have branchRun := Within.branch (test := .register 4) (b := false)
            (yes := .call add [.register 5, .register 0, .flag false] [6, 7]
              (recur self (.register 6)))
            (by simpa [Atom.eval] using hshift4) recurRun
          refine ⟨out, result, hext, hvalid, ?_, branchRun.mono (by omega)⟩
          simpa [Bits.multiplyAcc] using hresult
        | true =>
          let added := addCarryPointer n sp ap false mid
          have asafe := addCarryPointer_refines valid rep (hap.mono ext) false
          have aeval := addCarryPointer_eval valid rep (hap.mono ext) false
          have arun := RegisterAdder.compiled code add ha aeval
          have alen : added.trace.length = 11 * n + 3 := asafe.2.2.2
          change Within code mid (initialRegisters [.pointer sp, .pointer ap, .flag false])
            (code add) [.pointer added.value.1, .flag added.value.2]
            added.heap (10 * added.trace.length) at arun
          rw [alen] at arun
          obtain ⟨out, result, hext, hvalid, hresult, hrun⟩ :=
            ih asafe.1.2.1 ((hap.mono ext).mono asafe.1.1)
              ((hbt.mono ext).mono asafe.1.1) asafe.2.1
          let ready := bindResults shifted [6, 7]
            [Value.pointer added.value.1, .flag added.value.2]
          have hready0 : ready 0 = .pointer ap := by simp [ready, bindResults, hshift0]
          have hready3 : ready 3 = .pointer btail := by simp [ready, bindResults, hshift3]
          have hready6 : ready 6 = .pointer added.value.1 := by simp [ready, bindResults]
          have recurRun := recur_compiled code self (.register 6)
            hready0 hready3 (by simpa [Atom.eval] using hready6) hrun
          have aargs : values shifted [.register 5, .register 0, .flag false] =
              [.pointer sp, .pointer ap, .flag false] := by simp [values, Atom.eval, hshift0, hshift5]
          have addCall := Within.call (procedure := add)
            (arguments := [.register 5, .register 0, .flag false]) (results := [6, 7])
            (regs := shifted) (by simpa only [aargs] using arun) recurRun
          have branchRun := Within.branch (test := .register 4) (b := true)
            (no := recur self (.register 5)) (by simpa [Atom.eval] using hshift4) addCall
          refine ⟨out, result, asafe.1.1.trans hext, hvalid, ?_, ?_⟩
          · simpa [Bits.multiplyAcc, Bits.add] using hresult
          · exact branchRun.mono (by simp; omega)
      obtain ⟨out, result, hext, hvalid, hresult, hrest⟩ := continuation
      have call := Within.call (procedure := shift) (arguments := [.register 2, .flag false])
        (results := [5]) shiftCall hrest
      have load := Within.load (address := .register 1) (first := 3) (second := 15) (bit := 4)
        (branches := RegisterAdder.nilBitCases (.ret [.register 2])
          (.call shift [.register 2, .flag false] [5] (afterShift self add)))
        (by simp [Atom.eval, regs, initialRegisters]) hbc call
      refine ⟨out, result, ext.trans hext, hvalid, hresult, ?_⟩
      rw [hm]
      exact load.mono (by simp [Nat.mul_add]; omega)

/-- The public multiplication procedure constructs its own zero accumulator. -/
def multiplyBody (zero mul : Fin p) : Command p :=
  .call zero [.register 0] [3]
    (.call mul [.register 0, .register 1, .register 3] [4] (.ret [.register 4]))

theorem multiply_compiled (code : Code p) (zero mul shift snoc add : Fin p)
    (hz : code zero = RegisterZero.zeroBody zero)
    (hm : code mul = multiplyAccBody mul shift add)
    (hs : code shift = RegisterShift.shiftInBody snoc)
    (hn : code snoc = RegisterShift.snocBody snoc)
    (ha : code add = RegisterAdder.adderBody add)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits n}
    (hap : BitsAt h ap a) (hbp : BitsAt h bp b) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (Bits.multiply a b).1 ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp])
        (multiplyBody zero mul) [.pointer result] out
        ((136 * n + 80) * n + 24 * n + 39) := by
  obtain ⟨mid, zp, ext, valid, rep, cells, zeroRun⟩ := RegisterZero.compiled code zero hz hh hap
  obtain ⟨out, result, hext, hvalid, hresult, hrun⟩ :=
    compiled code mul shift snoc add hm hs hn ha valid (hap.mono ext) (hbp.mono ext) rep
  refine ⟨out, result, ext.trans hext, hvalid, hresult, ?_⟩
  let regs := initialRegisters [Value.pointer ap, .pointer bp]
  let first := bindResults regs [3] [Value.pointer zp]
  let second := bindResults first [4] [Value.pointer result]
  have last : Within code out second (.ret [.register 4]) [.pointer result] out 3 := by
    simpa [values, Atom.eval, second, bindResults] using Within.ret code out second [.register 4]
  have margs : values first [.register 0, .register 1, .register 3] =
      [.pointer ap, .pointer bp, .pointer zp] := by
    simp [values, Atom.eval, first, regs, bindResults, initialRegisters]
  have mcall := Within.call (procedure := mul)
    (arguments := [.register 0, .register 1, .register 3]) (results := [4])
    (regs := first) (by simpa only [margs] using hrun) last
  have zargs : values regs [.register 0] = [.pointer ap] := by
    simp [values, Atom.eval, regs, initialRegisters]
  have zcall := Within.call (procedure := zero) (arguments := [.register 0]) (results := [3])
    (regs := regs) (by simpa only [zargs] using zeroRun) mcall
  exact zcall.mono (by simp; omega)

end WeightedMIS.RegisterMultiplier
