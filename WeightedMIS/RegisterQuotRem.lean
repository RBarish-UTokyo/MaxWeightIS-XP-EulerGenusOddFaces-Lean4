module

public import WeightedMIS.RegisterRemainder

/-! # Fixed-width quotient and remainder returned together -/

@[expose] public section

namespace WeightedMIS.RegisterQuotRem

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch

variable {p : ℕ}

def body (divide : Fin p) : Command p :=
  .call divide [.register 0, .register 1] [2, 3]
    (.load (.register 3) 4 15 5
      (RegisterAdder.nilBitCases .fail (.ret [.register 2, .register 4])))

theorem compiled (code : Code p) (ids : RegisterDivision.Procedures p)
    (hm : ids.Matches code) {n : ℕ} {h : Heap} (hh : Valid h)
    {ap bp : Ptr} {a b : Bits n} (ha : BitsAt h ap a) (hb : BitsAt h bp b) :
    ∃ out : Heap, ∃ qp rp : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out qp (Bits.divide a b).1 ∧ BitsAt out rp (Bits.remainder a b).1 ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp]) (body ids.divide)
        [.pointer qp, .pointer rp] out (400 * (n + 1) ^ 2 + 20) := by
  obtain ⟨hz, hc, hx, hs, hsn, hsu, hco, had, hdv⟩ := hm
  obtain ⟨out, qp, rp, ext, valid, qAt, rAt, division⟩ :=
    RegisterDivision.divide_compiled code ids.zero ids.cmp ids.aux ids.shift ids.snoc
      ids.sub ids.complement ids.add hz hc hx hs hsn hsu hco had hh ha hb
  rw [← hdv] at division
  cases heq : (Bits.divide a b).2.1 with
  | cons bit tail =>
      rw [heq] at rAt
      cases rAt with
      | @cons _ tp _ _ _ cell tailAt =>
        refine ⟨out, qp, tp, ext, valid, qAt, ?_, ?_⟩
        · simpa [Bits.remainder, heq, Bits.low] using tailAt
        · let regs := initialRegisters [Value.pointer ap, .pointer bp]
          let divided := bindResults regs [2, 3] [Value.pointer qp, .pointer rp]
          let loaded := loadRegisters divided 4 15 5 (.bit bit tp)
          have last : Within code out loaded (.ret [.register 2, .register 4])
              [.pointer qp, .pointer tp] out 5 := by
            simpa [values, Atom.eval, loaded, divided, bindResults, loadRegisters, decoded] using
              Within.ret code out loaded [.register 2, .register 4]
          have load := Within.load (address := .register 3) (first := 4) (second := 15) (bit := 5)
            (branches := RegisterAdder.nilBitCases .fail (.ret [.register 2, .register 4]))
            (by simp [Atom.eval, divided, bindResults]) cell last
          have args : values regs [.register 0, .register 1] = [.pointer ap, .pointer bp] := by
            simp [regs, values, Atom.eval, initialRegisters]
          have call := Within.call (procedure := ids.divide)
            (arguments := [.register 0, .register 1]) (results := [2, 3]) (regs := regs)
            (by simpa only [args] using division) load
          exact call.mono (by simp only [List.length_cons, List.length_nil]; omega)

end WeightedMIS.RegisterQuotRem
