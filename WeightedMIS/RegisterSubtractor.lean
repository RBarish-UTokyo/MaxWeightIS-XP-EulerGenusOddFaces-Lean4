module

public import WeightedMIS.RegisterComplement

/-! # Closed binary subtraction from complement and ripple-carry addition -/

@[expose] public section

namespace WeightedMIS.RegisterSubtractor

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

/-- The procedure invokes bitwise complement and then adds with initial carry
one. Both calls are fixed finite syntax. -/
def subtractorBody (complement add : Fin p) : Command p :=
  .call complement [.register 1] [3]
    (.call add [.register 0, .register 3, .flag true] [4, 5]
      (.ret [.register 4, .register 5]))

theorem compiled (code : Code p) (complement add : Fin p)
    (hc : code complement = RegisterComplement.complementBody complement)
    (ha : code add = RegisterAdder.adderBody add)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits n}
    (hap : BitsAt h ap a) (hbp : BitsAt h bp b) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (Bits.subtract a b).1 ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp])
        (subtractorBody complement add) [.pointer result, .flag (Bits.subtract a b).2.1]
        out (137 * n + 58) := by
  obtain ⟨mid, cp, hext, hmid, hcomp, hlen, hce⟩ :=
    RegisterComplement.compiled code complement hc hh hbp
  have hapa := hap.mono hext
  let r := addCarryPointer n ap cp true mid
  have hrs := addCarryPointer_refines hmid hapa hcomp true
  have hre := addCarryPointer_eval hmid hapa hcomp true
  have hcompiled := RegisterAdder.compiled code add ha hre
  change Within code mid (initialRegisters [.pointer ap, .pointer cp, .flag true])
    (code add) [.pointer r.value.1, .flag r.value.2] r.heap (10 * r.trace.length) at hcompiled
  have hrlen : r.trace.length = 11 * n + 3 := hrs.2.2.2
  rw [hrlen] at hcompiled
  refine ⟨r.heap, r.value.1, hext.trans hrs.1.1, hrs.1.2.1, ?_, ?_⟩
  · simpa [Bits.subtract] using hrs.2.1
  · have hcarry : r.value.2 = (Bits.subtract a b).2.1 := by
      simpa [Bits.subtract] using hrs.2.2.1
    rw [← hcarry]
    let regs := initialRegisters [Value.pointer ap, .pointer bp]
    let first := bindResults regs [3] [Value.pointer cp]
    let second := bindResults first [4, 5] [Value.pointer r.value.1, .flag r.value.2]
    have last : Within code r.heap second (.ret [.register 4, .register 5])
        [.pointer r.value.1, .flag r.value.2] r.heap 5 := by
      simpa [values, Atom.eval, second, bindResults] using
        Within.ret code r.heap second [.register 4, .register 5]
    have hargs2 : values first [.register 0, .register 3, .flag true] =
        [.pointer ap, .pointer cp, .flag true] := by
      simp [first, regs, bindResults, initialRegisters, values, Atom.eval]
    have hcall2 := Within.call (procedure := add)
      (arguments := [.register 0, .register 3, .flag true]) (results := [4, 5])
      (regs := first) (returned := [.pointer r.value.1, .flag r.value.2])
      (by simpa only [hargs2] using hcompiled) last
    have hargs1 : values regs [.register 1] = [.pointer bp] := by
      simp [regs, initialRegisters, values, Atom.eval]
    have hcall1 := Within.call (procedure := complement) (arguments := [.register 1])
      (results := [3]) (regs := regs) (returned := [.pointer cp])
      (by simpa only [hargs1] using hce) hcall2
    convert hcall1 using 1 <;> first | rfl | simp only [List.length_cons, List.length_nil]; omega

end WeightedMIS.RegisterSubtractor
