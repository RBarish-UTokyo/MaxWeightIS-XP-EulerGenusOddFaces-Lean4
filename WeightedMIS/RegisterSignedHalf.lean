module

public import WeightedMIS.RegisterPotentialStep

/-! # Exact halving of an even signed binary integer -/

@[expose] public section

namespace WeightedMIS.RegisterSignedHalf

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.RegisterPotentialStep

def half {n : ℕ} (a : Word n) : Word n := (a.1, RegisterHalve.halve a.2)

/-- The parity equation is precisely the one supplied by feasible odd-row
recovery; no negative-odd rounding convention is silently assumed. -/
theorem half_value {n : ℕ} (a : Word n) (z : ℤ) (heven : value a = 2 * z) :
    value (half a) = z := by
  have hv := RegisterHalve.halve_value a.2
  cases hs : a.1 <;> simp [value, half, BinaryRational.signed, hs, hv] at heven ⊢ <;> omega

theorem half_div {n : ℕ} (a : Word n) (heven : Even (value a)) :
    value (half a) = value a / 2 := by
  obtain ⟨z, hz⟩ := heven
  have h2 : value a = 2 * z := by omega
  rw [half_value a z h2, h2]
  omega

variable {p : ℕ}

def halfBody (shift : Fin p) : Command p :=
  .call shift [.register 1, .flag false] [2, 3] (.ret [.register 0, .register 2])

theorem compiled (code : Code p) (shift : Fin p)
    (hshift : code shift = RegisterHalve.shiftBody shift)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap : Ptr} {a : Word n}
    (ha : BitsAt h ap a.2) :
    ∃ out result, Extends h out ∧ Valid out ∧ BitsAt out result (half a).2 ∧
      Within code h (initialRegisters [.flag a.1, .pointer ap]) (halfBody shift)
        [.flag (half a).1, .pointer result] out (28 * n + 25) := by
  obtain ⟨out, result, hx, hv, hr, hshifted⟩ := RegisterHalve.shift_compiled code shift hshift hh ha false
  let regs := initialRegisters [Value.flag a.1, .pointer ap]
  let done := bindResults regs [2, 3] [Value.pointer result, .flag (RegisterHalve.shiftRight false a.2).2]
  have last : Within code out done (.ret [.register 0, .register 2])
      [.flag a.1, .pointer result] out 5 := by
    simpa [done, regs, initialRegisters, bindResults, values, Atom.eval] using
      Within.ret code out done [.register 0, .register 2]
  have args : values regs [.register 1, .flag false] = [.pointer ap, .flag false] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have call := Within.call (procedure := shift) (regs := regs)
    (arguments := [.register 1, .flag false]) (results := [2, 3])
    (by simpa only [args] using hshifted) last
  exact ⟨out, result, hx, hv, hr, call.mono (by simp; omega)⟩

end WeightedMIS.RegisterSignedHalf
