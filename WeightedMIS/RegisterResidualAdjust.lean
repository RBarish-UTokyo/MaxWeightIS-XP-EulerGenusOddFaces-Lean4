module

public import WeightedMIS.RegisterSubtractor
public import WeightedMIS.RegisterWordArithmetic

/-! # Conditional binary residual decrease and reverse-arc increase -/

@[expose] public section

namespace WeightedMIS.RegisterResidualAdjust

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch

variable {p : ℕ}

def adjust {n : ℕ} (r d : Bits n) (forward reverse : Bool) : Bits n :=
  let r' := if forward then (Bits.subtract r d).1 else r
  if reverse then (Bits.add r' d).1 else r'

def increaseBody (add : Fin p) : Command p :=
  .branch (.register 3)
    (.call add [.register 4, .register 1, .flag false] [5, 6] (.ret [.register 5]))
    (.ret [.register 4])

/-- Inputs: residual, scale, forward-membership flag, reverse-membership flag. -/
def adjustBody (sub add : Fin p) : Command p :=
  .branch (.register 2)
    (.call sub [.register 0, .register 1] [4, 5] (increaseBody add))
    (.copy 4 (.register 0) (increaseBody add))

theorem increase_compiled (code : Code p) (add : Fin p)
    (hadd : code add = RegisterAdder.adderBody add)
    {n : ℕ} {h : Heap} (hh : Valid h) (regs : Registers)
    {r d : Bits n} {rp dp : Ptr} (hr : BitsAt h rp r) (hd : BitsAt h dp d)
    (reverse : Bool) (h4 : regs 4 = .pointer rp) (h1 : regs 1 = .pointer dp)
    (h3 : regs 3 = .flag reverse) :
    ∃ out result, Extends h out ∧ Valid out ∧
      BitsAt out result (if reverse then (Bits.add r d).1 else r) ∧
      Within code h regs (increaseBody add) [.pointer result] out (110 * n + 43) := by
  cases reverse
  · refine ⟨h, rp, .refl h, hh, hr, ?_⟩
    have ret : Within code h regs (.ret [.register 4]) [.pointer rp] h 3 := by
      simpa [values, Atom.eval, h4] using Within.ret code h regs [.register 4]
    have br := Within.branch (test := .register 3) (b := false)
      (yes := .call add [.register 4, .register 1, .flag false] [5, 6] (.ret [.register 5]))
      (no := .ret [.register 4]) (by simpa [Atom.eval] using h3) ret
    simpa [increaseBody] using br.mono (b := 110 * n + 43) (by omega)
  · obtain ⟨out, result, he, ho, hres, addRun⟩ :=
      RegisterWordArithmetic.add_compiled code add hadd hh hr hd
    let r1 := bindResults regs [5, 6] [.pointer result, .flag (Bits.add r d).2.1]
    have ret : Within code out r1 (.ret [.register 5]) [.pointer result] out 3 := by
      simpa [r1, bindResults, values, Atom.eval] using Within.ret code out r1 [.register 5]
    have args : values regs [.register 4, .register 1, .flag false] =
        [.pointer rp, .pointer dp, .flag false] := by simp [values, Atom.eval, h4, h1]
    have call := Within.call (procedure := add) (regs := regs)
      (arguments := [.register 4, .register 1, .flag false]) (results := [5, 6])
      (by simpa only [args] using addRun) ret
    have br := Within.branch (test := .register 3) (b := true)
      (yes := .call add [.register 4, .register 1, .flag false] [5, 6] (.ret [.register 5]))
      (no := .ret [.register 4]) (by simpa [Atom.eval] using h3) call
    refine ⟨out, result, he, ho, hres, ?_⟩
    simpa only [increaseBody] using br.mono (b := 110 * n + 43)
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem compiled (code : Code p) (sub complement add : Fin p)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hc : code complement = RegisterComplement.complementBody complement)
    (hadd : code add = RegisterAdder.adderBody add)
    {n : ℕ} {h : Heap} (hh : Valid h) {r d : Bits n} {rp dp : Ptr}
    (hr : BitsAt h rp r) (hd : BitsAt h dp d) (forward reverse : Bool) :
    ∃ out result, Extends h out ∧ Valid out ∧ BitsAt out result (adjust r d forward reverse) ∧
      Within code h (initialRegisters [.pointer rp, .pointer dp, .flag forward, .flag reverse])
        (adjustBody sub add) [.pointer result] out (247 * n + 109) := by
  let regs := initialRegisters [Value.pointer rp, .pointer dp, .flag forward, .flag reverse]
  cases forward
  · let r1 := Function.update regs 4 (.pointer rp)
    obtain ⟨out, result, he, ho, hresult, run⟩ := increase_compiled code add hadd hh r1 hr hd reverse
      (by simp [r1]) (by simp [r1, regs, initialRegisters]) (by simp [r1, regs, initialRegisters])
    have copy := Within.copy (dst := 4) (src := .register 0) (regs := regs)
      (by simpa [regs, initialRegisters, Atom.eval] using run)
    have br := Within.branch (test := .register 2) (b := false)
      (yes := .call sub [.register 0, .register 1] [4, 5] (increaseBody add))
      (no := .copy 4 (.register 0) (increaseBody add))
      (by simp [Atom.eval, regs, initialRegisters]) copy
    refine ⟨out, result, he, ho, ?_, ?_⟩
    · simpa [adjust] using hresult
    · simpa [adjustBody] using br.mono (b := 247 * n + 109) (by omega)
  · obtain ⟨mid, subp, he, hm, hdiff, subRun⟩ := RegisterSubtractor.compiled code complement add hc hadd hh hr hd
    let r1 := bindResults regs [4, 5] [.pointer subp, .flag (Bits.subtract r d).2.1]
    obtain ⟨out, result, he', ho, hresult, run⟩ :=
      increase_compiled code add hadd hm r1 hdiff (hd.mono he) reverse
        (by simp [r1, bindResults])
        (by simp [r1, regs, bindResults, initialRegisters])
        (by simp [r1, regs, bindResults, initialRegisters])
    have args : values regs [.register 0, .register 1] = [.pointer rp, .pointer dp] := by
      simp [regs, initialRegisters, values, Atom.eval]
    have call := Within.call (procedure := sub) (regs := regs)
      (arguments := [.register 0, .register 1]) (results := [4, 5])
      (by simpa only [args, hsub] using subRun) run
    have br := Within.branch (test := .register 2) (b := true)
      (yes := .call sub [.register 0, .register 1] [4, 5] (increaseBody add))
      (no := .copy 4 (.register 0) (increaseBody add))
      (by simp [Atom.eval, regs, initialRegisters]) call
    refine ⟨out, result, he.trans he', ho, ?_, ?_⟩
    · simpa [adjust] using hresult
    · simpa only [adjustBody] using br.mono (b := 247 * n + 109)
        (by simp only [List.length_cons, List.length_nil]; omega)

/-- Underflow and overflow are discharged from the mathematical residual
invariant; the compiled operations then agree with ordinary natural arithmetic. -/
theorem adjust_value {n : ℕ} (r d : Bits n) (forward reverse : Bool)
    (hsub : forward = true → d.value ≤ r.value)
    (hadd : (r.value - if forward then d.value else 0) +
      (if reverse then d.value else 0) < 2 ^ n) :
    (adjust r d forward reverse).value =
      (r.value - if forward then d.value else 0) + (if reverse then d.value else 0) := by
  cases forward <;> cases reverse
  · simp [adjust]
  · simpa [adjust] using (Bits.add_value_of_lt r d (by simpa using hadd)).2
  · simpa [adjust] using (Bits.subtract_value_of_le r d (hsub rfl)).2
  · have hd := (Bits.subtract_value_of_le r d (hsub rfl)).2
    have hb : (Bits.subtract r d).1.value + d.value < 2 ^ n := by simpa [hd] using hadd
    simpa [adjust, hd] using (Bits.add_value_of_lt (Bits.subtract r d).1 d hb).2

end WeightedMIS.RegisterResidualAdjust
