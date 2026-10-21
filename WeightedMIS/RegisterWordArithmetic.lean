module

public import WeightedMIS.RegisterAdder
public import WeightedMIS.RegisterMultiplier

/-! # Representation interfaces for the compiled word arithmetic bodies -/

@[expose] public section

namespace WeightedMIS.RegisterWordArithmetic

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch

variable {p n : ℕ}

theorem add_compiled (code : Code p) (add : Fin p)
    (body : code add = RegisterAdder.adderBody add)
    {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits n}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (Bits.add a b).1 ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp, .flag false]) (code add)
        [.pointer result, .flag (Bits.add a b).2.1] out (110 * n + 30) := by
  let output := addCarryPointer n ap bp false h
  have safe := addCarryPointer_refines hh ha hb false
  have eval := addCarryPointer_eval hh ha hb false
  have run := RegisterAdder.compiled code add body eval
  change Within code h (initialRegisters [.pointer ap, .pointer bp, .flag false]) (code add)
    [.pointer output.value.1, .flag output.value.2] output.heap (10 * output.trace.length) at run
  have len : output.trace.length = 11 * n + 3 := safe.2.2.2
  have bit : output.value.2 = (Bits.add a b).2.1 := safe.2.2.1
  rw [len, bit] at run
  exact ⟨output.heap, output.value.1, safe.1.1, safe.1.2.1, safe.2.1,
    run.mono (by omega)⟩

end WeightedMIS.RegisterWordArithmetic
