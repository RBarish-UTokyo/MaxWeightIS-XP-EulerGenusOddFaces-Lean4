module

public import WeightedMIS.RegisterZero
public import WeightedMIS.EfficientSearchCodeBounds

/-!
# Binary right shift, halving, and the leading capacity scale

A tag-directed traversal carries one bit from each position to the next. It
returns the bit dropped at the least significant position. The same routine
supports unsigned halving and exact signed division without an arithmetic
host opcode or a numerical loop counter.
-/

@[expose] public section

namespace WeightedMIS.RegisterHalve

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def shiftRight (incoming : Bool) : {n : ℕ} → Bits n → Bits n × Bool
  | 0, .nil => (.nil, incoming)
  | _ + 1, .cons bit tail =>
      let next := shiftRight bit tail
      (.cons incoming next.1, next.2)

def halve {n : ℕ} (a : Bits n) : Bits n := (shiftRight false a).1

theorem shiftRight_value {n : ℕ} (incoming : Bool) (a : Bits n) :
    2 * (shiftRight incoming a).1.value + (if (shiftRight incoming a).2 then 1 else 0) =
      (if incoming then 2 ^ n else 0) + a.value := by
  induction a generalizing incoming with
  | nil => cases incoming <;> simp [shiftRight, Bits.value]
  | @cons n bit tail ih =>
    have h := ih bit
    simp only [shiftRight, Bits.value, pow_succ]
    cases incoming <;> cases bit <;> simp_all <;> omega

theorem halve_value {n : ℕ} (a : Bits n) : (halve a).value = a.value / 2 := by
  have h := shiftRight_value false a
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at h
  unfold halve
  cases hd : (shiftRight false a).2 <;> simp [hd] at h <;> omega

def shiftedBody : Command p :=
  .allocate 6 (.bit (.register 1) (.register 4)) (.ret [.register 6, .register 5])

def shiftBody (self : Fin p) : Command p :=
  .load (.register 0) 2 15 3 (RegisterAdder.nilBitCases
    (.ret [.null, .register 1])
    (.call self [.register 2, .register 3] [4, 5] shiftedBody))

/-- Two inputs (word and incoming bit), two outputs (shifted word and dropped
bit). Every input bit causes one load, one recursive call, and one allocation. -/
theorem shift_compiled (code : Code p) (self : Fin p)
    (hself : code self = shiftBody self)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap : Ptr} {a : Bits n}
    (ha : BitsAt h ap a) (incoming : Bool) :
    ∃ out result, Extends h out ∧ Valid out ∧ BitsAt out result (shiftRight incoming a).1 ∧
      Within code h (initialRegisters [.pointer ap, .flag incoming]) (code self)
        [.pointer result, .flag (shiftRight incoming a).2] out (28 * n + 15) := by
  induction a generalizing h ap incoming with
  | nil =>
    cases ha with
    | nil hcell =>
      let regs := initialRegisters [Value.pointer ap, .flag incoming]
      have last : Within code h (loadRegisters regs 2 15 3 .nil)
          (.ret [.null, .register 1]) [.pointer 0, .flag incoming] h 5 := by
        simpa [regs, loadRegisters, decoded, initialRegisters, values, Atom.eval] using
          Within.ret code h (loadRegisters regs 2 15 3 .nil) [.null, .register 1]
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 2) (second := 15) (bit := 3)
        (branches := RegisterAdder.nilBitCases (.ret [.null, .register 1])
          (.call self [.register 2, .register 3] [4, 5] shiftedBody))
        (by simp [regs, initialRegisters, Atom.eval]) hcell last
      refine ⟨h, 0, Extends.refl h, hh, BitsAt.nil hh.1, ?_⟩
      rw [hself]
      exact load
  | @cons n bit tail ih =>
    cases ha with
    | @cons _ tailPtr _ _ _ hcell htail =>
      obtain ⟨out, result, hext, hv, hrep, hrest⟩ := ih hh htail bit
      have hs := allocate_bit hv incoming hrep
      let regs := initialRegisters [Value.pointer ap, .flag incoming]
      let loaded := loadRegisters regs 2 15 3 (.bit bit tailPtr)
      let recursed := bindResults loaded [4, 5] [Value.pointer result, .flag (shiftRight bit tail).2]
      have last : Within code (out ++ [.bit incoming result])
          (Function.update recursed 6 (.pointer out.length)) (.ret [.register 6, .register 5])
          [.pointer out.length, .flag (shiftRight bit tail).2] (out ++ [.bit incoming result]) 5 := by
        simpa [recursed, bindResults, values, Atom.eval] using
          Within.ret code (out ++ [.bit incoming result])
            (Function.update recursed 6 (.pointer out.length)) [.register 6, .register 5]
      have alloc := Within.allocate (regs := recursed) (dst := 6)
        (expr := .bit (.register 1) (.register 4))
        (by simp [recursed, loaded, regs, bindResults, loadRegisters, decoded, initialRegisters,
          CellExpr.eval, Atom.eval, Value.asPointer, Value.asFlag]) last
      have hargs : values loaded [.register 2, .register 3] = [.pointer tailPtr, .flag bit] := by
        simp [loaded, loadRegisters, decoded, values, Atom.eval]
      have call := Within.call (procedure := self) (regs := loaded)
        (arguments := [.register 2, .register 3]) (results := [4, 5])
        (by simpa only [hargs] using hrest) alloc
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 2) (second := 15) (bit := 3)
        (branches := RegisterAdder.nilBitCases (.ret [.null, .register 1])
          (.call self [.register 2, .register 3] [4, 5] shiftedBody))
        (by simp [regs, initialRegisters, Atom.eval]) hcell call
      refine ⟨out ++ [.bit incoming result], out.length, hext.trans hs.1.1, hs.1.2.1, hs.2, ?_⟩
      rw [hself]
      exact load.mono (by simp [CellExpr.args]; omega)

def halveBody (shift : Fin p) : Command p :=
  .call shift [.register 0, .flag false] [1, 2] (.ret [.register 1])

theorem halve_compiled (code : Code p) (shift : Fin p) (hshift : code shift = shiftBody shift)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap : Ptr} {a : Bits n} (ha : BitsAt h ap a) :
    ∃ out result, Extends h out ∧ Valid out ∧ BitsAt out result (halve a) ∧
      Within code h (initialRegisters [.pointer ap]) (halveBody shift)
        [.pointer result] out (28 * n + 23) := by
  obtain ⟨out, result, hext, hv, hr, hx⟩ := shift_compiled code shift hshift hh ha false
  let regs := initialRegisters [Value.pointer ap]
  let done := bindResults regs [1, 2] [Value.pointer result, .flag (shiftRight false a).2]
  have last : Within code out done (.ret [.register 1]) [.pointer result] out 3 := by
    simpa [done, bindResults, values, Atom.eval] using Within.ret code out done [.register 1]
  have hargs : values regs [.register 0, .flag false] = [.pointer ap, .flag false] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have call := Within.call (procedure := shift) (regs := regs)
    (arguments := [.register 0, .flag false]) (results := [1, 2])
    (by simpa only [hargs] using hx) last
  exact ⟨out, result, hext, hv, hr, call.mono (by simp; omega)⟩

/-- The highest representable power of two for a nonempty word shape. -/
def powerTop : (n : ℕ) → Bits n
  | 0 => .nil
  | n + 1 => .cons true (Bits.zero n)

theorem powerTop_value (n : ℕ) : (powerTop (n + 1)).value = 2 ^ n := by
  simp [powerTop, Bits.value]

def powerBody (zero : Fin p) : Command p :=
  .load (.register 0) 1 15 2 (RegisterAdder.nilBitCases (.ret [.null])
    (.call zero [.register 1] [3]
      (.allocate 4 (.bit (.flag true) (.register 3)) (.ret [.register 4]))))

theorem power_compiled (code : Code p) (zero : Fin p)
    (hzero : code zero = RegisterZero.zeroBody zero)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap : Ptr} {a : Bits n} (ha : BitsAt h ap a) :
    ∃ out result, Extends h out ∧ Valid out ∧ BitsAt out result (powerTop n) ∧
      Within code h (initialRegisters [.pointer ap]) (powerBody zero)
        [.pointer result] out (24 * n + 30) := by
  cases a with
  | nil =>
    cases ha with
    | nil hcell =>
      let regs := initialRegisters [Value.pointer ap]
      have last := Within.ret code h (loadRegisters regs 1 15 2 .nil) [.null]
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 1) (second := 15) (bit := 2)
        (branches := RegisterAdder.nilBitCases (.ret [.null])
          (.call zero [.register 1] [3]
            (.allocate 4 (.bit (.flag true) (.register 3)) (.ret [.register 4]))))
        (by simp [regs, initialRegisters, Atom.eval]) hcell last
      exact ⟨h, 0, Extends.refl h, hh, .nil hh.1, load.mono (by simp)⟩
  | @cons n bit tail =>
    cases ha with
    | @cons _ tailPtr _ _ _ hcell htail =>
      obtain ⟨out, zp, hext, hv, hz, _, hzeroCode⟩ := RegisterZero.compiled code zero hzero hh htail
      have hs := allocate_bit hv true hz
      let regs := initialRegisters [Value.pointer ap]
      let loaded := loadRegisters regs 1 15 2 (.bit bit tailPtr)
      let zeroed := bindResults loaded [3] [Value.pointer zp]
      have last : Within code (out ++ [.bit true zp])
          (Function.update zeroed 4 (.pointer out.length)) (.ret [.register 4])
          [.pointer out.length] (out ++ [.bit true zp]) 3 := by
        simpa [values, Atom.eval] using Within.ret code (out ++ [.bit true zp])
          (Function.update zeroed 4 (.pointer out.length)) [.register 4]
      have alloc := Within.allocate (regs := zeroed) (dst := 4)
        (expr := .bit (.flag true) (.register 3))
        (by simp [zeroed, bindResults, CellExpr.eval, Atom.eval, Value.asFlag, Value.asPointer]) last
      have hargs : values loaded [.register 1] = [.pointer tailPtr] := by
        simp [loaded, loadRegisters, decoded, values, Atom.eval]
      have call := Within.call (procedure := zero) (regs := loaded)
        (arguments := [.register 1]) (results := [3]) (by simpa only [hargs] using hzeroCode) alloc
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 1) (second := 15) (bit := 2)
        (branches := RegisterAdder.nilBitCases (.ret [.null])
          (.call zero [.register 1] [3]
            (.allocate 4 (.bit (.flag true) (.register 3)) (.ret [.register 4]))))
        (by simp [regs, initialRegisters, Atom.eval]) hcell call
      refine ⟨out ++ [.bit true zp], out.length, hext.trans hs.1.1, hs.1.2.1, hs.2, ?_⟩
      exact load.mono (by simp [CellExpr.args]; omega)

end WeightedMIS.RegisterHalve
