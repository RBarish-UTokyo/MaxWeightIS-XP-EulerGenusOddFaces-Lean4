module

public import WeightedMIS.RegisterAdder
public import WeightedMIS.EfficientSearchCodeBounds
public import WeightedMIS.WordNodeCodec

/-!
# Stripping leading zero bits

Words are big-endian, so the significant part of a word is the suffix that
starts at its first set bit. The procedure follows the stored bit cells and
returns a pointer to that suffix, or to the terminal cell for the value zero.
Nothing is allocated. The returned word has width exactly `x.value.size`,
which is how the canonical vertex and cost widths of the expanded search
graph are defined.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Bits

open WeightedMIS.SparseSearchGraph

/-- The value of `x` as a word of the binary length of that value. -/
def significant {n : ℕ} (x : Bits n) : Bits x.value.size := encodeBits _ x.value

@[simp] theorem significant_value {n : ℕ} (x : Bits n) : (significant x).value = x.value :=
  encodeBits_value _ _ (Nat.lt_size_self _)

theorem size_cons_true {n : ℕ} (t : Bits n) : (Bits.cons true t).value.size = n + 1 := by
  have ht := value_lt t
  apply le_antisymm
  · apply Nat.size_le.mpr
    simp only [value, ↓reduceIte, pow_succ]
    omega
  · apply Nat.lt_size.mpr
    simp [value]

@[simp] theorem value_cons_false {n : ℕ} (t : Bits n) : (Bits.cons false t).value = t.value := by
  simp [value]

end WeightedMIS.EfficientSearch.Bits

namespace WeightedMIS.RegisterSignificant

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.SparseSearchGraph

variable {p : ℕ}

/-- Argument: a word. Result: the suffix starting at its first set bit. -/
def stripBody (self : Fin p) : Command p :=
  .load (.register 0) 1 15 2 (RegisterAdder.nilBitCases
    (.ret [.register 0])
    (.branch (.register 2) (.ret [.register 0])
      (.call self [.register 1] [3] (.ret [.register 3]))))

def stripBudget (n : ℕ) : ℕ := 20 * n + 16

theorem strip_aux (code : Code p) (self : Fin p) (hself : code self = stripBody self)
    {h : Heap} {n : ℕ} {xp : Ptr} {x : Bits n} (hx : BitsAt h xp x) :
    ∃ (q : Ptr) (k : ℕ) (y : Bits k), k = x.value.size ∧ BitsAt h q y ∧ y.value = x.value ∧
      Within code h (initialRegisters [.pointer xp]) (code self) [.pointer q] h
        (stripBudget n) := by
  induction hx with
  | @nil xp cell =>
    refine ⟨xp, 0, .nil, by simp [Bits.value], .nil cell, rfl, ?_⟩
    let regs := initialRegisters [Value.pointer xp]
    have last : Within code h (loadRegisters regs 1 15 2 .nil) (.ret [.register 0])
        [.pointer xp] h 3 := by
      simpa [regs, loadRegisters, decoded, initialRegisters, values, Atom.eval] using
        Within.ret code h (loadRegisters regs 1 15 2 .nil) [.register 0]
    have load := Within.load (regs := regs) (address := .register 0)
      (first := 1) (second := 15) (bit := 2)
      (branches := RegisterAdder.nilBitCases (.ret [.register 0])
        (.branch (.register 2) (.ret [.register 0])
          (.call self [.register 1] [3] (.ret [.register 3]))))
      (by simp [regs, initialRegisters, Atom.eval]) cell last
    rw [hself]
    exact load.mono (by simp [stripBudget])
  | @cons xp tail n bit t cell rest ih =>
    let regs := initialRegisters [Value.pointer xp]
    let loaded := loadRegisters regs 1 15 2 (.bit bit tail)
    cases bit with
    | true =>
      refine ⟨xp, n + 1, .cons true t, (Bits.size_cons_true t).symm, .cons cell rest, rfl, ?_⟩
      have last : Within code h loaded (.ret [.register 0]) [.pointer xp] h 3 := by
        simpa [loaded, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval] using
          Within.ret code h loaded [.register 0]
      have br := Within.branch (regs := loaded) (test := .register 2) (b := true)
        (yes := .ret [.register 0]) (no := .call self [.register 1] [3] (.ret [.register 3]))
        (by simp [loaded, regs, loadRegisters, decoded, Atom.eval]) last
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 1) (second := 15) (bit := 2)
        (branches := RegisterAdder.nilBitCases (.ret [.register 0])
          (.branch (.register 2) (.ret [.register 0])
            (.call self [.register 1] [3] (.ret [.register 3]))))
        (by simp [regs, initialRegisters, Atom.eval]) cell br
      rw [hself]
      exact load.mono (by simp [stripBudget])
    | false =>
      obtain ⟨q, k, y, hk, hy, hval, hrun⟩ := ih
      refine ⟨q, k, y, by simpa using hk, hy, by simpa using hval, ?_⟩
      let ready := bindResults loaded [3] [Value.pointer q]
      have last : Within code h ready (.ret [.register 3]) [.pointer q] h 3 := by
        simpa [ready, values, Atom.eval, bindResults] using Within.ret code h ready [.register 3]
      have hargs : values loaded [.register 1] = [.pointer tail] := by
        simp [loaded, regs, loadRegisters, decoded, values, Atom.eval]
      have call := Within.call (procedure := self) (regs := loaded)
        (arguments := [.register 1]) (results := [3]) (by simpa only [hargs] using hrun) last
      have br := Within.branch (regs := loaded) (test := .register 2) (b := false)
        (yes := .ret [.register 0]) (no := .call self [.register 1] [3] (.ret [.register 3]))
        (by simp [loaded, regs, loadRegisters, decoded, Atom.eval]) call
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 1) (second := 15) (bit := 2)
        (branches := RegisterAdder.nilBitCases (.ret [.register 0])
          (.branch (.register 2) (.ret [.register 0])
            (.call self [.register 1] [3] (.ret [.register 3]))))
        (by simp [regs, initialRegisters, Atom.eval]) cell br
      rw [hself]
      exact load.mono (by simp [stripBudget]; omega)

/-- The returned pointer represents the significant part of the word. The heap
is unchanged and the cost is linear in the stored width. -/
theorem strip_compiled (code : Code p) (self : Fin p) (hself : code self = stripBody self)
    {h : Heap} {n : ℕ} {xp : Ptr} {x : Bits n} (hx : BitsAt h xp x) :
    ∃ q, BitsAt h q (Bits.significant x) ∧
      Within code h (initialRegisters [.pointer xp]) (code self) [.pointer q] h
        (stripBudget n) := by
  obtain ⟨q, k, y, hk, hy, hval, hrun⟩ := strip_aux code self hself hx
  subst hk
  refine ⟨q, ?_, hrun⟩
  rwa [← ScalarNodeCodec.bits_value_injective _ (show y.value = (Bits.significant x).value by
    rw [hval, Bits.significant_value])]

/-- When the stored value is known, the result is the canonical encoding of
that value at its own binary length. -/
theorem strip_compiled_of_value (code : Code p) (self : Fin p)
    (hself : code self = stripBody self)
    {h : Heap} {n N : ℕ} {xp : Ptr} {x : Bits n} (hx : BitsAt h xp x) (hv : x.value = N) :
    ∃ q, BitsAt h q (encodeBits N.size N) ∧
      Within code h (initialRegisters [.pointer xp]) (code self) [.pointer q] h
        (stripBudget n) := by
  subst hv
  exact strip_compiled code self hself hx

end WeightedMIS.RegisterSignificant
