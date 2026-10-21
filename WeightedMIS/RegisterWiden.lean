module

public import WeightedMIS.RegisterZero
public import WeightedMIS.CompiledTrie
public import WeightedMIS.EfficientSearchCodeBounds

/-!
# Zero extension of binary words

Words are big-endian: `Bits.cons` holds the most significant bit. Widening a
word by the width of a shape word prepends one zero bit for every shape bit, so
the numerical value is unchanged. The procedure traverses the shape word, sharing
the original word as the tail of the result.

A padding word of width `(w + 1) * L` is obtained by widening `L` times by a
zero-extended shape of width `w + 1`, one round per element of a linked list of
length `L`. It is exactly the zero word of that width.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Bits

/-- Prepend one zero bit for every bit of the shape word. -/
def widen {w : ℕ} : {j : ℕ} → Bits j → Bits w → Bits (w + j)
  | 0, .nil, a => a
  | _ + 1, .cons _ shape, a => .cons false (widen shape a)

@[simp] theorem widen_nil {w : ℕ} (a : Bits w) : widen Bits.nil a = a := rfl

@[simp] theorem widen_cons {w j : ℕ} (bit : Bool) (shape : Bits j) (a : Bits w) :
    widen (.cons bit shape) a = .cons false (widen shape a) := rfl

@[simp] theorem widen_value {w j : ℕ} (shape : Bits j) (a : Bits w) :
    (widen shape a).value = a.value := by
  induction shape with
  | nil => rfl
  | cons bit shape ih => simp [value, ih]

theorem widen_zero {w j : ℕ} (shape : Bits j) : widen shape (zero w) = zero (w + j) := by
  induction shape with
  | nil => rfl
  | cons bit shape ih => simp only [widen_cons, ih]; rfl

/-- The zero word of width `(w + 1) * L`, built from `L` widenings. -/
def pad {w : ℕ} (shape : Bits w) : (L : ℕ) → Bits ((w + 1) * L)
  | 0 => .nil
  | L + 1 => widen (.cons false shape) (pad shape L)

theorem pad_eq_zero {w : ℕ} (shape : Bits w) (L : ℕ) : pad shape L = zero ((w + 1) * L) := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [pad, ih]; exact widen_zero _

@[simp] theorem pad_value {w : ℕ} (shape : Bits w) (L : ℕ) : (pad shape L).value = 0 := by
  rw [pad_eq_zero, value_zero]

end WeightedMIS.EfficientSearch.Bits

namespace WeightedMIS.RegisterWiden

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch

variable {p : ℕ}

/-- Inputs: shape word, word. Output: the widened word. -/
def widenBody (self : Fin p) : Command p :=
  .load (.register 0) 2 15 3 (RegisterAdder.nilBitCases
    (.ret [.register 1])
    (.call self [.register 2, .register 1] [4]
      (.allocate 5 (.bit (.flag false) (.register 4)) (.ret [.register 5]))))

def widenBudget (j : ℕ) : ℕ := 26 * j + 13

/-- Every shape bit costs one load, one recursive call and one allocation. The
input word is shared, not copied. -/
theorem widen_compiled (code : Code p) (self : Fin p) (hself : code self = widenBody self)
    {j w : ℕ} {h : Heap} (hh : Valid h) {sp ap : Ptr} {shape : Bits j} {a : Bits w}
    (hs : BitsAt h sp shape) (ha : BitsAt h ap a) :
    ∃ out result, Extends h out ∧ Valid out ∧ BitsAt out result (Bits.widen shape a) ∧
      Within code h (initialRegisters [.pointer sp, .pointer ap]) (code self)
        [.pointer result] out (widenBudget j) := by
  induction shape generalizing h sp with
  | nil =>
    cases hs with
    | nil hcell =>
      let regs := initialRegisters [Value.pointer sp, .pointer ap]
      have last : Within code h (loadRegisters regs 2 15 3 .nil)
          (.ret [.register 1]) [.pointer ap] h 3 := by
        simpa [regs, loadRegisters, decoded, initialRegisters, values, Atom.eval] using
          Within.ret code h (loadRegisters regs 2 15 3 .nil) [.register 1]
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 2) (second := 15) (bit := 3)
        (branches := RegisterAdder.nilBitCases (.ret [.register 1])
          (.call self [.register 2, .register 1] [4]
            (.allocate 5 (.bit (.flag false) (.register 4)) (.ret [.register 5]))))
        (by simp [regs, initialRegisters, Atom.eval]) hcell last
      refine ⟨h, ap, Extends.refl h, hh, ha, ?_⟩
      rw [hself]
      exact load.mono (by simp [widenBudget])
  | @cons j bit shape ih =>
    cases hs with
    | @cons _ tailPtr _ _ _ hcell htail =>
      obtain ⟨out, result, hext, hv, hrep, hrest⟩ := ih hh htail ha
      have hb := allocate_bit hv false hrep
      let regs := initialRegisters [Value.pointer sp, .pointer ap]
      let loaded := loadRegisters regs 2 15 3 (.bit bit tailPtr)
      let recursed := bindResults loaded [4] [Value.pointer result]
      have last : Within code (out ++ [.bit false result])
          (Function.update recursed 5 (.pointer out.length)) (.ret [.register 5])
          [.pointer out.length] (out ++ [.bit false result]) 3 := by
        simpa [values, Atom.eval] using Within.ret code (out ++ [.bit false result])
          (Function.update recursed 5 (.pointer out.length)) [.register 5]
      have alloc := Within.allocate (regs := recursed) (dst := 5)
        (expr := .bit (.flag false) (.register 4))
        (by simp [recursed, bindResults, CellExpr.eval, Atom.eval, Value.asFlag,
          Value.asPointer]) last
      have hargs : values loaded [.register 2, .register 1] =
          [.pointer tailPtr, .pointer ap] := by
        simp [loaded, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
      have call := Within.call (procedure := self) (regs := loaded)
        (arguments := [.register 2, .register 1]) (results := [4])
        (by simpa only [hargs] using hrest) alloc
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 2) (second := 15) (bit := 3)
        (branches := RegisterAdder.nilBitCases (.ret [.register 1])
          (.call self [.register 2, .register 1] [4]
            (.allocate 5 (.bit (.flag false) (.register 4)) (.ret [.register 5]))))
        (by simp [regs, initialRegisters, Atom.eval]) hcell call
      refine ⟨out ++ [.bit false result], out.length, hext.trans hb.1.1, hb.1.2.1, hb.2, ?_⟩
      rw [hself]
      exact load.mono (by simp [CellExpr.args, widenBudget]; omega)

/-- Inputs: a linked list of length `L` (contents ignored), shape word of width
`w`. Output: the zero word `Bits.pad shape L` of width `(w + 1) * L`. -/
def padBody (self widen : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .call self [.register 3, .register 1] [4]
      (.call widen [.register 1, .register 4] [5]
        (.allocate 6 (.bit (.flag false) (.register 5)) (.ret [.register 6]))) }

def padBudget (w L : ℕ) : ℕ := (widenBudget w + 32) * L + 13

theorem pad_compiled (code : Code p) (self widen : Fin p)
    (hself : code self = padBody self widen) (hwiden : code widen = widenBody widen)
    {w : ℕ} {h : Heap} (hh : Valid h) {lp sp : Ptr} {xs : List Ptr} {shape : Bits w}
    (hl : ListAt h lp xs) (hs : BitsAt h sp shape) :
    ∃ out result, Extends h out ∧ Valid out ∧ BitsAt out result (Bits.pad shape xs.length) ∧
      Within code h (initialRegisters [.pointer lp, .pointer sp]) (code self)
        [.pointer result] out (padBudget w xs.length) := by
  induction xs generalizing h lp with
  | nil =>
    cases hl with
    | nil hcell =>
      let regs := initialRegisters [Value.pointer lp, .pointer sp]
      have last : Within code h (loadRegisters regs 2 3 15 .nil)
          (.ret [.null]) [.pointer 0] h 3 := by
        simpa [values, Atom.eval] using
          Within.ret code h (loadRegisters regs 2 3 15 .nil) [.null]
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 2) (second := 3) (bit := 15)
        (branches := { CompiledTrie.failCases with
          nil := .ret [.null]
          cons := .call self [.register 3, .register 1] [4]
            (.call widen [.register 1, .register 4] [5]
              (.allocate 6 (.bit (.flag false) (.register 5)) (.ret [.register 6]))) })
        (by simp [regs, initialRegisters, Atom.eval]) hcell last
      refine ⟨h, 0, Extends.refl h, hh, BitsAt.nil hh.1, ?_⟩
      rw [hself]
      exact load.mono (by simp [padBudget])
  | cons x xs ih =>
    cases hl with
    | @cons _ _ tailPtr _ hcell htail =>
      obtain ⟨mid, accp, he1, hv1, hacc, hrest⟩ := ih hh htail hs
      obtain ⟨out, wp, he2, hv2, hw, wrun⟩ :=
        widen_compiled code widen hwiden hv1 (hs.mono he1) hacc
      have hb := allocate_bit hv2 false hw
      let regs := initialRegisters [Value.pointer lp, .pointer sp]
      let loaded := loadRegisters regs 2 3 15 (.cons x tailPtr)
      let r1 := bindResults loaded [4] [Value.pointer accp]
      let r2 := bindResults r1 [5] [Value.pointer wp]
      have last : Within code (out ++ [.bit false wp])
          (Function.update r2 6 (.pointer out.length)) (.ret [.register 6])
          [.pointer out.length] (out ++ [.bit false wp]) 3 := by
        simpa [values, Atom.eval] using Within.ret code (out ++ [.bit false wp])
          (Function.update r2 6 (.pointer out.length)) [.register 6]
      have alloc := Within.allocate (regs := r2) (dst := 6)
        (expr := .bit (.flag false) (.register 5))
        (by simp [r2, bindResults, CellExpr.eval, Atom.eval, Value.asFlag,
          Value.asPointer]) last
      have hargsW : values r1 [.register 1, .register 4] = [.pointer sp, .pointer accp] := by
        simp [r1, loaded, regs, bindResults, loadRegisters, decoded, initialRegisters, values,
          Atom.eval]
      have wcall := Within.call (procedure := widen) (regs := r1)
        (arguments := [.register 1, .register 4]) (results := [5])
        (by simpa only [hargsW] using wrun) alloc
      have hargsP : values loaded [.register 3, .register 1] = [.pointer tailPtr, .pointer sp] := by
        simp [loaded, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
      have pcall := Within.call (procedure := self) (regs := loaded)
        (arguments := [.register 3, .register 1]) (results := [4])
        (by simpa only [hargsP] using hrest) wcall
      have load := Within.load (regs := regs) (address := .register 0)
        (first := 2) (second := 3) (bit := 15)
        (branches := { CompiledTrie.failCases with
          nil := .ret [.null]
          cons := .call self [.register 3, .register 1] [4]
            (.call widen [.register 1, .register 4] [5]
              (.allocate 6 (.bit (.flag false) (.register 5)) (.ret [.register 6]))) })
        (by simp [regs, initialRegisters, Atom.eval]) hcell pcall
      refine ⟨out ++ [.bit false wp], out.length, (he1.trans he2).trans hb.1.1, hb.1.2.1, hb.2, ?_⟩
      rw [hself]
      exact load.mono (by simp only [padBudget, CellExpr.args, List.length_cons,
        List.length_nil]; ring_nf; omega)

end WeightedMIS.RegisterWiden
