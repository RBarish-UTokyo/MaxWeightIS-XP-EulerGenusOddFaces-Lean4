module

public import WeightedMIS.RegisterComparator

/-! # Closed register code for bitwise complement -/

@[expose] public section

namespace WeightedMIS.RegisterComplement

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def leaf (bit : Bool) : Command p :=
  .allocate 9 (.bit (.flag (!bit)) (.register 7)) (.ret [.register 9])

def afterCall : Command p := .branch (.register 4) (leaf true) (leaf false)

def complementBody (self : Fin p) : Command p :=
  .load (.register 0) 3 15 4 (RegisterAdder.nilBitCases
    (.ret [.register 0])
    (.call self [.register 3] [7] afterCall))

theorem leaf_within (code : Code p) (h : Heap) (regs : Registers) (bit : Bool) (tail : Ptr)
    (ht : regs 7 = .pointer tail) :
    Within code h regs (leaf bit) [.pointer h.length] (h ++ [.bit (!bit) tail]) 11 := by
  have last : Within code (h ++ [.bit (!bit) tail])
      (Function.update regs 9 (.pointer h.length)) (.ret [.register 9])
      [.pointer h.length] (h ++ [.bit (!bit) tail]) 3 := by
    simpa [values, Atom.eval] using
      Within.ret code (h ++ [.bit (!bit) tail])
        (Function.update regs 9 (.pointer h.length)) [.register 9]
  have alloc := Within.allocate (dst := 9) (expr := .bit (.flag (!bit)) (.register 7))
    (by simp [CellExpr.eval, Atom.eval, ht, Value.asPointer, Value.asFlag]) last
  simpa [leaf, CellExpr.args] using alloc

theorem afterCall_within (code : Code p) (h : Heap) (regs : Registers) (bit : Bool) (tail : Ptr)
    (hb : regs 4 = .flag bit) (ht : regs 7 = .pointer tail) :
    Within code h regs afterCall [.pointer h.length] (h ++ [.bit (!bit) tail]) 14 := by
  have last := leaf_within code h regs bit tail ht
  apply Within.branch (budget := 11) (b := bit) (test := .register 4) (yes := leaf true) (no := leaf false)
    (by simpa [Atom.eval] using hb)
  cases bit <;> exact last

/-- The finite program constructs the represented bitwise complement, preserving
all existing cells and allocating exactly one new cell per input bit. -/
theorem compiled (code : Code p) (self : Fin p) (body : code self = complementBody self)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap : Ptr} {a : Bits n} (ha : BitsAt h ap a) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (Bits.complement a).1 ∧ out.length = h.length + n ∧
      Within code h (initialRegisters [.pointer ap]) (code self)
        [.pointer result] out (27 * n + 13) := by
  induction a generalizing h ap with
  | nil =>
      cases ha with
      | nil hac =>
        refine ⟨h, ap, .refl h, hh, .nil hac, by simp, ?_⟩
        rw [body]
        let regs := initialRegisters [Value.pointer ap]
        let loaded := loadRegisters regs 3 15 4 Cell.nil
        have last : Within code h loaded (.ret [.register 0]) [.pointer ap] h 3 := by
          simpa [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters] using
            Within.ret code h loaded [.register 0]
        exact Within.load (address := .register 0) (first := 3) (second := 15) (bit := 4)
          (branches := RegisterAdder.nilBitCases (.ret [.register 0])
            (.call self [.register 3] [7] afterCall))
          (by simp [Atom.eval, regs, initialRegisters]) hac last
  | @cons n bit tail ih =>
      cases ha with
      | @cons _ atail _ _ _ hac hat =>
        obtain ⟨mid, tp, hext, hvalid, hrep, hlen, hchild⟩ := ih hh hat
        have alloc := allocate_bit hvalid (!bit) hrep
        refine ⟨mid ++ [.bit (!bit) tp], mid.length, hext.trans alloc.1.1,
          alloc.1.2.1, ?_, ?_, ?_⟩
        · simpa [Bits.complement, Program.allocate] using alloc.2
        · simp [hlen]; omega
        · rw [body]
          let regs := initialRegisters [Value.pointer ap]
          let loaded := loadRegisters regs 3 15 4 (.bit bit atail)
          let ready := bindResults loaded [7] [Value.pointer tp]
          have hb : ready 4 = .flag bit := by
            simp [ready, loaded, regs, bindResults, loadRegisters, decoded]
          have ht : ready 7 = .pointer tp := by simp [ready, bindResults]
          have last := afterCall_within code mid ready bit tp hb ht
          have hargs : values loaded [.register 3] = [.pointer atail] := by
            simp [values, Atom.eval, loaded, loadRegisters, decoded]
          have hcall := Within.call (procedure := self) (arguments := [.register 3])
            (results := [7]) (regs := loaded) (returned := [.pointer tp])
            (by simpa only [hargs] using hchild) last
          have hload := Within.load (address := .register 0) (first := 3) (second := 15) (bit := 4)
            (branches := RegisterAdder.nilBitCases (.ret [.register 0])
              (.call self [.register 3] [7] afterCall))
            (by simp [Atom.eval, regs, initialRegisters]) hac hcall
          exact hload.mono (by simp only [List.length_cons, List.length_nil]; omega)

end WeightedMIS.RegisterComplement
