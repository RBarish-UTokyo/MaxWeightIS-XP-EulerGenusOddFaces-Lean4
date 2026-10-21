module

public import WeightedMIS.RegisterSubtractor

/-! # Closed register programs for appending a bit and fixed-width shifts -/

@[expose] public section

namespace WeightedMIS.RegisterShift

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

/-- Append the bit in register one to the word in register zero. -/
def snocBody (self : Fin p) : Command p :=
  .load (.register 0) 3 15 4 (RegisterAdder.nilBitCases
    (.allocate 9 (.bit (.register 1) (.register 0)) (.ret [.register 9]))
    (.call self [.register 3, .register 1] [7]
      (.allocate 9 (.bit (.register 4) (.register 7)) (.ret [.register 9]))))

theorem allocate_within (code : Code p) (h : Heap) (regs : Registers)
    (br tr : Register) (bit : Bool) (tail : Ptr)
    (hb : regs br = .flag bit) (ht : regs tr = .pointer tail) :
    Within code h regs
      (.allocate 9 (.bit (.register br) (.register tr)) (.ret [.register 9]))
      [.pointer h.length] (h ++ [.bit bit tail]) 11 := by
  have last : Within code (h ++ [.bit bit tail])
      (Function.update regs 9 (.pointer h.length)) (.ret [.register 9])
      [.pointer h.length] (h ++ [.bit bit tail]) 3 := by
    simpa [values, Atom.eval] using
      Within.ret code (h ++ [.bit bit tail])
        (Function.update regs 9 (.pointer h.length)) [.register 9]
  have hh := Within.allocate (dst := 9) (expr := .bit (.register br) (.register tr))
    (by simp [CellExpr.eval, Atom.eval, hb, ht, Value.asFlag, Value.asPointer]) last
  simpa [CellExpr.args] using hh

theorem snoc_compiled (code : Code p) (self : Fin p) (body : code self = snocBody self)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap : Ptr} {a : Bits n}
    (ha : BitsAt h ap a) (lastBit : Bool) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (Bits.snoc a lastBit).1 ∧ out.length = h.length + n + 1 ∧
      Within code h (initialRegisters [.pointer ap, .flag lastBit]) (code self)
        [.pointer result] out (26 * n + 21) := by
  induction a generalizing h ap with
  | nil =>
      cases ha with
      | nil hac =>
        have alloc := allocate_bit hh lastBit (BitsAt.nil hac)
        refine ⟨h ++ [.bit lastBit ap], h.length, alloc.1.1, alloc.1.2.1,
          alloc.2, by simp, ?_⟩
        rw [body]
        let regs := initialRegisters [Value.pointer ap, .flag lastBit]
        let loaded := loadRegisters regs 3 15 4 Cell.nil
        have last := allocate_within code h loaded 1 0 lastBit ap
          (by simp [loaded, regs, loadRegisters, decoded, initialRegisters])
          (by simp [loaded, regs, loadRegisters, decoded, initialRegisters])
        exact Within.load (address := .register 0) (first := 3) (second := 15) (bit := 4)
          (branches := RegisterAdder.nilBitCases
            (.allocate 9 (.bit (.register 1) (.register 0)) (.ret [.register 9]))
            (.call self [.register 3, .register 1] [7]
              (.allocate 9 (.bit (.register 4) (.register 7)) (.ret [.register 9]))))
          (by simp [Atom.eval, regs, initialRegisters]) hac last
  | @cons n bit tail ih =>
      cases ha with
      | @cons _ atail _ _ _ hac hat =>
        obtain ⟨mid, tp, hext, hvalid, hrep, hlen, hchild⟩ := ih hh hat
        have alloc := allocate_bit hvalid bit hrep
        refine ⟨mid ++ [.bit bit tp], mid.length, hext.trans alloc.1.1,
          alloc.1.2.1, ?_, ?_, ?_⟩
        · simpa [Bits.snoc, Program.allocate] using alloc.2
        · simp [hlen]; omega
        · rw [body]
          let regs := initialRegisters [Value.pointer ap, .flag lastBit]
          let loaded := loadRegisters regs 3 15 4 (.bit bit atail)
          let ready := bindResults loaded [7] [Value.pointer tp]
          have hb : ready 4 = .flag bit := by
            simp [ready, loaded, regs, bindResults, loadRegisters, decoded]
          have ht : ready 7 = .pointer tp := by simp [ready, bindResults]
          have last := allocate_within code mid ready 4 7 bit tp hb ht
          have hargs : values loaded [.register 3, .register 1] =
              [.pointer atail, .flag lastBit] := by
            simp [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters]
          have hcall := Within.call (procedure := self) (arguments := [.register 3, .register 1])
            (results := [7]) (regs := loaded) (returned := [.pointer tp])
            (by simpa only [hargs] using hchild) last
          have hload := Within.load (address := .register 0) (first := 3) (second := 15) (bit := 4)
            (branches := RegisterAdder.nilBitCases
              (.allocate 9 (.bit (.register 1) (.register 0)) (.ret [.register 9]))
              (.call self [.register 3, .register 1] [7]
                (.allocate 9 (.bit (.register 4) (.register 7)) (.ret [.register 9]))))
            (by simp [Atom.eval, regs, initialRegisters]) hac hcall
          exact hload.mono (by simp only [List.length_cons, List.length_nil]; omega)

/-- Discard the leading bit and append the supplied bit. -/
def shiftInBody (snoc : Fin p) : Command p :=
  .load (.register 0) 3 15 4 (RegisterAdder.nilBitCases
    (.ret [.register 0])
    (.call snoc [.register 3, .register 1] [7] (.ret [.register 7])))

theorem shiftIn_compiled (code : Code p) (snoc : Fin p) (body : code snoc = snocBody snoc)
    {n : ℕ} {h : Heap} (hh : Valid h) {ap : Ptr} {a : Bits n}
    (ha : BitsAt h ap a) (bit : Bool) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (Bits.shiftIn a bit).1 ∧ out.length = h.length + n ∧
      Within code h (initialRegisters [.pointer ap, .flag bit]) (shiftInBody snoc)
        [.pointer result] out (26 * n + 13) := by
  cases a with
  | nil =>
      cases ha with
      | nil hac =>
        refine ⟨h, ap, .refl h, hh, .nil hac, by simp, ?_⟩
        let regs := initialRegisters [Value.pointer ap, .flag bit]
        let loaded := loadRegisters regs 3 15 4 Cell.nil
        have last : Within code h loaded (.ret [.register 0]) [.pointer ap] h 3 := by
          simpa [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters] using
            Within.ret code h loaded [.register 0]
        exact Within.load (address := .register 0) (first := 3) (second := 15) (bit := 4)
          (branches := RegisterAdder.nilBitCases (.ret [.register 0])
            (.call snoc [.register 3, .register 1] [7] (.ret [.register 7])))
          (by simp [Atom.eval, regs, initialRegisters]) hac last
  | @cons n head tail =>
      cases ha with
      | @cons _ atail _ _ _ hac hat =>
        obtain ⟨out, result, hext, hvalid, hrep, hlen, hchild⟩ :=
          snoc_compiled code snoc body hh hat bit
        refine ⟨out, result, hext, hvalid, hrep, by omega, ?_⟩
        let regs := initialRegisters [Value.pointer ap, .flag bit]
        let loaded := loadRegisters regs 3 15 4 (.bit head atail)
        let ready := bindResults loaded [7] [Value.pointer result]
        have last : Within code out ready (.ret [.register 7]) [.pointer result] out 3 := by
          simpa [values, Atom.eval, ready, bindResults] using Within.ret code out ready [.register 7]
        have hargs : values loaded [.register 3, .register 1] =
            [.pointer atail, .flag bit] := by
          simp [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters]
        have hcall := Within.call (procedure := snoc) (arguments := [.register 3, .register 1])
          (results := [7]) (regs := loaded) (returned := [.pointer result])
          (by simpa only [hargs] using hchild) last
        have hload := Within.load (address := .register 0) (first := 3) (second := 15) (bit := 4)
          (branches := RegisterAdder.nilBitCases (.ret [.register 0])
            (.call snoc [.register 3, .register 1] [7] (.ret [.register 7])))
          (by simp [Atom.eval, regs, initialRegisters]) hac hcall
        exact hload.mono (by simp only [List.length_cons, List.length_nil]; omega)

end WeightedMIS.RegisterShift
