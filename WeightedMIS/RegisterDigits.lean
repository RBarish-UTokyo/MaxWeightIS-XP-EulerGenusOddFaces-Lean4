module

public import WeightedMIS.RegisterRemainder
public import WeightedMIS.ExpandedWords

/-!
# Closed repeated-division decoding

The length is supplied by the actual shape of a list, not by an unbounded
natural-number instruction. Every round calls the compiled divider, retains
the low remainder word, and recurses on the quotient and list tail.
-/

@[expose] public section

namespace WeightedMIS.RegisterDigits

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.ExpandedWords

variable {p n : ℕ}

def decodeWords (base : Bits n) : ℕ → Bits n → List (Bits n)
  | 0, _ => []
  | count + 1, value =>
      let qr := Bits.divide value base
      Bits.low qr.2.1 :: decodeWords base count qr.1

def naturalDigits (base : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | count + 1, value => value % base :: naturalDigits base count (value / base)

theorem decodeWords_values (base value : Bits n) (count : ℕ) :
    (decodeWords base count value).map Bits.value = naturalDigits base.value count value.value := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih =>
    simp only [decodeWords, naturalDigits, List.map_cons, ih]
    have hq := (Bits.divide_value value base).1
    have hr := Bits.remainder_value value base
    change (Bits.low (Bits.divide value base).2.1).value = _ at hr
    rw [hr, hq]

theorem decodeWords_length (base value : Bits n) (count : ℕ) :
    (decodeWords base count value).length = count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp [decodeWords, ih]

def afterRemainder (self : Fin p) : Command p :=
  .call self [.register 5, .register 1, .register 4] [8]
    (.allocate 9 (.cons (.register 7) (.register 8)) (.ret [.register 9]))

def afterDivision (self : Fin p) : Command p :=
  .load (.register 6) 7 15 14 (RegisterAdder.nilBitCases .fail (afterRemainder self))

def decodeBody (self divide : Fin p) : Command p :=
  .load (.register 2) 3 4 15 {
    nil := .ret [.null]
    bit := .fail
    cons := .call divide [.register 0, .register 1] [5, 6] (afterDivision self)
    fork := .fail
    bucket := .fail
    pair := .fail
  }

theorem compiled (code : Code p) (self : Fin p) (ids : RegisterDivision.Procedures p)
    (hcode : code self = decodeBody self ids.divide) (hdiv : ids.Matches code)
    {h : Heap} (hh : Valid h) {ap bp tp : Ptr} {value base : Bits n}
    (ha : BitsAt h ap value) (hb : BitsAt h bp base) (shape : List Ptr)
    (ht : ListAt h tp shape) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      WordsAt out result (decodeWords base shape.length value) ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp, .pointer tp]) (code self)
        [.pointer result] out ((400 * (n + 1) ^ 2 + 43) * shape.length + 13) := by
  obtain ⟨zeroCode, cmpCode, auxCode, shiftCode, snocCode, subCode, compCode, addCode, divCode⟩ := hdiv
  induction shape generalizing h ap bp tp value with
  | nil =>
    cases ht with
    | nil hcell =>
      refine ⟨h, 0, .refl h, hh, WordsAt.nil hh.1, ?_⟩
      rw [hcode]
      let regs := initialRegisters [Value.pointer ap, .pointer bp, .pointer tp]
      have last := Within.ret code h (loadRegisters regs 3 4 15 .nil) [.null]
      exact Within.load (address := .register 2) (first := 3) (second := 4) (bit := 15)
        (branches := ⟨.ret [.null], .fail,
          .call ids.divide [.register 0, .register 1] [5, 6] (afterDivision self),
          .fail, .fail, .fail⟩)
        (by simp [Atom.eval, regs, initialRegisters]) hcell last
  | cons item shape ih =>
    cases ht with
    | @cons _ _ tail _ hcell htail =>
      obtain ⟨mid, qp, rp, ext, valid, qrep, rrep, division⟩ :=
        RegisterDivision.divide_compiled code ids.zero ids.cmp ids.aux ids.shift ids.snoc
          ids.sub ids.complement ids.add zeroCode cmpCode auxCode shiftCode snocCode subCode
          compCode addCode hh ha hb
      rw [← divCode] at division
      cases remEq : (Bits.divide value base).2.1 with
      | cons bit remTail =>
        rw [remEq] at rrep
        cases rrep with
        | @cons _ remPtr _ _ _ remCell remRep =>
          obtain ⟨lastHeap, listPtr, lastExt, lastValid, lastRep, child⟩ :=
            ih valid qrep (hb.mono ext) (htail.mono ext)
          have alloc := allocate_word_cons lastValid (remRep.mono lastExt) lastRep
          let final := lastHeap ++ [.cons remPtr listPtr]
          let regs := initialRegisters [Value.pointer ap, .pointer bp, .pointer tp]
          let loaded := loadRegisters regs 3 4 15 (.cons item tail)
          let divided := bindResults loaded [5, 6] [Value.pointer qp, .pointer rp]
          let remainder := loadRegisters divided 7 15 14 (.bit bit remPtr)
          let ready := bindResults remainder [8] [Value.pointer listPtr]
          have last : Within code final (Function.update ready 9 (.pointer lastHeap.length))
              (.ret [.register 9]) [.pointer lastHeap.length] final 3 := by
            simpa [values, Atom.eval] using
              Within.ret code final (Function.update ready 9 (.pointer lastHeap.length)) [.register 9]
          have allocation := Within.allocate (dst := 9)
            (expr := .cons (.register 7) (.register 8))
            (by simp [CellExpr.eval, Atom.eval, ready, remainder, bindResults,
              loadRegisters, decoded, Value.asPointer]) last
          have cargs : values remainder [.register 5, .register 1, .register 4] =
              [.pointer qp, .pointer bp, .pointer tail] := by
            simp [values, Atom.eval, remainder, divided, loaded, regs, bindResults,
              loadRegisters, decoded, initialRegisters]
          have recursion := Within.call (procedure := self)
            (arguments := [.register 5, .register 1, .register 4]) (results := [8])
            (regs := remainder) (by simpa only [cargs] using child) allocation
          have remLoad := Within.load (address := .register 6) (first := 7) (second := 15) (bit := 14)
            (branches := RegisterAdder.nilBitCases .fail (afterRemainder self))
            (by simp [Atom.eval, divided, bindResults]) remCell recursion
          have dargs : values loaded [.register 0, .register 1] = [.pointer ap, .pointer bp] := by
            simp [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters]
          have dcall := Within.call (procedure := ids.divide) (arguments := [.register 0, .register 1])
            (results := [5, 6]) (regs := loaded) (by simpa only [dargs] using division) remLoad
          have initialLoad := Within.load (address := .register 2) (first := 3) (second := 4) (bit := 15)
            (branches := ⟨.ret [.null], .fail,
              .call ids.divide [.register 0, .register 1] [5, 6] (afterDivision self),
              .fail, .fail, .fail⟩)
            (by simp [Atom.eval, regs, initialRegisters]) hcell dcall
          refine ⟨final, lastHeap.length, ext.trans (lastExt.trans alloc.1.1), alloc.1.2.1, ?_, ?_⟩
          · simpa [decodeWords, remEq, Bits.low] using alloc.2
          · rw [hcode]
            exact initialLoad.mono (by simp [CellExpr.args, Nat.mul_add]; omega)

end WeightedMIS.RegisterDigits
