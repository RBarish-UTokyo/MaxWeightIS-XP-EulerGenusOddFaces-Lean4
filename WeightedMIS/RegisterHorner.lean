module

public import WeightedMIS.RegisterMultiplier
public import WeightedMIS.EfficientSearchPointerTrie
public import WeightedMIS.EncodingCost
public import WeightedMIS.ExpandedWords

/-!
# Closed positional encoding of a stored digit list

Digits are stored least-significant first, matching `finFunctionFinEquiv`.
The fixed procedure follows the list, encodes its tail, and performs one
compiled multiplication and addition. Intermediate words use a common width.
-/

@[expose] public section

namespace WeightedMIS.RegisterHorner

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer

variable {p n : ℕ}

def numeral (base : ℕ) : List (Bits n) → ℕ
  | [] => 0
  | digit :: rest => digit.value + base * numeral base rest

def encodeWords (base : Bits n) : List (Bits n) → Bits n
  | [] => Bits.zero n
  | digit :: rest => (Bits.add digit (Bits.multiply base (encodeWords base rest)).1).1

theorem encodeWords_modEq (base : Bits n) (digits : List (Bits n)) :
    Nat.ModEq (2 ^ n) (encodeWords base digits).value (numeral base.value digits) := by
  induction digits with
  | nil => simp [encodeWords, numeral, Nat.ModEq]
  | cons digit rest ih =>
    have hm : Nat.ModEq (2 ^ n) (Bits.multiply base (encodeWords base rest)).1.value
        (base.value * numeral base.value rest) := by
      rw [Bits.multiply_value]
      exact (Nat.mod_modEq _ _).trans (ih.mul_left base.value)
    exact (Bits.add_modEq digit _).trans (hm.add_left digit.value)

theorem encodeWords_value (base : Bits n) (digits : List (Bits n)) :
    (encodeWords base digits).value = numeral base.value digits % 2 ^ n := by
  have he := encodeWords_modEq base digits
  exact (Nat.mod_eq_of_lt (Bits.value_lt _)).symm.trans he

theorem encodeWords_exact (base : Bits n) (digits : List (Bits n))
    (h : numeral base.value digits < 2 ^ n) :
    (encodeWords base digits).value = numeral base.value digits := by
  rw [encodeWords_value, Nat.mod_eq_of_lt h]

def hornerBody (self mul add : Fin p) : Command p :=
  .load (.register 0) 3 4 15 {
    nil := .ret [.register 2]
    bit := .fail
    cons := .call self [.register 4, .register 1, .register 2] [5]
      (.call mul [.register 1, .register 5] [6]
        (.call add [.register 3, .register 6, .flag false] [7, 8] (.ret [.register 7])))
    fork := .fail
    bucket := .fail
    pair := .fail
  }

structure Procedures (p : ℕ) where
  self : Fin p
  mul : Fin p
  zero : Fin p
  mulAcc : Fin p
  shift : Fin p
  snoc : Fin p
  add : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.self = hornerBody ids.self ids.mul ids.add ∧
  code ids.mul = RegisterMultiplier.multiplyBody ids.zero ids.mulAcc ∧
  code ids.zero = RegisterZero.zeroBody ids.zero ∧
  code ids.mulAcc = RegisterMultiplier.multiplyAccBody ids.mulAcc ids.shift ids.add ∧
  code ids.shift = RegisterShift.shiftInBody ids.snoc ∧
  code ids.snoc = RegisterShift.snocBody ids.snoc ∧
  code ids.add = RegisterAdder.adderBody ids.add

def digitBudget (n : ℕ) : ℕ := (136 * n + 80) * n + 134 * n + 101

theorem compiled_aux (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {pp : Ptr} {pointers : List Ptr}
    (hl : ListAt h pp pointers) {digits : List (Bits n)}
    (hr : List.Forall₂ (BitsAt h) pointers digits)
    {bp zp : Ptr} {base : Bits n} (hb : BitsAt h bp base) (hz : BitsAt h zp (Bits.zero n)) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (encodeWords base digits) ∧
      Within code h (initialRegisters [.pointer pp, .pointer bp, .pointer zp]) (code ids.self)
        [.pointer result] out (digitBudget n * digits.length + 13) := by
  obtain ⟨selfCode, mulCode, zeroCode, mulAccCode, shiftCode, snocCode, addCode⟩ := hcode
  induction hl generalizing digits with
  | @nil pp cell =>
    cases hr
    refine ⟨h, zp, .refl h, hh, hz, ?_⟩
    rw [selfCode]
    let regs := initialRegisters [Value.pointer pp, .pointer bp, .pointer zp]
    let loaded := loadRegisters regs 3 4 15 Cell.nil
    have last : Within code h loaded (.ret [.register 2]) [.pointer zp] h 3 := by
      simpa [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters] using
        Within.ret code h loaded [.register 2]
    exact Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
      (branches := ⟨.ret [.register 2], .fail,
        .call ids.self [.register 4, .register 1, .register 2] [5]
          (.call ids.mul [.register 1, .register 5] [6]
            (.call ids.add [.register 3, .register 6, .flag false] [7, 8] (.ret [.register 7]))),
        .fail, .fail, .fail⟩)
      (by simp [Atom.eval, regs, initialRegisters]) cell last
  | @cons pp dp tail pointers cell rest ih =>
    cases hr with
    | @cons _ digit _ digits digitAt digitsAt =>
      obtain ⟨mid, ep, extension, midValid, encodedAt, child⟩ := ih digitsAt
      obtain ⟨productHeap, productPtr, productExt, productValid, productAt, productRun⟩ :=
        RegisterMultiplier.multiply_compiled code ids.zero ids.mulAcc ids.shift ids.snoc ids.add
          zeroCode mulAccCode shiftCode snocCode addCode midValid (hb.mono extension) encodedAt
      let added := addCarryPointer n dp productPtr false productHeap
      have asafe := addCarryPointer_refines productValid
        ((digitAt.mono extension).mono productExt) productAt false
      have aeval := addCarryPointer_eval productValid
        ((digitAt.mono extension).mono productExt) productAt false
      have addRun := RegisterAdder.compiled code ids.add addCode aeval
      change Within code productHeap
        (initialRegisters [.pointer dp, .pointer productPtr, .flag false]) (code ids.add)
        [.pointer added.value.1, .flag added.value.2] added.heap (10 * added.trace.length) at addRun
      have alen : added.trace.length = 11 * n + 3 := asafe.2.2.2
      rw [alen] at addRun
      refine ⟨added.heap, added.value.1, extension.trans (productExt.trans asafe.1.1),
        asafe.1.2.1, asafe.2.1, ?_⟩
      let regs := initialRegisters [Value.pointer pp, .pointer bp, .pointer zp]
      let loaded := loadRegisters regs 3 4 15 (.cons dp tail)
      let encoded := bindResults loaded [5] [Value.pointer ep]
      let multiplied := bindResults encoded [6] [Value.pointer productPtr]
      let ready := bindResults multiplied [7, 8]
        [Value.pointer added.value.1, .flag added.value.2]
      have last : Within code added.heap ready (.ret [.register 7])
          [.pointer added.value.1] added.heap 3 := by
        simpa [values, Atom.eval, ready, bindResults] using Within.ret code added.heap ready [.register 7]
      have aargs : values multiplied [.register 3, .register 6, .flag false] =
          [.pointer dp, .pointer productPtr, .flag false] := by
        simp [values, Atom.eval, multiplied, encoded, loaded, bindResults, loadRegisters, decoded]
      have acall := Within.call (procedure := ids.add)
        (arguments := [.register 3, .register 6, .flag false]) (results := [7, 8])
        (regs := multiplied) (by simpa only [aargs] using addRun) last
      have margs : values encoded [.register 1, .register 5] = [.pointer bp, .pointer ep] := by
        simp [values, Atom.eval, encoded, loaded, regs, bindResults, loadRegisters, decoded, initialRegisters]
      have mcall := Within.call (procedure := ids.mul) (arguments := [.register 1, .register 5])
        (results := [6]) (regs := encoded) (by simpa only [margs, mulCode] using productRun) acall
      have eargs : values loaded [.register 4, .register 1, .register 2] =
          [.pointer tail, .pointer bp, .pointer zp] := by
        simp [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters]
      have ecall := Within.call (procedure := ids.self)
        (arguments := [.register 4, .register 1, .register 2]) (results := [5])
        (regs := loaded) (by simpa only [eargs] using child) mcall
      rw [selfCode]
      have load := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
        (branches := ⟨.ret [.register 2], .fail,
          .call ids.self [.register 4, .register 1, .register 2] [5]
            (.call ids.mul [.register 1, .register 5] [6]
              (.call ids.add [.register 3, .register 6, .flag false] [7, 8] (.ret [.register 7]))),
          .fail, .fail, .fail⟩)
        (by simp [Atom.eval, regs, initialRegisters]) cell ecall
      exact load.mono (by simp [digitBudget, Nat.mul_add]; omega)

theorem compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {pp bp zp : Ptr} {digits : List (Bits n)} {base : Bits n}
    (hd : ExpandedWords.WordsAt h pp digits)
    (hb : BitsAt h bp base) (hz : BitsAt h zp (Bits.zero n)) :
    ∃ out : Heap, ∃ result : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out result (encodeWords base digits) ∧
      Within code h (initialRegisters [.pointer pp, .pointer bp, .pointer zp]) (code ids.self)
        [.pointer result] out (digitBudget n * digits.length + 13) := by
  obtain ⟨pointers, hl, hr⟩ := hd
  exact compiled_aux code ids hcode hh hl hr hb hz

end WeightedMIS.RegisterHorner
