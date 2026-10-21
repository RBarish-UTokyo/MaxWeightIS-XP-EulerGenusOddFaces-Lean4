module

public import WeightedMIS.SignedWords
public import WeightedMIS.RegisterMultiplier
public import WeightedMIS.CompiledTrie

/-!
# A compiled signed dot product against nonnegative histogram counts

The two input lists are traversed in their actual stored order. Products use the
bitwise multiplier and the accumulating sum uses signed binary addition.
-/

@[expose] public section

namespace WeightedMIS.RegisterSignedDot

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.RegisterPotentialStep
open WeightedMIS.SignedWords WeightedMIS.ExpandedWords

variable {n : ℕ}

def dot : List (Word n) → List (Bits n) → Word n
  | a :: as, b :: bs =>
      let r := dot as bs
      (BinaryRational.signedAdd a.1 r.1 (Bits.multiply a.2 b).1 r.2).1
  | _, _ => (false, Bits.zero n)

def integerDot : List (Word n) → List (Bits n) → ℤ
  | a :: as, b :: bs => value a * b.value + integerDot as bs
  | _, _ => 0

def mass : List (Word n) → List (Bits n) → ℕ
  | a :: as, b :: bs => a.2.value * b.value + mass as bs
  | _, _ => 0

theorem dot_correct (as : List (Word n)) (bs : List (Bits n))
    (hwidth : mass as bs < 2 ^ n) :
    value (dot as bs) = integerDot as bs ∧ (dot as bs).2.value ≤ mass as bs := by
  induction as generalizing bs with
  | nil => simp [dot, integerDot, mass, value, BinaryRational.signed]
  | cons a as ih =>
    cases bs with
    | nil => simp [dot, integerDot, mass, value, BinaryRational.signed]
    | cons b bs =>
      have ht : mass as bs < 2 ^ n := by simpa only [mass] using (show a.2.value*b.value+mass as bs < 2^n from hwidth) |> (fun h => by omega)
      obtain ⟨hv, hm⟩ := ih bs ht
      have hp : a.2.value*b.value < 2^n := by change a.2.value*b.value+mass as bs < 2^n at hwidth; omega
      have hprod := Bits.multiply_value_of_lt a.2 b hp
      have hsum : (Bits.multiply a.2 b).1.value + (dot as bs).2.value < 2^n := by
        rw [hprod]
        change a.2.value*b.value+mass as bs < 2^n at hwidth
        omega
      have hadd := BinaryRational.signedAdd_value a.1 (dot as bs).1 (Bits.multiply a.2 b).1 (dot as bs).2 hsum
      have heq : value (dot (a::as) (b::bs)) = value a * b.value + value (dot as bs) := by
        simp only [dot, value]
        rw [hadd, hprod]
        cases ha : a.1 <;> simp [value, BinaryRational.signed, ha, Int.natCast_mul]
      constructor
      · simpa only [integerDot, hv] using heq
      · rw [← value_natAbs, heq]
        have hbound := Int.natAbs_add_le (value a * b.value) (value (dot as bs))
        simp only [Int.natAbs_mul, value_natAbs, Int.natAbs_natCast] at hbound
        change _ ≤ a.2.value*b.value+mass as bs
        omega

variable {p : ℕ}

structure Procedures (p : ℕ) where
  zero : Fin p
  add : Fin p
  cmp : Fin p
  complement : Fin p
  sub : Fin p
  snoc : Fin p
  shift : Fin p
  mulAcc : Fin p
  multiply : Fin p
  signedAdd : Fin p

def Matches (code : Code p) (ids : Procedures p) : Prop :=
  code ids.zero = RegisterZero.zeroBody ids.zero ∧
  code ids.add = RegisterAdder.adderBody ids.add ∧
  code ids.cmp = RegisterComparator.comparatorBody ids.cmp ∧
  code ids.complement = RegisterComplement.complementBody ids.complement ∧
  code ids.sub = RegisterSubtractor.subtractorBody ids.complement ids.add ∧
  code ids.snoc = RegisterShift.snocBody ids.snoc ∧
  code ids.shift = RegisterShift.shiftInBody ids.snoc ∧
  code ids.mulAcc = RegisterMultiplier.multiplyAccBody ids.mulAcc ids.shift ids.add ∧
  code ids.multiply = RegisterMultiplier.multiplyBody ids.zero ids.mulAcc ∧
  code ids.signedAdd = RegisterSignedAdd.signedAddBody ids.add ids.cmp ids.sub

def sumBody (ids : Procedures p) : Command p :=
  .call ids.signedAdd [.register 8, .register 11, .register 12, .register 13] [14, 15]
    (.ret [.register 14, .register 15])

def recurseBody (self : Fin p) (ids : Procedures p) : Command p :=
  .call self [.register 4, .register 6, .register 2] [12, 13] (sumBody ids)

def productBody (self : Fin p) (ids : Procedures p) : Command p :=
  .call ids.multiply [.register 7, .register 5] [11] (recurseBody self ids)

def recordBody (self : Fin p) (ids : Procedures p) : Command p :=
  .load (.register 3) 7 10 8 (RegisterAdder.nilBitCases .fail (productBody self ids))

/-- Input: signed coefficient list, unsigned count list, zero word.
Output: signed dot product. -/
def dotBody (self : Fin p) (ids : Procedures p) : Command p :=
  .load (.register 0) 3 4 10 { CompiledTrie.failCases with
    nil := .ret [.flag false, .register 2]
    cons := .load (.register 1) 5 6 10 { CompiledTrie.failCases with
      cons := recordBody self ids } }

def budget (width length : ℕ) : ℕ := 500 * (width + 1)^2 * length + 15

theorem compiled (code : Code p) (self : Fin p) (ids : Procedures p)
    (hself : code self = dotBody self ids) (hmatches : Matches code ids)
    {h : Heap} (hh : Valid h) {ap bp zp : Ptr}
    {as : List (Word n)} {bs : List (Bits n)}
    (ha : SignedWords.ListAt h ap as) (hb : WordsAt h bp bs)
    (hz : BitsAt h zp (Bits.zero n)) (hlen : as.length = bs.length) :
    ∃ out result, Extends h out ∧ Valid out ∧ BitsAt out result (dot as bs).2 ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp, .pointer zp])
        (code self) [.flag (dot as bs).1, .pointer result] out (budget n as.length) := by
  obtain ⟨hzero, hadd, hcmp, hcomp, hsub, hsnoc, hshift, hmulAcc, hmul, hsigned⟩ := hmatches
  induction as generalizing bs h ap bp with
  | nil =>
    cases bs with
    | cons b bs => simp at hlen
    | nil =>
      have cell := SignedWords.ListAt.nil_iff.mp ha
      let regs := initialRegisters [Value.pointer ap, .pointer bp, .pointer zp]
      have last : Within code h (loadRegisters regs 3 4 10 .nil)
          (.ret [.flag false, .register 2]) [.flag false, .pointer zp] h 5 := by
        simpa [regs, initialRegisters, loadRegisters, decoded, values, Atom.eval] using
          Within.ret code h (loadRegisters regs 3 4 10 .nil) [.flag false, .register 2]
      have load := Within.load (regs := regs) (address := .register 0) (first := 3) (second := 4) (bit := 10)
        (branches := { CompiledTrie.failCases with
          nil := .ret [.flag false, .register 2]
          cons := .load (.register 1) 5 6 10 { CompiledTrie.failCases with cons := recordBody self ids } })
        (by simp [regs, initialRegisters, Atom.eval]) cell last
      refine ⟨h, zp, .refl h, hh, hz, ?_⟩
      simpa [hself, dotBody, dot, budget] using load
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlength : as.length = bs.length := by simpa using hlen
      obtain ⟨ah, atail, acell, hhead, htail⟩ := SignedWords.ListAt.cons_iff.mp ha
      obtain ⟨am, arecord, amag⟩ := hhead
      obtain ⟨bh, bt, bcell, bmag, btail⟩ := WordsAt.cons_iff.mp hb
      obtain ⟨mid, mp, hx, hv, hprod, hproduct⟩ :=
        RegisterMultiplier.multiply_compiled code ids.zero ids.mulAcc ids.shift ids.snoc ids.add
          hzero hmulAcc hshift hsnoc hadd hh amag bmag
      obtain ⟨next, rp, hy, hw, hrest, hrecursive⟩ := ih hv (htail.mono hx) (btail.mono hx) (hz.mono hx) hlength
      obtain ⟨out, result, he, hvalid, hresult, hsum⟩ :=
        RegisterSignedAdd.compiled code ids.cmp ids.sub ids.complement ids.add hcmp hsub hcomp hadd hw
          (hprod.mono hy) hrest a.1 (dot as bs).1
      let regs := initialRegisters [Value.pointer ap, .pointer bp, .pointer zp]
      let first := loadRegisters regs 3 4 10 (.cons ah atail)
      let second := loadRegisters first 5 6 10 (.cons bh bt)
      let loaded := loadRegisters second 7 10 8 (.bit a.1 am)
      let product := bindResults loaded [11] [Value.pointer mp]
      let recursed := bindResults product [12, 13] [Value.flag (dot as bs).1, .pointer rp]
      let done := bindResults recursed [14, 15] [Value.flag (dot (a::as) (b::bs)).1, .pointer result]
      have last : Within code out done (.ret [.register 14, .register 15])
          [.flag (dot (a::as) (b::bs)).1, .pointer result] out 5 := by
        simpa [done, bindResults, values, Atom.eval] using Within.ret code out done [.register 14, .register 15]
      have sargs : values recursed [.register 8, .register 11, .register 12, .register 13] =
          [.flag a.1, .pointer mp, .flag (dot as bs).1, .pointer rp] := by
        simp [recursed, product, loaded, bindResults, loadRegisters, decoded, values, Atom.eval]
      have sum := Within.call (procedure := ids.signedAdd) (regs := recursed)
        (arguments := [.register 8, .register 11, .register 12, .register 13]) (results := [14, 15])
        (by simpa only [sargs, hsigned, dot] using hsum) last
      have rargs : values product [.register 4, .register 6, .register 2] =
          [.pointer atail, .pointer bt, .pointer zp] := by
        simp [product, loaded, second, first, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
      have recurse := Within.call (procedure := self) (regs := product)
        (arguments := [.register 4, .register 6, .register 2]) (results := [12, 13])
        (by simpa only [rargs] using hrecursive) sum
      have margs : values loaded [.register 7, .register 5] = [.pointer am, .pointer bh] := by
        simp [loaded, second, loadRegisters, decoded, values, Atom.eval]
      have multiply := Within.call (procedure := ids.multiply) (regs := loaded)
        (arguments := [.register 7, .register 5]) (results := [11])
        (by simpa only [margs, hmul] using hproduct) recurse
      have loadRecord := Within.load (regs := second) (address := .register 3)
        (first := 7) (second := 10) (bit := 8)
        (branches := RegisterAdder.nilBitCases .fail (productBody self ids))
        (by simp [second, first, loadRegisters, decoded, Atom.eval]) arecord multiply
      have loadCount := Within.load (regs := first) (address := .register 1)
        (first := 5) (second := 6) (bit := 10)
        (branches := { CompiledTrie.failCases with cons := recordBody self ids })
        (by simp [first, regs, loadRegisters, decoded, initialRegisters, Atom.eval]) bcell loadRecord
      have loadList := Within.load (regs := regs) (address := .register 0)
        (first := 3) (second := 4) (bit := 10)
        (branches := { CompiledTrie.failCases with
          nil := .ret [.flag false, .register 2]
          cons := .load (.register 1) 5 6 10 { CompiledTrie.failCases with cons := recordBody self ids } })
        (by simp [regs, initialRegisters, Atom.eval]) acell loadCount
      refine ⟨out, result, hx.trans (hy.trans he), hvalid, hresult, ?_⟩
      rw [hself]
      exact loadList.mono (by simp [budget, pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]; omega)

end WeightedMIS.RegisterSignedDot
