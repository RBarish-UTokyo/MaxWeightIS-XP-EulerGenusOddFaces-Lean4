module

public import WeightedMIS.RegisterRationalAdd

/-!
# A concrete finite program for exact binary rational arithmetic

Nineteen explicitly listed procedure bodies implement all arithmetic used by
rational elimination. The table is independent of the input dimensions and
values. Its dependency equalities are checked definitionally.
-/

@[expose] public section

namespace WeightedMIS.ArithmeticProgram

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

/-- One fixed finite table, with no host-language callback instruction. -/
def code : Code 19 := fun i =>
  match i.val with
  | 0 => RegisterZero.zeroBody 0
  | 1 => RegisterAdder.adderBody 1
  | 2 => RegisterComparator.comparatorBody 2
  | 3 => RegisterComplement.complementBody 3
  | 4 => RegisterSubtractor.subtractorBody 3 1
  | 5 => RegisterShift.snocBody 5
  | 6 => RegisterShift.shiftInBody 5
  | 7 => RegisterDivision.auxBody 7 6 2 4
  | 8 => RegisterDivision.divideBody 0 2 7
  | 9 => RegisterDivision.remainderBody 8
  | 10 => RegisterGCD.gcdBody 10 9 0 2
  | 11 => RegisterNormalization.normalizeBody 10 8
  | 12 => RegisterMultiplier.multiplyAccBody 12 6 1
  | 13 => RegisterMultiplier.multiplyBody 0 12
  | 14 => RegisterSignedAdd.signedAddBody 1 2 4
  | 15 => RegisterRationalAdd.addBody 13 14 11
  | 16 => RegisterRationalProducts.multiplyBody 13 11
  | 17 => RegisterRationalProducts.divideBody 16
  | _ => RegisterRationalAdd.subtractBody 15

def division : RegisterDivision.Procedures 19 :=
  ⟨0, 2, 7, 6, 5, 4, 3, 1, 8⟩

def products : RegisterRationalProducts.Procedures 19 :=
  ⟨division, 12, 13, 10, 9, 11⟩

theorem division_matches : division.Matches code :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem products_matches : products.Matches code :=
  ⟨division_matches, rfl, rfl, rfl, rfl, rfl⟩

/-- The concrete gcd entry terminates with the correct natural gcd. -/
theorem gcd_correct {n : ℕ} {h : Heap} (hh : Valid h) {ap bp : Ptr} {a b : Bits n}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) :
    ∃ out : Heap, ∃ result : Ptr, ∃ g : Bits n, Extends h out ∧ Valid out ∧
      BitsAt out result g ∧ g.value = Nat.gcd a.value b.value ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp]) (code 10)
        [.pointer result] out (1200 * (n + 1) ^ 3) :=
  RegisterGCD.compiled code division division_matches 10 9 rfl rfl hh ha hb

/-- The concrete addition entry performs reduced rational addition. -/
theorem add_correct {n : ℕ} {h : Heap} (hh : Valid h) (q r : BinaryRational.Word n)
    {ap dp bp ep : Ptr} (ha : BitsAt h ap q.magnitude) (hd : BitsAt h dp q.denominator)
    (hb : BitsAt h bp r.magnitude) (he : BitsAt h ep r.denominator)
    (hq : 0 < q.denominator.value) (hr : 0 < r.denominator.value)
    (hnum : q.magnitude.value * r.denominator.value +
      r.magnitude.value * q.denominator.value < 2 ^ n)
    (hden : q.denominator.value * r.denominator.value < 2 ^ n) :
    ∃ out : Heap, ∃ np denp : Ptr, ∃ z : BinaryRational.Word n,
      Extends h out ∧ Valid out ∧ BinaryRational.Canonical z ∧ z.value = q.value + r.value ∧
      BitsAt out np z.magnitude ∧ BitsAt out denp z.denominator ∧
      Within code h (initialRegisters [.flag q.negative, .pointer ap, .pointer dp,
          .flag r.negative, .pointer bp, .pointer ep])
        (code 15) [.flag z.negative, .pointer np, .pointer denp]
        out (3000 * (n + 1) ^ 3) :=
  RegisterRationalAdd.add_correct code products products_matches 14 rfl hh q r ha hd hb he hq hr hnum hden

/-- The concrete subtraction entry performs reduced rational subtraction. -/
theorem subtract_correct {n : ℕ} {h : Heap} (hh : Valid h) (q r : BinaryRational.Word n)
    {ap dp bp ep : Ptr} (ha : BitsAt h ap q.magnitude) (hd : BitsAt h dp q.denominator)
    (hb : BitsAt h bp r.magnitude) (he : BitsAt h ep r.denominator)
    (hq : 0 < q.denominator.value) (hr : 0 < r.denominator.value)
    (hnum : q.magnitude.value * r.denominator.value +
      r.magnitude.value * q.denominator.value < 2 ^ n)
    (hden : q.denominator.value * r.denominator.value < 2 ^ n) :
    ∃ out : Heap, ∃ np denp : Ptr, ∃ z : BinaryRational.Word n,
      Extends h out ∧ Valid out ∧ BinaryRational.Canonical z ∧ z.value = q.value - r.value ∧
      BitsAt out np z.magnitude ∧ BitsAt out denp z.denominator ∧
      Within code h (initialRegisters [.flag q.negative, .pointer ap, .pointer dp,
          .flag r.negative, .pointer bp, .pointer ep])
        (code 18) [.flag z.negative, .pointer np, .pointer denp]
        out (3100 * (n + 1) ^ 3) :=
  RegisterRationalAdd.subtract_correct code products products_matches 14 15 rfl rfl
    hh q r ha hd hb he hq hr hnum hden

/-- The concrete multiplication entry performs reduced rational multiplication. -/
theorem multiply_correct {n : ℕ} {h : Heap} (hh : Valid h) (q r : BinaryRational.Word n)
    {ap dp bp ep : Ptr} (ha : BitsAt h ap q.magnitude) (hd : BitsAt h dp q.denominator)
    (hb : BitsAt h bp r.magnitude) (he : BitsAt h ep r.denominator)
    (hq : 0 < q.denominator.value) (hr : 0 < r.denominator.value)
    (hnum : q.magnitude.value * r.magnitude.value < 2 ^ n)
    (hden : q.denominator.value * r.denominator.value < 2 ^ n) :
    ∃ out : Heap, ∃ np denp : Ptr, ∃ z : BinaryRational.Word n,
      Extends h out ∧ Valid out ∧ BinaryRational.Canonical z ∧ z.value = q.value * r.value ∧
      BitsAt out np z.magnitude ∧ BitsAt out denp z.denominator ∧
      Within code h (initialRegisters [.flag q.negative, .pointer ap, .pointer dp,
          .flag r.negative, .pointer bp, .pointer ep])
        (code 16) [.flag z.negative, .pointer np, .pointer denp]
        out (3000 * (n + 1) ^ 3) :=
  RegisterRationalProducts.multiply_correct code products products_matches hh q r ha hd hb he hq hr hnum hden

/-- The concrete division entry performs reduced rational division. -/
theorem divide_correct {n : ℕ} {h : Heap} (hh : Valid h) (q r : BinaryRational.Word n)
    {ap dp bp ep : Ptr} (ha : BitsAt h ap q.magnitude) (hd : BitsAt h dp q.denominator)
    (hb : BitsAt h bp r.magnitude) (he : BitsAt h ep r.denominator)
    (hq : 0 < q.denominator.value) (hr : 0 < r.denominator.value) (hrn : 0 < r.magnitude.value)
    (hnum : q.magnitude.value * r.denominator.value < 2 ^ n)
    (hden : q.denominator.value * r.magnitude.value < 2 ^ n) :
    ∃ out : Heap, ∃ np denp : Ptr, ∃ z : BinaryRational.Word n,
      Extends h out ∧ Valid out ∧ BinaryRational.Canonical z ∧ z.value = q.value / r.value ∧
      BitsAt out np z.magnitude ∧ BitsAt out denp z.denominator ∧
      Within code h (initialRegisters [.flag q.negative, .pointer ap, .pointer dp,
          .flag r.negative, .pointer bp, .pointer ep])
        (code 17) [.flag z.negative, .pointer np, .pointer denp]
        out (3100 * (n + 1) ^ 3) :=
  RegisterRationalProducts.divide_correct code products products_matches 16 rfl
    hh q r ha hd hb he hq hr hrn hnum hden

end WeightedMIS.ArithmeticProgram
