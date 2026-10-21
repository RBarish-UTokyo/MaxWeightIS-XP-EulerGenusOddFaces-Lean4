module

public import WeightedMIS.RegisterNormalization
public import WeightedMIS.RegisterMultiplier

/-!
# Compiled rational multiplication and division

The six input registers contain two sign/magnitude/denominator triples.
Multiplication executes two binary word products, dispatches on the sign bits,
and invokes the compiled Euclidean normalizer. Division exchanges the right
numerator and denominator before executing the same closed product routine.
-/

@[expose] public section

namespace WeightedMIS.RegisterRationalProducts

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def finishBody (normalize : Fin p) (sign : Bool) : Command p :=
  .call normalize [.flag sign, .register 6, .register 7] [8, 9, 10]
    (.ret [.register 8, .register 9, .register 10])

def signBody (normalize : Fin p) : Command p :=
  .branch (.register 0)
    (.branch (.register 3) (finishBody normalize false) (finishBody normalize true))
    (.branch (.register 3) (finishBody normalize true) (finishBody normalize false))

def multiplyBody (multiply normalize : Fin p) : Command p :=
  .call multiply [.register 1, .register 4] [6]
    (.call multiply [.register 2, .register 5] [7] (signBody normalize))

/-- Rational division needs no new integer arithmetic procedure. -/
def divideBody (rationalMultiply : Fin p) : Command p :=
  .call rationalMultiply [.register 0, .register 1, .register 2,
      .register 3, .register 5, .register 4] [6, 7, 8]
    (.ret [.register 6, .register 7, .register 8])

/-- The dependencies name specific closed bodies, not assumed arithmetic
oracles or uncosted host operations. -/
structure Procedures (p : ℕ) where
  division : RegisterDivision.Procedures p
  mulAcc : Fin p
  multiply : Fin p
  gcd : Fin p
  remainder : Fin p
  normalize : Fin p

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  d.division.Matches code ∧
  code d.mulAcc = RegisterMultiplier.multiplyAccBody d.mulAcc d.division.shift d.division.add ∧
  code d.multiply = RegisterMultiplier.multiplyBody d.division.zero d.mulAcc ∧
  code d.gcd = RegisterGCD.gcdBody d.gcd d.remainder d.division.zero d.division.cmp ∧
  code d.remainder = RegisterDivision.remainderBody d.division.divide ∧
  code d.normalize = RegisterNormalization.normalizeBody d.gcd d.division.divide

theorem sign_compiled {code : Code p} {normalize : Fin p} {h out : Heap} {regs : Registers}
    {s t : Bool} {outputs : List Value} {budget : ℕ}
    (hs : regs 0 = .flag s) (ht : regs 3 = .flag t)
    (he : Within code h regs (finishBody normalize (xor s t)) outputs out budget) :
    Within code h regs (signBody normalize) outputs out (3 + (3 + budget)) := by
  cases s <;> cases t <;>
    apply Within.branch (budget := 3 + budget) (by simpa [Atom.eval] using hs) <;>
    apply Within.branch (budget := budget) (by simpa [Atom.eval] using ht) <;>
    simpa using he

/-- Exact machine refinement of the binary rational product, including both
raw multiplications and normalization. No arithmetic overflow assumption is
needed for refinement; such assumptions are used only for rational correctness. -/
theorem multiply_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {n : ℕ} {h : Heap} (hh : Valid h) (q r : BinaryRational.Word n)
    {ap dp bp ep : Ptr} (ha : BitsAt h ap q.magnitude) (hd : BitsAt h dp q.denominator)
    (hb : BitsAt h bp r.magnitude) (he : BitsAt h ep r.denominator) :
    ∃ out : Heap, ∃ np denp : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out np (BinaryRational.multiply q r).1.magnitude ∧
      BitsAt out denp (BinaryRational.multiply q r).1.denominator ∧
      Within code h (initialRegisters [.flag q.negative, .pointer ap, .pointer dp,
          .flag r.negative, .pointer bp, .pointer ep])
        (multiplyBody d.multiply d.normalize)
        [.flag (BinaryRational.multiply q r).1.negative, .pointer np, .pointer denp]
        out (3000 * (n + 1) ^ 3) := by
  rcases hm with ⟨hdm, hmacc, hmul, hgcd, hrem, hnorm⟩
  have hdm' := hdm
  rcases hdm' with ⟨hz, hc, hx, hs, hsn, hsu, hco, had, hdv⟩
  obtain ⟨h₁, mp, hext₁, hv₁, hmp, hm₁⟩ :=
    RegisterMultiplier.multiply_compiled code d.division.zero d.mulAcc d.division.shift
      d.division.snoc d.division.add hz hmacc hs hsn had hh ha hb
  rw [← hmul] at hm₁
  obtain ⟨h₂, dmp, hext₂, hv₂, hdmp, hm₂⟩ :=
    RegisterMultiplier.multiply_compiled code d.division.zero d.mulAcc d.division.shift
      d.division.snoc d.division.add hz hmacc hs hsn had hv₁ (hd.mono hext₁) (he.mono hext₁)
  rw [← hmul] at hm₂
  let raw : BinaryRational.Word n := ⟨xor q.negative r.negative,
    (Bits.multiply q.magnitude r.magnitude).1,
    (Bits.multiply q.denominator r.denominator).1⟩
  obtain ⟨out, np, denp, hext₃, hv₃, hnp, hdenp, hn⟩ :=
    RegisterNormalization.compiled code d.division hdm d.gcd d.remainder hgcd hrem
      hv₂ raw (hmp.mono hext₂) hdmp
  rw [← hnorm] at hn
  refine ⟨out, np, denp, hext₁.trans (hext₂.trans hext₃), hv₃, hnp, hdenp, ?_⟩
  let regs := initialRegisters [Value.flag q.negative, .pointer ap, .pointer dp,
    .flag r.negative, .pointer bp, .pointer ep]
  let numDone := bindResults regs [6] [Value.pointer mp]
  let denDone := bindResults numDone [7] [Value.pointer dmp]
  let finished := bindResults denDone [8, 9, 10]
    [Value.flag raw.negative, .pointer np, .pointer denp]
  have last : Within code out finished (.ret [.register 8, .register 9, .register 10])
      [.flag raw.negative, .pointer np, .pointer denp] out 7 := by
    simpa [finished, bindResults, values, Atom.eval] using
      Within.ret code out finished [.register 8, .register 9, .register 10]
  have hargsN : values denDone [.flag raw.negative, .register 6, .register 7] =
      [.flag raw.negative, .pointer mp, .pointer dmp] := by
    simp [denDone, numDone, bindResults, values, Atom.eval]
  have hcallN := Within.call (procedure := d.normalize) (regs := denDone)
    (arguments := [.flag raw.negative, .register 6, .register 7]) (results := [8, 9, 10])
    (by simpa only [hargsN] using hn) last
  have hsign := sign_compiled
    (by simp [denDone, numDone, regs, bindResults, initialRegisters])
    (by simp [denDone, numDone, regs, bindResults, initialRegisters]) hcallN
  have hargsD : values numDone [.register 2, .register 5] = [.pointer dp, .pointer ep] := by
    simp [numDone, regs, bindResults, initialRegisters, values, Atom.eval]
  have hcallD := Within.call (procedure := d.multiply) (regs := numDone)
    (arguments := [.register 2, .register 5]) (results := [7])
    (by simpa only [hargsD] using hm₂) hsign
  have hargsM : values regs [.register 1, .register 4] = [.pointer ap, .pointer bp] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have hcallM := Within.call (procedure := d.multiply) (regs := regs)
    (arguments := [.register 1, .register 4]) (results := [6])
    (by simpa only [hargsM] using hm₁) hcallD
  exact hcallM.mono (by simp only [List.length_cons, List.length_nil]; nlinarith [Nat.zero_le (n ^ 3)])

/-- The represented output is the canonical exact rational product when its
raw integer products fit in the working width. -/
theorem multiply_correct (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {n : ℕ} {h : Heap} (hh : Valid h) (q r : BinaryRational.Word n)
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
        (multiplyBody d.multiply d.normalize) [.flag z.negative, .pointer np, .pointer denp]
        out (3000 * (n + 1) ^ 3) := by
  obtain ⟨out, np, denp, hext, hv, hn, hdn, hx⟩ := multiply_compiled code d hm hh q r ha hd hb he
  exact ⟨out, np, denp, (BinaryRational.multiply q r).1, hext, hv,
    BinaryRational.multiply_canonical q r hq hr hden,
    BinaryRational.multiply_value q r hq hr hnum hden, hn, hdn, hx⟩

/-- The finite division wrapper returns exactly the arrays computed by binary
rational division; swapping two input pointers requires only register moves. -/
theorem divide_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    (rationalMultiply : Fin p) (hprod : code rationalMultiply = multiplyBody d.multiply d.normalize)
    {n : ℕ} {h : Heap} (hh : Valid h) (q r : BinaryRational.Word n)
    {ap dp bp ep : Ptr} (ha : BitsAt h ap q.magnitude) (hd : BitsAt h dp q.denominator)
    (hb : BitsAt h bp r.magnitude) (he : BitsAt h ep r.denominator) :
    ∃ out : Heap, ∃ np denp : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out np (BinaryRational.divide q r).1.magnitude ∧
      BitsAt out denp (BinaryRational.divide q r).1.denominator ∧
      Within code h (initialRegisters [.flag q.negative, .pointer ap, .pointer dp,
          .flag r.negative, .pointer bp, .pointer ep])
        (divideBody rationalMultiply)
        [.flag (BinaryRational.divide q r).1.negative, .pointer np, .pointer denp]
        out (3100 * (n + 1) ^ 3) := by
  let reciprocal : BinaryRational.Word n := ⟨r.negative, r.denominator, r.magnitude⟩
  obtain ⟨out, np, denp, hext, hv, hn, hdn, hx⟩ :=
    multiply_compiled code d hm hh q reciprocal ha hd he hb
  rw [← hprod] at hx
  refine ⟨out, np, denp, hext, hv, hn, hdn, ?_⟩
  let regs := initialRegisters [Value.flag q.negative, .pointer ap, .pointer dp,
    .flag r.negative, .pointer bp, .pointer ep]
  let returned := bindResults regs [6, 7, 8]
    [Value.flag (BinaryRational.divide q r).1.negative, .pointer np, .pointer denp]
  have last : Within code out returned (.ret [.register 6, .register 7, .register 8])
      [.flag (BinaryRational.divide q r).1.negative, .pointer np, .pointer denp] out 7 := by
    simpa [returned, bindResults, values, Atom.eval] using
      Within.ret code out returned [.register 6, .register 7, .register 8]
  have hargs : values regs [.register 0, .register 1, .register 2,
        .register 3, .register 5, .register 4] =
      [.flag q.negative, .pointer ap, .pointer dp, .flag r.negative, .pointer ep, .pointer bp] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have call := Within.call (procedure := rationalMultiply) (regs := regs)
    (arguments := [.register 0, .register 1, .register 2, .register 3, .register 5, .register 4])
    (results := [6, 7, 8]) (by simpa only [hargs, reciprocal, BinaryRational.multiply, BinaryRational.divide] using hx) last
  exact call.mono (by
    have hp : 0 < (n + 1) ^ 3 := by positivity
    simp only [List.length_cons, List.length_nil]
    omega)

/-- Canonical exact rational division, for a nonzero divisor and sufficient
binary width for both crossed products. -/
theorem divide_correct (code : Code p) (d : Procedures p) (hm : d.Matches code)
    (rationalMultiply : Fin p) (hprod : code rationalMultiply = multiplyBody d.multiply d.normalize)
    {n : ℕ} {h : Heap} (hh : Valid h) (q r : BinaryRational.Word n)
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
        (divideBody rationalMultiply) [.flag z.negative, .pointer np, .pointer denp]
        out (3100 * (n + 1) ^ 3) := by
  obtain ⟨out, np, denp, hext, hv, hn, hdn, hx⟩ :=
    divide_compiled code d hm rationalMultiply hprod hh q r ha hd hb he
  exact ⟨out, np, denp, (BinaryRational.divide q r).1, hext, hv,
    BinaryRational.divide_canonical q r hq hrn hden,
    BinaryRational.divide_value q r hq hr hrn hnum hden, hn, hdn, hx⟩

end WeightedMIS.RegisterRationalProducts
