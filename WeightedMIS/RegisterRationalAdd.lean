module

public import WeightedMIS.RegisterSignedAdd
public import WeightedMIS.RegisterRationalProducts

/-! # Closed register code for exact rational addition and subtraction -/

@[expose] public section

namespace WeightedMIS.RegisterRationalAdd

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def addBody (multiply signedAdd normalize : Fin p) : Command p :=
  .call multiply [.register 1, .register 5] [6]
    (.call multiply [.register 4, .register 2] [7]
      (.call multiply [.register 2, .register 5] [8]
        (.call signedAdd [.register 0, .register 6, .register 3, .register 7] [9, 10]
          (.call normalize [.register 9, .register 10, .register 8] [11, 12, 13]
            (.ret [.register 11, .register 12, .register 13])))))

theorem add_compiled (code : Code p) (d : RegisterRationalProducts.Procedures p)
    (hm : d.Matches code) (signedAdd : Fin p)
    (hsa : code signedAdd = RegisterSignedAdd.signedAddBody d.division.add d.division.cmp d.division.sub)
    {n : ℕ} {h : Heap} (hh : Valid h) (q r : BinaryRational.Word n)
    {ap dp bp ep : Ptr} (ha : BitsAt h ap q.magnitude) (hd : BitsAt h dp q.denominator)
    (hb : BitsAt h bp r.magnitude) (he : BitsAt h ep r.denominator) :
    ∃ out : Heap, ∃ np denp : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out np (BinaryRational.add q r).1.magnitude ∧
      BitsAt out denp (BinaryRational.add q r).1.denominator ∧
      Within code h (initialRegisters [.flag q.negative, .pointer ap, .pointer dp,
          .flag r.negative, .pointer bp, .pointer ep])
        (addBody d.multiply signedAdd d.normalize)
        [.flag (BinaryRational.add q r).1.negative, .pointer np, .pointer denp]
        out (3000 * (n + 1) ^ 3) := by
  rcases hm with ⟨hdivision, hacc, hmul, hgcd, hrem, hnorm⟩
  rcases hdivision with ⟨hz, hc, hx, hs, hsn, hsu, hco, had, hdv⟩
  have hdiv : d.division.Matches code := ⟨hz, hc, hx, hs, hsn, hsu, hco, had, hdv⟩
  obtain ⟨ah, acp, haext, havalid, harep, hae⟩ :=
    RegisterMultiplier.multiply_compiled code d.division.zero d.mulAcc d.division.shift d.division.snoc d.division.add
      hz hacc hs hsn had hh ha he
  rw [← hmul] at hae
  obtain ⟨bh, bcp, hbext, hbvalid, hbrep, hbe⟩ :=
    RegisterMultiplier.multiply_compiled code d.division.zero d.mulAcc d.division.shift d.division.snoc d.division.add
      hz hacc hs hsn had havalid (hb.mono haext) (hd.mono haext)
  rw [← hmul] at hbe
  have habext := haext.trans hbext
  obtain ⟨dh, dcp, hdext, hdvalid, hdrep, hde⟩ :=
    RegisterMultiplier.multiply_compiled code d.division.zero d.mulAcc d.division.shift d.division.snoc d.division.add
      hz hacc hs hsn had hbvalid (hd.mono habext) (he.mono habext)
  rw [← hmul] at hde
  let a := (Bits.multiply q.magnitude r.denominator).1
  let b := (Bits.multiply r.magnitude q.denominator).1
  let den := (Bits.multiply q.denominator r.denominator).1
  let sum := (BinaryRational.signedAdd q.negative r.negative a b).1
  obtain ⟨sh, sp, hsext, hsvalid, hsrep, hse⟩ :=
    RegisterSignedAdd.compiled code d.division.cmp d.division.sub d.division.complement d.division.add
      hc hsu hco had hdvalid (harep.mono (hbext.trans hdext)) (hbrep.mono hdext)
      q.negative r.negative
  rw [← hsa] at hse
  let raw : BinaryRational.Word n := ⟨sum.1, sum.2, den⟩
  obtain ⟨out, np, denp, hnex, hnvalid, hnrep, hdoutrep, hne⟩ :=
    RegisterNormalization.compiled code d.division hdiv d.gcd d.remainder hgcd hrem hsvalid raw
      hsrep (hdrep.mono hsext)
  rw [← hnorm] at hne
  refine ⟨out, np, denp, haext.trans (hbext.trans (hdext.trans (hsext.trans hnex))),
    hnvalid, hnrep, hdoutrep, ?_⟩
  let regs := initialRegisters [Value.flag q.negative, .pointer ap, .pointer dp,
    .flag r.negative, .pointer bp, .pointer ep]
  let aDone := bindResults regs [6] [Value.pointer acp]
  let bDone := bindResults aDone [7] [Value.pointer bcp]
  let dDone := bindResults bDone [8] [Value.pointer dcp]
  let sDone := bindResults dDone [9, 10] [Value.flag sum.1, .pointer sp]
  let nDone := bindResults sDone [11, 12, 13] [Value.flag sum.1, .pointer np, .pointer denp]
  have last : Within code out nDone (.ret [.register 11, .register 12, .register 13])
      [.flag sum.1, .pointer np, .pointer denp] out 7 := by
    simpa [nDone, bindResults, values, Atom.eval] using
      Within.ret code out nDone [.register 11, .register 12, .register 13]
  have hargsN : values sDone [.register 9, .register 10, .register 8] =
      [.flag sum.1, .pointer sp, .pointer dcp] := by
    simp [sDone, dDone, bindResults, values, Atom.eval]
  have hcallN := Within.call (procedure := d.normalize) (arguments := [.register 9, .register 10, .register 8])
    (results := [11, 12, 13]) (regs := sDone) (returned := [.flag sum.1, .pointer np, .pointer denp])
    (by simpa only [hargsN] using hne) last
  have hargsS : values dDone [.register 0, .register 6, .register 3, .register 7] =
      [.flag q.negative, .pointer acp, .flag r.negative, .pointer bcp] := by
    simp [dDone, bDone, aDone, regs, bindResults, values, Atom.eval, initialRegisters]
  have hcallS := Within.call (procedure := signedAdd)
    (arguments := [.register 0, .register 6, .register 3, .register 7])
    (results := [9, 10]) (regs := dDone) (returned := [.flag sum.1, .pointer sp])
    (by simpa only [hargsS] using hse) hcallN
  have hargsD : values bDone [.register 2, .register 5] = [.pointer dp, .pointer ep] := by
    simp [bDone, aDone, regs, bindResults, values, Atom.eval, initialRegisters]
  have hcallD := Within.call (procedure := d.multiply) (arguments := [.register 2, .register 5])
    (results := [8]) (regs := bDone) (returned := [.pointer dcp])
    (by simpa only [hargsD] using hde) hcallS
  have hargsB : values aDone [.register 4, .register 2] = [.pointer bp, .pointer dp] := by
    simp [aDone, regs, bindResults, values, Atom.eval, initialRegisters]
  have hcallB := Within.call (procedure := d.multiply) (arguments := [.register 4, .register 2])
    (results := [7]) (regs := aDone) (returned := [.pointer bcp])
    (by simpa only [hargsB] using hbe) hcallD
  have hargsA : values regs [.register 1, .register 5] = [.pointer ap, .pointer ep] := by
    simp [regs, values, Atom.eval, initialRegisters]
  have hcallA := Within.call (procedure := d.multiply) (arguments := [.register 1, .register 5])
    (results := [6]) (regs := regs) (returned := [.pointer acp])
    (by simpa only [hargsA] using hae) hcallB
  exact hcallA.mono (by simp only [List.length_cons, List.length_nil]; ring_nf; omega)

theorem add_correct (code : Code p) (d : RegisterRationalProducts.Procedures p)
    (hm : d.Matches code) (signedAdd : Fin p)
    (hsa : code signedAdd = RegisterSignedAdd.signedAddBody d.division.add d.division.cmp d.division.sub)
    {n : ℕ} {h : Heap} (hh : Valid h) (q r : BinaryRational.Word n)
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
        (addBody d.multiply signedAdd d.normalize) [.flag z.negative, .pointer np, .pointer denp]
        out (3000 * (n + 1) ^ 3) := by
  obtain ⟨out, np, denp, hx, hv, hn, hdn, he⟩ := add_compiled code d hm signedAdd hsa hh q r ha hd hb he
  exact ⟨out, np, denp, (BinaryRational.add q r).1, hx, hv,
    BinaryRational.add_canonical q r hq hr hden, BinaryRational.add_value q r hq hr hnum hden,
    hn, hdn, he⟩

def subtractCase (add : Fin p) (rightSign : Bool) : Command p :=
  .call add [.register 0, .register 1, .register 2, .flag rightSign, .register 4, .register 5]
    [6, 7, 8] (.ret [.register 6, .register 7, .register 8])

def subtractBody (add : Fin p) : Command p :=
  .branch (.register 3) (subtractCase add false) (subtractCase add true)

theorem subtract_compiled (code : Code p) (d : RegisterRationalProducts.Procedures p)
    (hm : d.Matches code) (signedAdd rationalAdd : Fin p)
    (hsa : code signedAdd = RegisterSignedAdd.signedAddBody d.division.add d.division.cmp d.division.sub)
    (hadd : code rationalAdd = addBody d.multiply signedAdd d.normalize)
    {n : ℕ} {h : Heap} (hh : Valid h) (q r : BinaryRational.Word n)
    {ap dp bp ep : Ptr} (ha : BitsAt h ap q.magnitude) (hd : BitsAt h dp q.denominator)
    (hb : BitsAt h bp r.magnitude) (he : BitsAt h ep r.denominator) :
    ∃ out : Heap, ∃ np denp : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out np (BinaryRational.subtract q r).1.magnitude ∧
      BitsAt out denp (BinaryRational.subtract q r).1.denominator ∧
      Within code h (initialRegisters [.flag q.negative, .pointer ap, .pointer dp,
          .flag r.negative, .pointer bp, .pointer ep])
        (subtractBody rationalAdd)
        [.flag (BinaryRational.subtract q r).1.negative, .pointer np, .pointer denp]
        out (3100 * (n + 1) ^ 3) := by
  obtain ⟨out, np, denp, hx, hv, hn, hdn, he⟩ :=
    add_compiled code d hm signedAdd hsa hh q (BinaryRational.negate r) ha hd hb he
  rw [← hadd] at he
  refine ⟨out, np, denp, hx, hv, hn, hdn, ?_⟩
  let sign := (BinaryRational.subtract q r).1.negative
  let regs := initialRegisters [Value.flag q.negative, .pointer ap, .pointer dp,
    .flag r.negative, .pointer bp, .pointer ep]
  let ready := bindResults regs [6, 7, 8] [Value.flag sign, .pointer np, .pointer denp]
  have last : Within code out ready (.ret [.register 6, .register 7, .register 8])
      [.flag sign, .pointer np, .pointer denp] out 7 := by
    simpa [ready, bindResults, values, Atom.eval] using
      Within.ret code out ready [.register 6, .register 7, .register 8]
  have hargs : values regs [.register 0, .register 1, .register 2,
      .flag (!r.negative), .register 4, .register 5] =
      [.flag q.negative, .pointer ap, .pointer dp, .flag (!r.negative), .pointer bp, .pointer ep] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have hcall := Within.call (procedure := rationalAdd)
    (arguments := [.register 0, .register 1, .register 2, .flag (!r.negative), .register 4, .register 5])
    (results := [6, 7, 8]) (regs := regs) (returned := [.flag sign, .pointer np, .pointer denp])
    (by simpa only [hargs, BinaryRational.negate, BinaryRational.subtract, sign] using he) last
  have hcall' := hcall.mono (show _ ≤ 3000 * (n + 1) ^ 3 + 20 by
    simp only [List.length_cons, List.length_nil]; omega)
  have hbranch := Within.branch (b := r.negative) (test := .register 3) (regs := regs)
    (budget := 3000 * (n + 1) ^ 3 + 20)
    (yes := subtractCase rationalAdd false) (no := subtractCase rationalAdd true)
    (by simp [Atom.eval, regs, initialRegisters])
    (by cases hsign : r.negative <;> simpa [hsign, subtractCase] using hcall')
  exact hbranch.mono (by
    have hp : 0 < (n + 1) ^ 3 := by positivity
    omega)

theorem subtract_correct (code : Code p) (d : RegisterRationalProducts.Procedures p)
    (hm : d.Matches code) (signedAdd rationalAdd : Fin p)
    (hsa : code signedAdd = RegisterSignedAdd.signedAddBody d.division.add d.division.cmp d.division.sub)
    (hadd : code rationalAdd = addBody d.multiply signedAdd d.normalize)
    {n : ℕ} {h : Heap} (hh : Valid h) (q r : BinaryRational.Word n)
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
        (subtractBody rationalAdd) [.flag z.negative, .pointer np, .pointer denp]
        out (3100 * (n + 1) ^ 3) := by
  obtain ⟨out, np, denp, hx, hv, hn, hdn, he⟩ :=
    subtract_compiled code d hm signedAdd rationalAdd hsa hadd hh q r ha hd hb he
  exact ⟨out, np, denp, (BinaryRational.subtract q r).1, hx, hv,
    BinaryRational.add_canonical q (BinaryRational.negate r) hq hr hden,
    BinaryRational.subtract_value q r hq hr hnum hden, hn, hdn, he⟩

end WeightedMIS.RegisterRationalAdd
