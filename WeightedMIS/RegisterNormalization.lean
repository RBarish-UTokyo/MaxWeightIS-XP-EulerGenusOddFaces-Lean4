module

public import WeightedMIS.RegisterGCD
public import WeightedMIS.BinaryRationalInterface

/-!
# Closed binary rational normalization

A sign bit, numerator-magnitude pointer, and denominator pointer are normalized
by a fixed sequence of one compiled gcd call and two compiled division calls.
The returned arrays are exactly those of the verified binary rational normalizer.
-/

@[expose] public section

namespace WeightedMIS.RegisterNormalization

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def normalizeBody (gcd divide : Fin p) : Command p :=
  .call gcd [.register 1, .register 2] [3]
    (.call divide [.register 1, .register 3] [4, 5]
      (.call divide [.register 2, .register 3] [6, 7]
        (.ret [.register 0, .register 4, .register 6])))

/-- The compiled normalizer performs cubic register work on represented words,
including all gcd iterations, quotient computations, and register transfers. -/
theorem compiled (code : Code p) (d : RegisterDivision.Procedures p)
    (hm : d.Matches code) (gcd remProc : Fin p)
    (hgcd : code gcd = RegisterGCD.gcdBody gcd remProc d.zero d.cmp)
    (hrem : code remProc = RegisterDivision.remainderBody d.divide)
    {n : ℕ} {h : Heap} (hh : Valid h) (q : BinaryRational.Word n) {ap dp : Ptr}
    (ha : BitsAt h ap q.magnitude) (hd : BitsAt h dp q.denominator) :
    ∃ out : Heap, ∃ np denp : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out np (BinaryRational.normalize q).1.magnitude ∧
      BitsAt out denp (BinaryRational.normalize q).1.denominator ∧
      Within code h (initialRegisters [.flag q.negative, .pointer ap, .pointer dp])
        (normalizeBody gcd d.divide) [.flag q.negative, .pointer np, .pointer denp]
        out (2100 * (n + 1) ^ 3) := by
  obtain ⟨gh, gp, hgext, hgvalid, hgrep, hge⟩ :=
    RegisterGCD.euclid_compiled code d hm gcd remProc hgcd hrem hh ha hd
      (Bits.value_lt q.denominator)
  change BitsAt gh gp (Bits.gcd q.magnitude q.denominator).1 at hgrep
  have hag := ha.mono hgext
  have hdg := hd.mono hgext
  rcases hm with ⟨hz, hc, hx, hs, hsn, hsu, hco, had, hdv⟩
  obtain ⟨ah, np, nrp, haext, havalid, harep, hanrem, hae⟩ :=
    RegisterDivision.divide_compiled code d.zero d.cmp d.aux d.shift d.snoc d.sub d.complement d.add
      hz hc hx hs hsn hsu hco had hgvalid hag hgrep
  rw [← hdv] at hae
  have hda := hdg.mono haext
  have hga := hgrep.mono haext
  obtain ⟨out, denp, drp, hdext, hdvalid, hdrep, hdrem, hde⟩ :=
    RegisterDivision.divide_compiled code d.zero d.cmp d.aux d.shift d.snoc d.sub d.complement d.add
      hz hc hx hs hsn hsu hco had havalid hda hga
  rw [← hdv] at hde
  refine ⟨out, np, denp, hgext.trans (haext.trans hdext), hdvalid,
    harep.mono hdext, hdrep, ?_⟩
  let regs := initialRegisters [Value.flag q.negative, .pointer ap, .pointer dp]
  let gcdDone := bindResults regs [3] [Value.pointer gp]
  let numDone := bindResults gcdDone [4, 5] [Value.pointer np, .pointer nrp]
  let denDone := bindResults numDone [6, 7] [Value.pointer denp, .pointer drp]
  have last : Within code out denDone (.ret [.register 0, .register 4, .register 6])
      [.flag q.negative, .pointer np, .pointer denp] out 7 := by
    simpa [denDone, numDone, gcdDone, regs, bindResults, initialRegisters, values, Atom.eval] using
      Within.ret code out denDone [.register 0, .register 4, .register 6]
  have hargsD : values numDone [.register 2, .register 3] = [.pointer dp, .pointer gp] := by
    simp [numDone, gcdDone, regs, bindResults, initialRegisters, values, Atom.eval]
  have hcallD := Within.call (procedure := d.divide) (arguments := [.register 2, .register 3])
    (results := [6, 7]) (regs := numDone) (returned := [.pointer denp, .pointer drp])
    (by simpa only [hargsD] using hde) last
  have hargsA : values gcdDone [.register 1, .register 3] = [.pointer ap, .pointer gp] := by
    simp [gcdDone, regs, bindResults, initialRegisters, values, Atom.eval]
  have hcallA := Within.call (procedure := d.divide) (arguments := [.register 1, .register 3])
    (results := [4, 5]) (regs := gcdDone) (returned := [.pointer np, .pointer nrp])
    (by simpa only [hargsA] using hae) hcallD
  have hargsG : values regs [.register 1, .register 2] = [.pointer ap, .pointer dp] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have hcallG := Within.call (procedure := gcd) (arguments := [.register 1, .register 2])
    (results := [3]) (regs := regs) (returned := [.pointer gp])
    (by simpa only [hargsG] using hge) hcallA
  exact hcallG.mono (by simp only [List.length_cons, List.length_nil]; nlinarith)

/-- The actual arrays returned by the closed code denote the input rational
and have exactly its canonical reduced numerator magnitude and denominator. -/
theorem correct (code : Code p) (d : RegisterDivision.Procedures p)
    (hm : d.Matches code) (gcd remProc : Fin p)
    (hgcd : code gcd = RegisterGCD.gcdBody gcd remProc d.zero d.cmp)
    (hrem : code remProc = RegisterDivision.remainderBody d.divide)
    {n : ℕ} {h : Heap} (hh : Valid h) (q : BinaryRational.Word n) {ap dp : Ptr}
    (ha : BitsAt h ap q.magnitude) (hd : BitsAt h dp q.denominator)
    (hpos : 0 < q.denominator.value) :
    ∃ out : Heap, ∃ np denp : Ptr, ∃ r : BinaryRational.Word n,
      Extends h out ∧ Valid out ∧ BinaryRational.Canonical r ∧ r.value = q.value ∧
      BitsAt out np r.magnitude ∧ BitsAt out denp r.denominator ∧
      Within code h (initialRegisters [.flag q.negative, .pointer ap, .pointer dp])
        (normalizeBody gcd d.divide) [.flag r.negative, .pointer np, .pointer denp]
        out (2100 * (n + 1) ^ 3) := by
  obtain ⟨out, np, denp, hx, hv, hn, hd, he⟩ := compiled code d hm gcd remProc hgcd hrem hh q ha hd
  exact ⟨out, np, denp, (BinaryRational.normalize q).1, hx, hv,
    BinaryRational.normalize_canonical q hpos, BinaryRational.normalize_value q hpos, hn, hd, he⟩

end WeightedMIS.RegisterNormalization
