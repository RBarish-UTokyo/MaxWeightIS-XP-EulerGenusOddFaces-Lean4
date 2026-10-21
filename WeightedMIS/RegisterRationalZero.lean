module

public import WeightedMIS.RegisterStoredRational

/-! # Closed zero test on a stored rational record -/

@[expose] public section

namespace WeightedMIS.RegisterRationalZero

open PointerMemory RegisterMachine EfficientSearch StoredRational

variable {p n : ℕ}

def body (read zero compare : Fin p) : Command p :=
  .call read [.register 0] [1,2,3]
    (.call zero [.register 2] [4]
      (.call compare [.register 2,.register 4] [5,6] (.ret [.register 6])))

theorem compiled (code : Code p) (read zero compare : Fin p)
    (hread : code read = StoredRational.readBody)
    (hzero : code zero = RegisterZero.zeroBody zero)
    (hcompare : code compare = RegisterComparator.comparatorBody compare)
    {h : Heap} (hh : Valid h) {qp : Ptr} {q : BinaryRational.Word n} (hq : At h qp q) :
    ∃ out, Extends h out ∧ Valid out ∧
      Within code h (initialRegisters [.pointer qp]) (body read zero compare)
        [.flag (BinaryRational.isZero q).1] out (60*n+80) := by
  obtain ⟨np,dp,hn,hd,readQ⟩ := StoredRational.read_compiled code hq
  obtain ⟨out,zp,ext,valid,hz,_hlen,zeroed⟩ := RegisterZero.compiled code zero hzero hh hn
  have compared := RegisterComparator.compiled code compare hcompare (hn.mono ext) hz
  let flags := RegisterComparator.flags (Bits.compare q.magnitude (Bits.zero n)).1
  let r0 := initialRegisters [Value.pointer qp]
  let r1 := bindResults r0 [1,2,3] [.flag q.negative,.pointer np,.pointer dp]
  let r2 := bindResults r1 [4] [Value.pointer zp]
  let r3 := bindResults r2 [5,6] flags
  have last : Within code out r3 (.ret [.register 6]) [.flag (BinaryRational.isZero q).1] out 3 := by
    simpa [r3,flags,RegisterComparator.flags,BinaryRational.isZero,bindResults,values,Atom.eval] using
      Within.ret code out r3 [.register 6]
  have cmpArgs : values r2 [.register 2,.register 4] = [.pointer np,.pointer zp] := by
    simp [r2,r1,bindResults,values,Atom.eval]
  have cmpCall := Within.call (procedure := compare) (arguments := [.register 2,.register 4])
    (results := [5,6]) (regs := r2) (by simpa only [cmpArgs] using compared) last
  have zeroArgs : values r1 [.register 2] = [.pointer np] := by
    simp [r1,bindResults,values,Atom.eval]
  have zeroCall := Within.call (procedure := zero) (arguments := [.register 2]) (results := [4])
    (regs := r1) (by simpa only [zeroArgs] using zeroed) cmpCall
  have readArgs : values r0 [.register 0] = [.pointer qp] := by
    simp [r0,initialRegisters,values,Atom.eval]
  have readCall := Within.call (procedure := read) (arguments := [.register 0]) (results := [1,2,3])
    (regs := r0) (by simpa only [readArgs,hread] using readQ) zeroCall
  refine ⟨out,ext,valid,readCall.mono ?_⟩
  simp only [List.length_cons,List.length_nil]
  omega

theorem correct (code : Code p) (read zero compare : Fin p)
    (hread : code read = StoredRational.readBody)
    (hzero : code zero = RegisterZero.zeroBody zero)
    (hcompare : code compare = RegisterComparator.comparatorBody compare)
    {h : Heap} (hh : Valid h) {qp : Ptr} {q : BinaryRational.Word n} (hq : At h qp q)
    (hden : 0 < q.denominator.value) :
    ∃ out, Extends h out ∧ Valid out ∧
      Within code h (initialRegisters [.pointer qp]) (body read zero compare)
        [.flag (decide (q.value = 0))] out (60*n+80) := by
  have he : (BinaryRational.isZero q).1 = decide (q.value = 0) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using BinaryRational.isZero_correct q hden
  simpa only [he] using compiled code read zero compare hread hzero hcompare hh hq

end WeightedMIS.RegisterRationalZero
