module

public import WeightedMIS.StoredRational
public import WeightedMIS.RegisterRationalAdd

/-!
# Closed arithmetic on stored rational records

The fixed wrapper reads two rational records, calls the verified binary
arithmetic body, and stores its normalized result while sharing its words.
-/

@[expose] public section

namespace WeightedMIS.RegisterStoredRational

open PointerMemory RegisterMachine EfficientSearch StoredRational

variable {p n : ℕ}

def binaryBody (read op store : Fin p) : Command p :=
  .call read [.register 0] [2,3,4]
    (.call read [.register 1] [5,6,7]
      (.call op [.register 2,.register 3,.register 4,.register 5,.register 6,.register 7] [8,9,10]
        (.call store [.register 8,.register 9,.register 10] [11] (.ret [.register 11]))))

def RawRefines (code : Code p) (raw : Fin p)
    (f : BinaryRational.Word n → BinaryRational.Word n → BinaryRational.Word n) (budget : ℕ) : Prop :=
  ∀ {h : Heap}, Valid h → ∀ (q r : BinaryRational.Word n) {ap dp bp ep : Ptr},
    BitsAt h ap q.magnitude → BitsAt h dp q.denominator →
    BitsAt h bp r.magnitude → BitsAt h ep r.denominator →
    ∃ out : Heap, ∃ np denp : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out np (f q r).magnitude ∧ BitsAt out denp (f q r).denominator ∧
      Within code h (initialRegisters [.flag q.negative,.pointer ap,.pointer dp,
        .flag r.negative,.pointer bp,.pointer ep]) (code raw)
        [.flag (f q r).negative,.pointer np,.pointer denp] out budget

theorem binary_compiled (code : Code p) (read raw store : Fin p)
    (hread : code read = StoredRational.readBody) (hstore : code store = StoredRational.storeBody)
    (f : BinaryRational.Word n → BinaryRational.Word n → BinaryRational.Word n)
    (budget : ℕ) (rawCompiled : RawRefines code raw f budget)
    {h : Heap} (hh : Valid h) {qp rp : Ptr} {q r : BinaryRational.Word n}
    (hq : At h qp q) (hr : At h rp r) :
    ∃ out result, Extends h out ∧ Valid out ∧ At out result (f q r) ∧
      Within code h (initialRegisters [.pointer qp,.pointer rp]) (binaryBody read raw store)
        [.pointer result] out (budget + 110) := by
  obtain ⟨ap,dp,ha,hd,readQ⟩ := StoredRational.read_compiled code hq
  obtain ⟨bp,ep,hb,he,readR⟩ := StoredRational.read_compiled code hr
  obtain ⟨mid,np,denp,ext,valid,hn,hden,operated⟩ := rawCompiled hh q r ha hd hb he
  obtain ⟨out,result,extOut,validOut,hresult,stored⟩ := StoredRational.store_compiled code valid (f q r) hn hden
  let r0 := initialRegisters [Value.pointer qp,.pointer rp]
  let r1 := bindResults r0 [2,3,4] [.flag q.negative,.pointer ap,.pointer dp]
  let r2 := bindResults r1 [5,6,7] [.flag r.negative,.pointer bp,.pointer ep]
  let r3 := bindResults r2 [8,9,10] [.flag (f q r).negative,.pointer np,.pointer denp]
  let r4 := bindResults r3 [11] [Value.pointer result]
  have last : Within code out r4 (.ret [.register 11]) [.pointer result] out 3 := by
    simpa [r4,bindResults,values,Atom.eval] using Within.ret code out r4 [.register 11]
  have storeArgs : values r3 [.register 8,.register 9,.register 10] =
      [.flag (f q r).negative,.pointer np,.pointer denp] := by
    simp [r3,bindResults,values,Atom.eval]
  have storeCall := Within.call (procedure := store) (arguments := [.register 8,.register 9,.register 10])
    (results := [11]) (regs := r3) (by simpa only [storeArgs,hstore] using stored) last
  have opArgs : values r2 [.register 2,.register 3,.register 4,.register 5,.register 6,.register 7] =
      [.flag q.negative,.pointer ap,.pointer dp,.flag r.negative,.pointer bp,.pointer ep] := by
    simp [r2,r1,bindResults,values,Atom.eval]
  have opCall := Within.call (procedure := raw)
    (arguments := [.register 2,.register 3,.register 4,.register 5,.register 6,.register 7])
    (results := [8,9,10]) (regs := r2) (by simpa only [opArgs] using operated) storeCall
  have rArgs : values r1 [.register 1] = [.pointer rp] := by
    simp [r1,r0,bindResults,initialRegisters,values,Atom.eval]
  have rCall := Within.call (procedure := read) (arguments := [.register 1]) (results := [5,6,7])
    (regs := r1) (by simpa only [rArgs,hread] using readR) opCall
  have qArgs : values r0 [.register 0] = [.pointer qp] := by
    simp [r0,initialRegisters,values,Atom.eval]
  have qCall := Within.call (procedure := read) (arguments := [.register 0]) (results := [2,3,4])
    (regs := r0) (by simpa only [qArgs,hread] using readQ) rCall
  refine ⟨out,result,ext.trans extOut,validOut,hresult,?_⟩
  exact qCall.mono (by simp only [List.length_cons,List.length_nil]; omega)

def scalarBudget (width : ℕ) : ℕ := 3300 * (width + 1) ^ 3

theorem multiply_compiled (code : Code p) (read raw store : Fin p)
    (d : RegisterRationalProducts.Procedures p) (hm : d.Matches code)
    (hread : code read = StoredRational.readBody) (hstore : code store = StoredRational.storeBody)
    (hraw : code raw = RegisterRationalProducts.multiplyBody d.multiply d.normalize)
    {h : Heap} (hh : Valid h) {qp rp : Ptr} {q r : BinaryRational.Word n}
    (hq : At h qp q) (hr : At h rp r) :
    ∃ out result, Extends h out ∧ Valid out ∧ At out result (BinaryRational.multiply q r).1 ∧
      Within code h (initialRegisters [.pointer qp,.pointer rp]) (binaryBody read raw store)
        [.pointer result] out (scalarBudget n) := by
  have rawCompiled : RawRefines code raw (fun (q r : BinaryRational.Word n) => (BinaryRational.multiply q r).1) (3000*(n+1)^3) := by
    intro heap valid q r ap dp bp ep ha hd hb he
    simpa only [hraw] using RegisterRationalProducts.multiply_compiled code d hm valid q r ha hd hb he
  obtain ⟨out,result,he,ho,ht,exec⟩ := binary_compiled code read raw store hread hstore
    (fun (q r : BinaryRational.Word n) => (BinaryRational.multiply q r).1) _ rawCompiled hh hq hr
  exact ⟨out,result,he,ho,ht,exec.mono (by
    have hpos : 0 < (n+1)^3 := by positivity
    unfold scalarBudget; omega)⟩

theorem add_compiled (code : Code p) (read raw store signedAdd : Fin p)
    (d : RegisterRationalProducts.Procedures p) (hm : d.Matches code)
    (hread : code read = StoredRational.readBody) (hstore : code store = StoredRational.storeBody)
    (hsa : code signedAdd = RegisterSignedAdd.signedAddBody d.division.add d.division.cmp d.division.sub)
    (hraw : code raw = RegisterRationalAdd.addBody d.multiply signedAdd d.normalize)
    {h : Heap} (hh : Valid h) {qp rp : Ptr} {q r : BinaryRational.Word n}
    (hq : At h qp q) (hr : At h rp r) :
    ∃ out result, Extends h out ∧ Valid out ∧ At out result (BinaryRational.add q r).1 ∧
      Within code h (initialRegisters [.pointer qp,.pointer rp]) (binaryBody read raw store)
        [.pointer result] out (scalarBudget n) := by
  have rawCompiled : RawRefines code raw (fun (q r : BinaryRational.Word n) => (BinaryRational.add q r).1) (3000*(n+1)^3) := by
    intro heap valid q r ap dp bp ep ha hd hb he
    simpa only [hraw] using RegisterRationalAdd.add_compiled code d hm signedAdd hsa valid q r ha hd hb he
  obtain ⟨out,result,he,ho,ht,exec⟩ := binary_compiled code read raw store hread hstore
    (fun (q r : BinaryRational.Word n) => (BinaryRational.add q r).1) _ rawCompiled hh hq hr
  exact ⟨out,result,he,ho,ht,exec.mono (by
    have hpos : 0 < (n+1)^3 := by positivity
    unfold scalarBudget; omega)⟩

theorem divide_compiled (code : Code p) (read raw store rationalMultiply : Fin p)
    (d : RegisterRationalProducts.Procedures p) (hm : d.Matches code)
    (hread : code read = StoredRational.readBody) (hstore : code store = StoredRational.storeBody)
    (hprod : code rationalMultiply = RegisterRationalProducts.multiplyBody d.multiply d.normalize)
    (hraw : code raw = RegisterRationalProducts.divideBody rationalMultiply)
    {h : Heap} (hh : Valid h) {qp rp : Ptr} {q r : BinaryRational.Word n}
    (hq : At h qp q) (hr : At h rp r) :
    ∃ out result, Extends h out ∧ Valid out ∧ At out result (BinaryRational.divide q r).1 ∧
      Within code h (initialRegisters [.pointer qp,.pointer rp]) (binaryBody read raw store)
        [.pointer result] out (scalarBudget n) := by
  have rawCompiled : RawRefines code raw (fun (q r : BinaryRational.Word n) => (BinaryRational.divide q r).1) (3100*(n+1)^3) := by
    intro heap valid q r ap dp bp ep ha hd hb he
    simpa only [hraw] using RegisterRationalProducts.divide_compiled code d hm rationalMultiply hprod valid q r ha hd hb he
  obtain ⟨out,result,he,ho,ht,exec⟩ := binary_compiled code read raw store hread hstore
    (fun (q r : BinaryRational.Word n) => (BinaryRational.divide q r).1) _ rawCompiled hh hq hr
  exact ⟨out,result,he,ho,ht,exec.mono (by
    have hpos : 0 < (n+1)^3 := by positivity
    unfold scalarBudget; omega)⟩

theorem subtract_compiled (code : Code p) (read raw store signedAdd rationalAdd : Fin p)
    (d : RegisterRationalProducts.Procedures p) (hm : d.Matches code)
    (hread : code read = StoredRational.readBody) (hstore : code store = StoredRational.storeBody)
    (hsa : code signedAdd = RegisterSignedAdd.signedAddBody d.division.add d.division.cmp d.division.sub)
    (hadd : code rationalAdd = RegisterRationalAdd.addBody d.multiply signedAdd d.normalize)
    (hraw : code raw = RegisterRationalAdd.subtractBody rationalAdd)
    {h : Heap} (hh : Valid h) {qp rp : Ptr} {q r : BinaryRational.Word n}
    (hq : At h qp q) (hr : At h rp r) :
    ∃ out result, Extends h out ∧ Valid out ∧ At out result (BinaryRational.subtract q r).1 ∧
      Within code h (initialRegisters [.pointer qp,.pointer rp]) (binaryBody read raw store)
        [.pointer result] out (scalarBudget n) := by
  have rawCompiled : RawRefines code raw (fun (q r : BinaryRational.Word n) => (BinaryRational.subtract q r).1) (3100*(n+1)^3) := by
    intro heap valid q r ap dp bp ep ha hd hb he
    simpa only [hraw] using RegisterRationalAdd.subtract_compiled code d hm signedAdd rationalAdd hsa hadd valid q r ha hd hb he
  obtain ⟨out,result,he,ho,ht,exec⟩ := binary_compiled code read raw store hread hstore
    (fun (q r : BinaryRational.Word n) => (BinaryRational.subtract q r).1) _ rawCompiled hh hq hr
  exact ⟨out,result,he,ho,ht,exec.mono (by
    have hpos : 0 < (n+1)^3 := by positivity
    unfold scalarBudget; omega)⟩

end WeightedMIS.RegisterStoredRational
