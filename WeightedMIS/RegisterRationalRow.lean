module

public import WeightedMIS.RegisterStoredRational
public import WeightedMIS.EfficientSearchPointerTrie
public import WeightedMIS.CompiledTrie

/-!
# Fixed register code for rational row dot products

Rows are linked lists of shared rational records. The procedure follows both
lists, multiplies their entries with compiled binary arithmetic, and adds the
result to the recursively computed suffix. The recursion is on actual list
cells; its length does not appear in the program.
-/

@[expose] public section

namespace WeightedMIS.RegisterRationalRow

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational

variable {p n : ℕ}

def RowAt (h : Heap) (rp : Ptr) (row : List (BinaryRational.Word n)) : Prop :=
  ListRep (fun heap ptr (q : BinaryRational.Word n) => At heap ptr q) h rp row

theorem RowAt.mono {h out : Heap} (ext : Extends h out) {rp : Ptr}
    {row : List (BinaryRational.Word n)} (hr : RowAt h rp row) : RowAt out rp row :=
  ListRep.mono ext (fun _ _ hq => At.mono ext hq) hr

def dotWords (zero : BinaryRational.Word n) :
    List (BinaryRational.Word n) → List (BinaryRational.Word n) → BinaryRational.Word n
  | q :: qs, r :: rs => (BinaryRational.add (BinaryRational.multiply q r).1 (dotWords zero qs rs)).1
  | _, _ => zero

def stepBody (self multiply add : Fin p) : Command p :=
  .call self [.register 4,.register 6,.register 2] [7]
    (.call multiply [.register 3,.register 5] [8]
      (.call add [.register 8,.register 7] [9] (.ret [.register 9])))

def body (self multiply add : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.register 2]
    cons := .load (.register 1) 5 6 15 { CompiledTrie.failCases with
      nil := .ret [.register 2]
      cons := stepBody self multiply add } }

structure Procedures (p : ℕ) where
  self : Fin p
  multiply : Fin p
  add : Fin p
  read : Fin p
  store : Fin p
  rawMultiply : Fin p
  rawAdd : Fin p
  signedAdd : Fin p

structure Procedures.Matches (ids : Procedures p) (code : Code p)
    (d : RegisterRationalProducts.Procedures p) : Prop where
  arithmetic : d.Matches code
  self : code ids.self = body ids.self ids.multiply ids.add
  read : code ids.read = StoredRational.readBody
  store : code ids.store = StoredRational.storeBody
  multiply : code ids.multiply = RegisterStoredRational.binaryBody ids.read ids.rawMultiply ids.store
  add : code ids.add = RegisterStoredRational.binaryBody ids.read ids.rawAdd ids.store
  rawMultiply : code ids.rawMultiply = RegisterRationalProducts.multiplyBody d.multiply d.normalize
  rawAdd : code ids.rawAdd = RegisterRationalAdd.addBody d.multiply ids.signedAdd d.normalize
  signedAdd : code ids.signedAdd = RegisterSignedAdd.signedAddBody d.division.add d.division.cmp d.division.sub

def budget (width length : ℕ) : ℕ :=
  (2 * RegisterStoredRational.scalarBudget width + 50) * length + 23

theorem compiled (code : Code p) (ids : Procedures p) (d : RegisterRationalProducts.Procedures p)
    (hcode : ids.Matches code d) {h : Heap} (hh : Valid h) {qp rp zp : Ptr}
    {qs rs : List (BinaryRational.Word n)} {zero : BinaryRational.Word n}
    (hq : RowAt h qp qs) (hr : RowAt h rp rs) (hz : At h zp zero) :
    ∃ out result, Extends h out ∧ Valid out ∧ At out result (dotWords zero qs rs) ∧
      Within code h (initialRegisters [.pointer qp,.pointer rp,.pointer zp]) (code ids.self)
        [.pointer result] out (budget n qs.length) := by
  obtain ⟨qps,hql,hqr⟩ := hq
  induction hql generalizing qs rp rs with
  | @nil qp cell =>
    cases hqr
    refine ⟨h,zp,.refl h,hh,hz,?_⟩
    let regs := initialRegisters [Value.pointer qp,.pointer rp,.pointer zp]
    let loaded := loadRegisters regs 3 4 15 .nil
    have last : Within code h loaded (.ret [.register 2]) [.pointer zp] h 3 := by
      simpa [values,Atom.eval,loaded,loadRegisters,decoded,regs,initialRegisters] using
        Within.ret code h loaded [.register 2]
    rw [hcode.self]
    apply Within.mono (b := budget n 0) (a := 13) ?_ (by simp [budget])
    exact Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := .ret [.register 2],
        cons := .load (.register 1) 5 6 15 {CompiledTrie.failCases with
          nil := .ret [.register 2], cons := stepBody ids.self ids.multiply ids.add}})
      (by simp [Atom.eval,regs,initialRegisters]) cell last
  | @cons qp ap qt qps cell tail ih =>
    cases hqr with
    | @cons _ q _ qs hq hqs =>
      obtain ⟨rps,hrl,hrr⟩ := hr
      cases hrl with
      | nil rcell =>
        cases hrr
        refine ⟨h,zp,.refl h,hh,hz,?_⟩
        let regs := initialRegisters [Value.pointer qp,.pointer rp,.pointer zp]
        let lq := loadRegisters regs 3 4 15 (.cons ap qt)
        let lr := loadRegisters lq 5 6 15 .nil
        have last : Within code h lr (.ret [.register 2]) [.pointer zp] h 3 := by
          simpa [values,Atom.eval,lr,lq,loadRegisters,decoded,regs,initialRegisters] using
            Within.ret code h lr [.register 2]
        have right := Within.load (address := .register 1) (first := 5) (second := 6) (bit := 15)
          (branches := {CompiledTrie.failCases with
            nil := .ret [.register 2],
            cons := stepBody ids.self ids.multiply ids.add})
          (by simp [Atom.eval,lq,loadRegisters,decoded,regs,initialRegisters]) rcell last
        have left := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
          (branches := {CompiledTrie.failCases with
            nil := .ret [.register 2],
            cons := .load (.register 1) 5 6 15 {CompiledTrie.failCases with
              nil := .ret [.register 2], cons := stepBody ids.self ids.multiply ids.add}})
          (by simp [Atom.eval,regs,initialRegisters]) cell right
        rw [hcode.self]
        exact left.mono (by simp [budget])
      | @cons rp bp rt rps rcell rtail =>
        cases hrr with
        | @cons _ r _ rs hr hrs =>
          obtain ⟨mid,suffix,e1,v1,hsuffix,recurse⟩ := ih ⟨rps,rtail,hrs⟩ hqs
          obtain ⟨mid2,product,e2,v2,hproduct,multiplied⟩ := RegisterStoredRational.multiply_compiled
            code ids.read ids.rawMultiply ids.store d hcode.arithmetic hcode.read hcode.store
              hcode.rawMultiply v1 (hq.mono e1) (hr.mono e1)
          obtain ⟨out,result,e3,vo,hresult,added⟩ := RegisterStoredRational.add_compiled code
            ids.read ids.rawAdd ids.store ids.signedAdd d hcode.arithmetic hcode.read hcode.store
              hcode.signedAdd hcode.rawAdd v2 hproduct (hsuffix.mono e2)
          refine ⟨out,result,e1.trans (e2.trans e3),vo,hresult,?_⟩
          let r0 := initialRegisters [Value.pointer qp,.pointer rp,.pointer zp]
          let r1 := loadRegisters r0 3 4 15 (.cons ap qt)
          let r2 := loadRegisters r1 5 6 15 (.cons bp rt)
          let r3 := bindResults r2 [7] [Value.pointer suffix]
          let r4 := bindResults r3 [8] [Value.pointer product]
          let r5 := bindResults r4 [9] [Value.pointer result]
          have last : Within code out r5 (.ret [.register 9]) [.pointer result] out 3 := by
            simpa [r5,bindResults,values,Atom.eval] using Within.ret code out r5 [.register 9]
          have addArgs : values r4 [.register 8,.register 7] = [.pointer product,.pointer suffix] := by
            simp [r4,r3,bindResults,values,Atom.eval]
          have addCall := Within.call (procedure := ids.add) (arguments := [.register 8,.register 7])
            (results := [9]) (regs := r4) (by simpa only [addArgs,hcode.add] using added) last
          have mulArgs : values r3 [.register 3,.register 5] = [.pointer ap,.pointer bp] := by
            simp [r3,r2,r1,bindResults,loadRegisters,decoded,values,Atom.eval]
          have mulCall := Within.call (procedure := ids.multiply) (arguments := [.register 3,.register 5])
            (results := [8]) (regs := r3) (by simpa only [mulArgs,hcode.multiply] using multiplied) addCall
          have recArgs : values r2 [.register 4,.register 6,.register 2] = [.pointer qt,.pointer rt,.pointer zp] := by
            simp [r2,r1,r0,loadRegisters,decoded,initialRegisters,values,Atom.eval]
          have recCall := Within.call (procedure := ids.self) (arguments := [.register 4,.register 6,.register 2])
            (results := [7]) (regs := r2) (by simpa only [recArgs] using recurse) mulCall
          have right := Within.load (address := .register 1) (first := 5) (second := 6) (bit := 15)
            (branches := {CompiledTrie.failCases with
              nil := .ret [.register 2],
              cons := stepBody ids.self ids.multiply ids.add})
            (by simp [Atom.eval,r1,r0,loadRegisters,decoded,initialRegisters]) rcell recCall
          have left := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
            (branches := {CompiledTrie.failCases with
              nil := .ret [.register 2],
              cons := .load (.register 1) 5 6 15 {CompiledTrie.failCases with
                nil := .ret [.register 2], cons := stepBody ids.self ids.multiply ids.add}})
            (by simp [Atom.eval,r0,initialRegisters]) cell right
          rw [hcode.self]
          exact left.mono (by simp only [budget,List.length_cons,List.length_nil,Nat.mul_add]; omega)

end WeightedMIS.RegisterRationalRow
