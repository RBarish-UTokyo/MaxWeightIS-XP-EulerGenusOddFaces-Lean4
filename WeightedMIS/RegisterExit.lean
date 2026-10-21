module

public import WeightedMIS.RegisterCandidateFinish
public import WeightedMIS.RegisterPairReads

/-! # Finite generation of the possible working-node exit arc -/

@[expose] public section

namespace WeightedMIS.RegisterExit

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.EfficientSearch.Pointer WeightedMIS.RegisterPairReads

variable {p n cbits : ℕ}

def reads : List Fields := [(5,8,9),(9,10,9),(9,11,9),(9,12,9),(9,13,14)]

def emitExit (encode emit : Fin p) : Command p :=
  .call encode [.flag true,.register 1,.register 2,.register 3,.register 4,
      .register 10,.register 11,.register 12,.register 13] [14]
    (.call emit [.register 0,.register 14,.register 6,.register 7] [15] (.ret [.register 15]))

/-- Arguments: source, anchor, current, box, parity, arithmetic, cost/label, tail. -/
def body (compare encode emit : Fin p) : Command p :=
  readPairs reads (.call compare [.register 2,.register 1] [14,15]
    (.branch (.register 15) (emitExit encode emit) (.ret [.register 7])))

def arcs (a : ArithmeticWords n) (source anchor current box parity : Bits n)
    (weight : Bits cbits) (label : Ptr) : List (RawArc Ptr n cbits) :=
  if (Bits.compare current anchor).1 = .eq then
    [(source,⟨ScalarNodeCodec.encodeWords a.states a.block a.one a.two
      ⟨true,anchor,current,box,parity⟩,weight,label⟩)]
  else []

theorem compiled (code : Code p) (compare encode emit : Fin p) (arith : RegisterHorner.Procedures p)
    (harith : arith.Matches code) (hcompare : code compare = RegisterComparator.comparatorBody compare)
    (hencode : code encode = RegisterNodeEncode.encodeBody arith.mul arith.add)
    (hemit : code emit = RegisterArcEmitter.emitBody)
    {h : Heap} (hh : Valid h) {a : ArithmeticWords n} {source anchor current box parity : Bits n}
    {weight : Bits cbits} {label sp ap cp bp pp arp cost acc : Ptr} {tail : List (RawArc Ptr n cbits)}
    (hs : BitsAt h sp source) (ha : BitsAt h ap anchor) (hc : BitsAt h cp current)
    (hb : BitsAt h bp box) (hp : BitsAt h pp parity) (har : ArithmeticAt h arp a)
    (hcost : CostLabelAt h cost weight label) (htail : TraceAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (arcs a source anchor current box parity weight label ++ tail) ∧
      Within code h (initialRegisters [.pointer sp,.pointer ap,.pointer cp,.pointer bp,.pointer pp,
        .pointer arp,.pointer cost,.pointer acc]) (body compare encode emit) [.pointer q] out
          (1200*(n+1)^2 + 36*n + 150) := by
  obtain ⟨base,t1,states,t2,block,t3,one,t4,two,zero,h0,h1,h2,h3,h4,hbase,hstates,hblock,hone,htwo,hzero⟩ := har
  let r0 := initialRegisters [Value.pointer sp,.pointer ap,.pointer cp,.pointer bp,.pointer pp,
    .pointer arp,.pointer cost,.pointer acc]
  let r1 := loadRegisters r0 8 9 15 (.pair base t1)
  let r2 := loadRegisters r1 10 9 15 (.pair states t2)
  let r3 := loadRegisters r2 11 9 15 (.pair block t3)
  let r4 := loadRegisters r3 12 9 15 (.pair one t4)
  let r5 := loadRegisters r4 13 14 15 (.pair two zero)
  have parsed : Reads h r0 reads r5 := by
    refine Reads.cons (ptr := arp) (by simp [r0,initialRegisters]) h0 ?_
    refine Reads.cons (ptr := t1) (by simp [r1,loadRegisters,decoded]) h1 ?_
    refine Reads.cons (ptr := t2) (by simp [r2,loadRegisters,decoded]) h2 ?_
    refine Reads.cons (ptr := t3) (by simp [r3,loadRegisters,decoded]) h3 ?_
    refine Reads.cons (ptr := t4) (by simp [r4,loadRegisters,decoded]) h4 ?_
    exact Reads.nil r5
  have cmp := RegisterComparator.compiled code compare hcompare hc ha
  let order := (Bits.compare current anchor).1
  let r6 := bindResults r5 [14,15] (RegisterComparator.flags order)
  obtain ⟨out,q,he,ho,hq,branch⟩ :
      ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (arcs a source anchor current box parity weight label ++ tail) ∧
        Within code h r6 (.branch (.register 15) (emitExit encode emit) (.ret [.register 7]))
          [.pointer q] out (1200*(n+1)^2+70) := by
    by_cases hm : order = .eq
    · let node : ScalarNodeCodec.Words n := ⟨true,anchor,current,box,parity⟩
      let ptrs : RegisterNodeDecode.Pointers := ⟨true,ap,cp,bp,pp⟩
      have hn : RegisterNodeDecode.At h ptrs node := ⟨rfl,ha,hc,hb,hp⟩
      obtain ⟨mid,dest,he,hmiddle,hd,enc⟩ := RegisterNodeEncode.compiled code arith harith hh node ptrs hn hstates hblock hone htwo
      obtain ⟨out,q,heout,ho,hq,emitter⟩ := RegisterArcEmitter.compiled code hmiddle (hs.mono he) hd (hcost.mono he) (htail.mono he)
      let r7 := bindResults r6 [14] [.pointer dest]
      let r8 := bindResults r7 [15] [.pointer q]
      have ret : Within code out r8 (.ret [.register 15]) [.pointer q] out 3 := by
        simpa [values,Atom.eval,r8,bindResults] using Within.ret code out r8 [.register 15]
      have eargs : values r7 [.register 0,.register 14,.register 6,.register 7] =
          [.pointer sp,.pointer dest,.pointer cost,.pointer acc] := by
        simp [values,Atom.eval,r7,r6,r5,r4,r3,r2,r1,r0,RegisterComparator.flags,bindResults,loadRegisters,decoded,initialRegisters]
      have ecall := Within.call (procedure := emit) (arguments := [.register 0,.register 14,.register 6,.register 7])
        (results := [15]) (regs := r7) (by simpa only [eargs,hemit] using emitter) ret
      have args : values r6 [.flag true,.register 1,.register 2,.register 3,.register 4,
          .register 10,.register 11,.register 12,.register 13] =
          ptrs.outputs ++ [.pointer states,.pointer block,.pointer one,.pointer two] := by
        simp [values,Atom.eval,r6,r5,r4,r3,r2,r1,r0,RegisterComparator.flags,bindResults,loadRegisters,decoded,initialRegisters,
          ptrs,RegisterNodeDecode.Pointers.outputs]
      have ecall := Within.call (procedure := encode) (arguments := [.flag true,.register 1,.register 2,.register 3,.register 4,
          .register 10,.register 11,.register 12,.register 13]) (results := [14]) (regs := r6)
        (by simpa only [args,hencode] using enc) ecall
      have branch := Within.branch (test := .register 15) (b := true) (yes := emitExit encode emit) (no := .ret [.register 7])
        (by simp [Atom.eval,r6,bindResults,RegisterComparator.flags,hm]) ecall
      refine ⟨out,q,he.trans heout,ho,?_,branch.mono (by simp;omega)⟩
      simpa [arcs,show (Bits.compare current anchor).1 = .eq from hm,node] using hq
    · have ret : Within code h r6 (.ret [.register 7]) [.pointer acc] h 3 := by
        simpa [values,Atom.eval,r6,r5,r4,r3,r2,r1,r0,RegisterComparator.flags,bindResults,loadRegisters,decoded,initialRegisters]
          using Within.ret code h r6 [.register 7]
      have branch := Within.branch (test := .register 15) (b := false) (yes := emitExit encode emit) (no := .ret [.register 7])
        (by simp [Atom.eval,r6,bindResults,RegisterComparator.flags,hm]) ret
      refine ⟨h,acc,.refl h,hh,?_,branch.mono (by omega)⟩
      simpa [arcs,show (Bits.compare current anchor).1 ≠ .eq from hm] using htail
  have args : values r5 [.register 2,.register 1] = [.pointer cp,.pointer ap] := by
    simp [values,Atom.eval,r5,r4,r3,r2,r1,r0,loadRegisters,decoded,initialRegisters]
  have call := Within.call (procedure := compare) (arguments := [.register 2,.register 1])
    (results := [14,15]) (regs := r5) (by simpa only [args] using cmp) branch
  refine ⟨out,q,he,ho,hq,?_⟩
  exact (parsed.within call).mono (by simp [reads];omega)

end WeightedMIS.RegisterExit
