module

public import WeightedMIS.ExpandedGenerationData
public import WeightedMIS.RegisterContextPack
public import WeightedMIS.RegisterTemplateScan
public import WeightedMIS.RegisterExit
public import WeightedMIS.RegisterDigits

/-! # Closed enumeration of all arcs from one decoded working source -/

@[expose] public section

namespace WeightedMIS.RegisterWorkSource

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.EfficientSearch.Pointer WeightedMIS.RegisterPairReads

variable {p n cbits : ℕ} {Row : Type*}

structure Procedures (p : ℕ) where
  digits : Fin p
  pack : Fin p
  scan : Fin p
  candidate : Fin p
  exit : Fin p

def reads : List Fields := [(5,7,8),(8,9,8),(8,10,11),(7,12,13)]

/-- Arguments: source, anchor, current, box, parity, shared data, accumulator. -/
def body (ids : Procedures p) : Command p :=
  readPairs reads
    (.call ids.digits [.register 3,.register 12,.register 10] [14]
      (.call ids.pack [.register 0,.register 1,.register 2,.register 4,.register 14,.register 7] [13]
        (.call ids.scan [.register 9,.register 13,.register 6] [14]
          (.call ids.exit [.register 0,.register 1,.register 2,.register 3,.register 4,
              .register 7,.register 11,.register 14] [15] (.ret [.register 15])))))

structure Procedures.Matches (ids : Procedures p) (code : Code p)
    (moves : RegisterCandidate.Procedures p) (arith : RegisterHorner.Procedures p)
    (digit complement : Fin p) (division : RegisterDivision.Procedures p) : Prop where
  moveCode : moves.Matches code arith digit complement
  divisionCode : division.Matches code
  digits : code ids.digits = RegisterDigits.decodeBody ids.digits division.divide
  pack : code ids.pack = RegisterContextPack.body
  scan : code ids.scan = RegisterListFlatMap.body ids.scan ids.candidate
  candidate : code ids.candidate = RegisterCandidate.candidateBody moves
  exit : code ids.exit = RegisterExit.body moves.compare moves.encode moves.emit

def context (data : GenerationData Row n cbits) (source anchor current box parity : Bits n) : WorkContext n :=
  ⟨source,anchor,current,parity,RegisterDigits.decodeWords data.arithmetic.base data.shape.length box,data.arithmetic⟩

def arcs (key : Walks.State Row → Bits n) (data : GenerationData Row n cbits)
    (source anchor current box parity : Bits n) : List (RawArc Ptr n cbits) :=
  RegisterExit.arcs data.arithmetic source anchor current box parity data.weight data.label ++
    data.templates.flatMap (candidate key (context data source anchor current box parity))

def budget (n d m : ℕ) : ℕ :=
  ((400*(n+1)^2+43)*d+13) +
    ((RegisterCandidate.candidateBudget n d+27)*m+13) + (1200*(n+1)^2+36*n+150) + 130

theorem compiled (code : Code p) (ids : Procedures p)
    (moves : RegisterCandidate.Procedures p) (arith : RegisterHorner.Procedures p)
    (digit complement : Fin p) (division : RegisterDivision.Procedures p)
    (hcode : ids.Matches code moves arith digit complement division)
    {key : Walks.State Row → Bits n} {data : GenerationData Row n cbits}
    {h : Heap} (hh : Valid h) {source anchor current box parity : Bits n}
    {sp ap cp bp pp dataPtr acc : Ptr} {tail : List (RawArc Ptr n cbits)}
    (hs : BitsAt h sp source) (ha : BitsAt h ap anchor) (hc : BitsAt h cp current)
    (hb : BitsAt h bp box) (hp : BitsAt h pp parity) (hg : GenerationAt key h dataPtr data)
    (htail : TraceAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (arcs key data source anchor current box parity ++ tail) ∧
      Within code h (initialRegisters [.pointer sp,.pointer ap,.pointer cp,.pointer bp,.pointer pp,
        .pointer dataPtr,.pointer acc]) (body ids) [.pointer q] out (budget n data.shape.length data.templates.length) := by
  obtain ⟨arp,t1,templates,t2,shape,cost,hg0,hg1,hg2,har,ht,hshape,hcost,hlen⟩ := hg
  obtain ⟨base,t3,states,t4,block,t5,one,t6,two,zero,har0,har1,har2,har3,har4,
    hbase,hstates,hblock,hone,htwo,hzero⟩ := har
  have har : ArithmeticAt h arp data.arithmetic :=
    ⟨base,t3,states,t4,block,t5,one,t6,two,zero,har0,har1,har2,har3,har4,
      hbase,hstates,hblock,hone,htwo,hzero⟩
  obtain ⟨shapePtrs,hshapeList,hshapeWords⟩ := hshape
  have shapeLength : shapePtrs.length = data.shape.length := hshapeWords.length_eq
  obtain ⟨h1,dp,e1,v1,hd,decode⟩ := RegisterDigits.compiled code ids.digits division hcode.digits
    hcode.divisionCode hh hb hbase shapePtrs hshapeList
  have hdigits : WordsAt h1 dp (context data source anchor current box parity).digits := by
    simpa only [context,shapeLength] using hd
  let ctx := context data source anchor current box parity
  obtain ⟨h2,ctxp,e2,v2,hctx,pack⟩ := RegisterContextPack.compiled code v1
    (ctx := ctx) (hs.mono e1) (ha.mono e1) (hc.mono e1) (hp.mono e1) hdigits (har.mono e1)
  have e02 := e1.trans e2
  have ht2 := ht.mono e02 (fun _ _ ht => CompiledTemplates.TemplateAt.mono (metaAt := MetadataAt)
    (fun he hm => MetadataAt.mono he hm) e02 ht)
  obtain ⟨h3,mp,e3,v3,hmoves,scan⟩ := RegisterTemplateScan.compiled code ids.scan ids.candidate
    moves arith digit complement hcode.moveCode hcode.scan hcode.candidate v2 ht2 hctx
    (htail.mono e02) (RegisterDigits.decodeWords_length _ _ _) hlen
  have e03 := e02.trans e3
  obtain ⟨out,q,e4,vo,hout,exit⟩ := RegisterExit.compiled code moves.compare moves.encode moves.emit arith
    hcode.moveCode.arithmetic hcode.moveCode.compare hcode.moveCode.encode hcode.moveCode.emit v3
    (hs.mono e03) (ha.mono e03) (hc.mono e03) (hb.mono e03) (hp.mono e03)
    (har.mono e03) (hcost.mono e03) hmoves
  refine ⟨out,q,e03.trans e4,vo,?_,?_⟩
  · simpa only [arcs,List.append_assoc] using hout
  · let r0 := initialRegisters [Value.pointer sp,.pointer ap,.pointer cp,.pointer bp,.pointer pp,
      .pointer dataPtr,.pointer acc]
    let r1 := loadRegisters r0 7 8 15 (.pair arp t1)
    let r2 := loadRegisters r1 9 8 15 (.pair templates t2)
    let r3 := loadRegisters r2 10 11 15 (.pair shape cost)
    let r4 := loadRegisters r3 12 13 15 (.pair base t3)
    have parsed : Reads h r0 reads r4 := by
      refine Reads.cons (ptr := dataPtr) (by simp [r0,initialRegisters]) hg0 ?_
      refine Reads.cons (ptr := t1) (by simp [r1,loadRegisters,decoded]) hg1 ?_
      refine Reads.cons (ptr := t2) (by simp [r2,loadRegisters,decoded]) hg2 ?_
      refine Reads.cons (ptr := arp) (by simp [r3,r2,r1,loadRegisters,decoded]) har0 ?_
      exact Reads.nil r4
    let r5 := bindResults r4 [14] [.pointer dp]
    let r6 := bindResults r5 [13] [.pointer ctxp]
    let r7 := bindResults r6 [14] [.pointer mp]
    let r8 := bindResults r7 [15] [.pointer q]
    have ret : Within code out r8 (.ret [.register 15]) [.pointer q] out 3 := by
      simpa [values,Atom.eval,r8,bindResults] using Within.ret code out r8 [.register 15]
    have exitArgs : values r7 [.register 0,.register 1,.register 2,.register 3,.register 4,
        .register 7,.register 11,.register 14] =
        [.pointer sp,.pointer ap,.pointer cp,.pointer bp,.pointer pp,.pointer arp,.pointer cost,.pointer mp] := by
      simp [values,Atom.eval,r7,r6,r5,r4,r3,r2,r1,r0,bindResults,loadRegisters,decoded,initialRegisters]
    have exitCall := Within.call (procedure := ids.exit) (arguments := [.register 0,.register 1,.register 2,
        .register 3,.register 4,.register 7,.register 11,.register 14]) (results := [15]) (regs := r7)
        (by simpa only [exitArgs,hcode.exit] using exit) ret
    have scanArgs : values r6 [.register 9,.register 13,.register 6] =
        [.pointer templates,.pointer ctxp,.pointer acc] := by
      simp [values,Atom.eval,r6,r5,r4,r3,r2,r1,r0,bindResults,loadRegisters,decoded,initialRegisters]
    have scanCall := Within.call (procedure := ids.scan) (arguments := [.register 9,.register 13,.register 6])
      (results := [14]) (regs := r6) (by simpa only [scanArgs] using scan) exitCall
    have packArgs : values r5 [.register 0,.register 1,.register 2,.register 4,.register 14,.register 7] =
        [.pointer sp,.pointer ap,.pointer cp,.pointer pp,.pointer dp,.pointer arp] := by
      simp [values,Atom.eval,r5,r4,r3,r2,r1,r0,bindResults,loadRegisters,decoded,initialRegisters]
    have packCall := Within.call (procedure := ids.pack)
      (arguments := [.register 0,.register 1,.register 2,.register 4,.register 14,.register 7])
      (results := [13]) (regs := r5) (by simpa only [packArgs,hcode.pack] using pack) scanCall
    have decodeArgs : values r4 [.register 3,.register 12,.register 10] =
        [.pointer bp,.pointer base,.pointer shape] := by
      simp [values,Atom.eval,r4,r3,r2,r1,r0,loadRegisters,decoded,initialRegisters]
    have decodeCall := Within.call (procedure := ids.digits) (arguments := [.register 3,.register 12,.register 10])
      (results := [14]) (regs := r4) (by simpa only [decodeArgs] using decode) packCall
    exact (parsed.within decodeCall).mono (by simp [budget,reads,shapeLength];omega)

end WeightedMIS.RegisterWorkSource
