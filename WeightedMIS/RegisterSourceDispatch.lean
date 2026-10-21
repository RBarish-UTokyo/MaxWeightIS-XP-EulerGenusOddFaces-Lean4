module

public import WeightedMIS.RegisterWorkSource
public import WeightedMIS.RegisterNodeDecode

/-! # Closed numeric-source decoding and hub/work dispatch -/

@[expose] public section

namespace WeightedMIS.RegisterSourceDispatch

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.EfficientSearch.Pointer WeightedMIS.RegisterPairReads

set_option maxRecDepth 4000

variable {p n cbits : ℕ} {Row : Type*}

def reads : List Fields := [(1,3,4),(3,4,5),(5,6,5),(5,7,5),(5,8,5),(5,9,10)]

def hubCall (hub : Fin p) : Command p :=
  .call hub [.register 0,.register 6,.register 7,.register 1,.register 2] [8] (.ret [.register 8])

def workCall (work : Fin p) : Command p :=
  .call work [.register 0,.register 4,.register 5,.register 6,.register 7,.register 1,.register 2]
    [8] (.ret [.register 8])

def body (decode hub work : Fin p) : Command p :=
  readPairs reads (.call decode [.register 0,.register 6,.register 7,.register 8,.register 9] [3,4,5,6,7]
    (.branch (.register 3) (hubCall hub) (workCall work)))

def node (data : GenerationData Row n cbits) (source : Bits n) : ScalarNodeCodec.Words n :=
  ScalarNodeCodec.decodeWords source data.arithmetic.states data.arithmetic.block data.arithmetic.one data.arithmetic.two

def arcs (hubArcs : GenerationData Row n cbits → Bits n → Bits n → Bits n → List (RawArc Ptr n cbits))
    (key : Walks.State Row → Bits n) (data : GenerationData Row n cbits) (source : Bits n) :
    List (RawArc Ptr n cbits) :=
  let out := node data source
  if out.hub then hubArcs data source out.box out.parity
  else RegisterWorkSource.arcs key data source out.anchor out.current out.box out.parity

/-- This compositional rule calls one fixed hub procedure identifier. Its
hypothesis is a refinement theorem for that same finite-code table, not a
host-language instruction or an oracle selected during execution. -/
theorem compiled (code : Code p) (decode hub work quotRem : Fin p)
    (workIds : RegisterWorkSource.Procedures p) (moves : RegisterCandidate.Procedures p)
    (arith : RegisterHorner.Procedures p) (digit complement : Fin p)
    (division : RegisterDivision.Procedures p)
    (hwork : code work = RegisterWorkSource.body workIds)
    (hworkCode : workIds.Matches code moves arith digit complement division)
    (hdecode : code decode = RegisterNodeDecode.decodeBody quotRem division.cmp division.sub)
    (hqr : code quotRem = RegisterQuotRem.body division.divide)
    (hubArcs : GenerationData Row n cbits → Bits n → Bits n → Bits n → List (RawArc Ptr n cbits))
    (hubBudget : GenerationData Row n cbits → ℕ)
    (hubCompiled : ∀ {h : Heap}, Valid h → ∀ {key : Walks.State Row → Bits n}
      {data : GenerationData Row n cbits} {source box parity : Bits n} {sp bp pp dp acc : Ptr}
      {tail : List (RawArc Ptr n cbits)},
      BitsAt h sp source → BitsAt h bp box → BitsAt h pp parity → GenerationAt key h dp data →
      data.arithmetic.one.value = 1 → TraceAt h acc tail →
      ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (hubArcs data source box parity ++ tail) ∧
        Within code h (initialRegisters [.pointer sp,.pointer bp,.pointer pp,.pointer dp,.pointer acc])
          (code hub) [.pointer q] out (hubBudget data))
    {key : Walks.State Row → Bits n} {data : GenerationData Row n cbits}
    {h : Heap} (hh : Valid h) {source : Bits n} {sp dp acc : Ptr} {tail : List (RawArc Ptr n cbits)}
    (hs : BitsAt h sp source) (hg : GenerationAt key h dp data)
    (hone : data.arithmetic.one.value = 1) (htail : TraceAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (arcs hubArcs key data source ++ tail) ∧
      Within code h (initialRegisters [.pointer sp,.pointer dp,.pointer acc]) (body decode hub work)
        [.pointer q] out (1600*(n+1)^2 + hubBudget data +
          RegisterWorkSource.budget n data.shape.length data.templates.length + 100) := by
  obtain ⟨arp,t1,templates,t2,shape,cost,hg0,hg1,hg2,har,ht,hshape,hcost,hlen⟩ := hg
  have hg : GenerationAt key h dp data :=
    ⟨arp,t1,templates,t2,shape,cost,hg0,hg1,hg2,har,ht,hshape,hcost,hlen⟩
  obtain ⟨base,a1,states,a2,block,a3,one,a4,two,zero,h0,h1,h2,h3,h4,hbase,hstates,hblock,h1word,h2word,hzero⟩ := har
  obtain ⟨mid,ptrs,he,vm,hn,decoder⟩ := RegisterNodeDecode.compiled code quotRem division hqr
    hworkCode.divisionCode hh hs hstates hblock h1word h2word
  obtain ⟨hubEq,hanchor,hcurrent,hbox,hparity⟩ := hn
  change ptrs.hub = (node data source).hub at hubEq
  change BitsAt mid ptrs.anchor (node data source).anchor at hanchor
  change BitsAt mid ptrs.current (node data source).current at hcurrent
  change BitsAt mid ptrs.box (node data source).box at hbox
  change BitsAt mid ptrs.parity (node data source).parity at hparity
  let r0 := initialRegisters [Value.pointer sp,.pointer dp,.pointer acc]
  let r1 := loadRegisters r0 3 4 15 (.pair arp t1)
  let r2 := loadRegisters r1 4 5 15 (.pair base a1)
  let r3 := loadRegisters r2 6 5 15 (.pair states a2)
  let r4 := loadRegisters r3 7 5 15 (.pair block a3)
  let r5 := loadRegisters r4 8 5 15 (.pair one a4)
  let r6 := loadRegisters r5 9 10 15 (.pair two zero)
  let r7 := bindResults r6 [3,4,5,6,7] ptrs.outputs
  have parsed : Reads h r0 reads r6 := by
    refine .cons (by simp [r0,initialRegisters]) hg0 ?_
    refine .cons (by simp [r1,loadRegisters,decoded]) h0 ?_
    refine .cons (by simp [r2,loadRegisters,decoded]) h1 ?_
    refine .cons (by simp [r3,loadRegisters,decoded]) h2 ?_
    refine .cons (by simp [r4,loadRegisters,decoded]) h3 ?_
    refine .cons (by simp [r5,loadRegisters,decoded]) h4 (.nil _)
  obtain ⟨out,q,heout,vo,hq,branch⟩ :
      ∃ out q, Extends mid out ∧ Valid out ∧ TraceAt out q (arcs hubArcs key data source ++ tail) ∧
        Within code mid r7 (.branch (.register 3) (hubCall hub) (workCall work)) [.pointer q] out
          (hubBudget data + RegisterWorkSource.budget n data.shape.length data.templates.length + 21) := by
    cases hubFlag : (node data source).hub with
    | true =>
      obtain ⟨out,q,ext,valid,rep,run⟩ := hubCompiled vm (hs.mono he) hbox hparity (hg.mono he) hone (htail.mono he)
      let r8 := bindResults r7 [8] [.pointer q]
      have ret : Within code out r8 (.ret [.register 8]) [.pointer q] out 3 := by
        simpa [values,Atom.eval,r8,bindResults] using Within.ret code out r8 [.register 8]
      have args : values r7 [.register 0,.register 6,.register 7,.register 1,.register 2] =
          [.pointer sp,.pointer ptrs.box,.pointer ptrs.parity,.pointer dp,.pointer acc] := by
        simp [values,Atom.eval,r7,r6,r5,r4,r3,r2,r1,r0,bindResults,loadRegisters,decoded,
          initialRegisters,RegisterNodeDecode.Pointers.outputs]
      have call := Within.call (procedure := hub) (arguments := [.register 0,.register 6,.register 7,.register 1,.register 2])
        (results := [8]) (regs := r7) (by simpa only [args] using run) ret
      have branch := Within.branch (test := .register 3) (b := true) (yes := hubCall hub) (no := workCall work)
        (by simp [Atom.eval,r7,bindResults,RegisterNodeDecode.Pointers.outputs,hubEq,hubFlag]) call
      exact ⟨out,q,ext,valid,by simpa [arcs,hubFlag] using rep,branch.mono (by simp;omega)⟩
    | false =>
      obtain ⟨out,q,ext,valid,rep,run⟩ := RegisterWorkSource.compiled code workIds moves arith digit complement
        division hworkCode vm (hs.mono he) hanchor hcurrent hbox hparity (hg.mono he) (htail.mono he)
      let r8 := bindResults r7 [8] [.pointer q]
      have ret : Within code out r8 (.ret [.register 8]) [.pointer q] out 3 := by
        simpa [values,Atom.eval,r8,bindResults] using Within.ret code out r8 [.register 8]
      have args : values r7 [.register 0,.register 4,.register 5,.register 6,.register 7,.register 1,.register 2] =
          [.pointer sp,.pointer ptrs.anchor,.pointer ptrs.current,.pointer ptrs.box,.pointer ptrs.parity,.pointer dp,.pointer acc] := by
        simp [values,Atom.eval,r7,r6,r5,r4,r3,r2,r1,r0,bindResults,loadRegisters,decoded,
          initialRegisters,RegisterNodeDecode.Pointers.outputs]
      have call := Within.call (procedure := work) (arguments := [.register 0,.register 4,.register 5,.register 6,.register 7,.register 1,.register 2])
        (results := [8]) (regs := r7) (by simpa only [args,hwork] using run) ret
      have branch := Within.branch (test := .register 3) (b := false) (yes := hubCall hub) (no := workCall work)
        (by simp [Atom.eval,r7,bindResults,RegisterNodeDecode.Pointers.outputs,hubEq,hubFlag]) call
      exact ⟨out,q,ext,valid,by simpa [arcs,hubFlag] using rep,branch.mono (by simp;omega)⟩
  have args : values r6 [.register 0,.register 6,.register 7,.register 8,.register 9] =
      [.pointer sp,.pointer states,.pointer block,.pointer one,.pointer two] := by
    simp [values,Atom.eval,r6,r5,r4,r3,r2,r1,r0,loadRegisters,decoded,initialRegisters]
  have call := Within.call (procedure := decode) (arguments := [.register 0,.register 6,.register 7,.register 8,.register 9])
    (results := [3,4,5,6,7]) (regs := r6) (by simpa only [args,hdecode] using decoder) branch
  exact ⟨out,q,he.trans heout,vo,hq,(parsed.within call).mono (by simp [reads];omega)⟩

end WeightedMIS.RegisterSourceDispatch
