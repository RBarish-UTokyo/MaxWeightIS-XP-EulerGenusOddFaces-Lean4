module

public import WeightedMIS.RegisterCandidate

/-! # Exact stored-field parsing for local move generation -/

@[expose] public section

namespace WeightedMIS.RegisterCandidate

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.EfficientSearch.Pointer WeightedMIS.RegisterPairReads

variable {p n cbits : ℕ} {Row : Type*}

def RegisterWord (h : Heap) (regs : Registers) (r : Register) (word : Bits n) : Prop :=
  ∃ ptr, regs r = .pointer ptr ∧ BitsAt h ptr word

structure Initial (key : Walks.State Row → Bits n) (h : Heap) (regs : Registers)
    (ctx : WorkContext n) (a : CompiledTemplates.Template Row (ArcMetadata n cbits))
    (tail : List (RawArc Ptr n cbits)) : Prop where
  sourceKey : RegisterWord h regs 5 (key a.source)
  current : RegisterWord h regs 13 ctx.current
  target : RegisterWord h regs 7 (key a.target)
  source : RegisterWord h regs 9 ctx.source
  anchor : RegisterWord h regs 11 ctx.anchor
  parityDigits : ∃ r pp dp, regs 14 = .pointer r ∧ h[r]? = some (.pair pp dp) ∧
    BitsAt h pp ctx.parity ∧ WordsAt h dp ctx.digits
  metadata : ∃ mp, regs 8 = .pointer mp ∧ MetadataAt h mp a.metadata
  arithmetic : ∃ ap, regs 4 = .pointer ap ∧ ArithmeticAt h ap ctx.arithmetic
  tail : ∃ tp, regs 2 = .pointer tp ∧ TraceAt h tp tail

structure Matched (h : Heap) (regs : Registers) (ctx : WorkContext n) (target : Bits n)
    (metadata : ArcMetadata n cbits) (tail : List (RawArc Ptr n cbits)) : Prop where
  source : RegisterWord h regs 9 ctx.source
  anchor : RegisterWord h regs 11 ctx.anchor
  target : RegisterWord h regs 7 target
  parity : RegisterWord h regs 13 ctx.parity
  base : RegisterWord h regs 0 ctx.arithmetic.base
  states : RegisterWord h regs 1 ctx.arithmetic.states
  block : RegisterWord h regs 4 ctx.arithmetic.block
  one : RegisterWord h regs 8 ctx.arithmetic.one
  two : RegisterWord h regs 10 ctx.arithmetic.two
  zero : RegisterWord h regs 12 (Bits.zero n)
  digits : ∃ dp, regs 14 = .pointer dp ∧ WordsAt h dp ctx.digits
  deltas : ∃ dp, regs 5 = .pointer dp ∧ DeltasAt h dp metadata.deltas
  parityCost : ∃ r cp, regs 6 = .pointer r ∧ h[r]? = some (.bit metadata.parity cp) ∧
    CostLabelAt h cp metadata.weight metadata.label
  tail : ∃ tp, regs 2 = .pointer tp ∧ TraceAt h tp tail

theorem parse_initial {key : Walks.State Row → Bits n} {h : Heap} {tp cp ap : Ptr}
    {ctx : WorkContext n} {a : CompiledTemplates.Template Row (ArcMetadata n cbits)}
    {tail : List (RawArc Ptr n cbits)}
    (ht : CompiledTemplates.TemplateAt key MetadataAt h tp a)
    (hc : ContextAt h cp ctx) (ha : TraceAt h ap tail) :
    ∃ regs, Reads h (initialRegisters [.pointer tp,.pointer cp,.pointer ap]) initialReads regs ∧
      Initial key h regs ctx a tail := by
  obtain ⟨src,dst,mp,inside,ht0,ht1,hsrc,hdst,hm⟩ := ht
  obtain ⟨work,ar,source,t1,anchor,t2,current,t3,parity,digits,
    hc0,hc1,hc2,hc3,hc4,hs,hanchor,hcurrent,hparity,hdigits,har⟩ := hc
  let r0 := initialRegisters [Value.pointer tp,.pointer cp,.pointer ap]
  let r1 := loadRegisters r0 3 4 15 (.pair work ar)
  let r2 := loadRegisters r1 5 6 15 (.pair src inside)
  let r3 := loadRegisters r2 7 8 15 (.pair dst mp)
  let r4 := loadRegisters r3 9 10 15 (.pair source t1)
  let r5 := loadRegisters r4 11 12 15 (.pair anchor t2)
  let r6 := loadRegisters r5 13 14 15 (.pair current t3)
  have reads : Reads h r0 initialReads r6 := by
    refine Reads.cons (ptr := cp) (by simp [r0,initialRegisters]) hc0 ?_
    refine Reads.cons (ptr := tp) (by simp [r1,r0,loadRegisters,decoded,initialRegisters]) ht0 ?_
    refine Reads.cons (ptr := inside) (by simp [r2,loadRegisters,decoded]) ht1 ?_
    refine Reads.cons (ptr := work) (by simp [r3,r2,r1,loadRegisters,decoded]) hc1 ?_
    refine Reads.cons (ptr := t1) (by simp [r4,loadRegisters,decoded]) hc2 ?_
    refine Reads.cons (ptr := t2) (by simp [r5,loadRegisters,decoded]) hc3 ?_
    exact Reads.nil r6
  refine ⟨r6,reads,?_⟩
  constructor
  · exact ⟨src,by simp [r6,r5,r4,r3,r2,loadRegisters,decoded],hsrc⟩
  · exact ⟨current,by simp [r6,loadRegisters,decoded],hcurrent⟩
  · exact ⟨dst,by simp [r6,r5,r4,r3,loadRegisters,decoded],hdst⟩
  · exact ⟨source,by simp [r6,r5,r4,loadRegisters,decoded],hs⟩
  · exact ⟨anchor,by simp [r6,r5,loadRegisters,decoded],hanchor⟩
  · exact ⟨t3,parity,digits,by simp [r6,loadRegisters,decoded],hc4,hparity,hdigits⟩
  · exact ⟨mp,by simp [r6,r5,r4,r3,loadRegisters,decoded],hm⟩
  · exact ⟨ar,by simp [r6,r5,r4,r3,r2,r1,loadRegisters,decoded],har⟩
  · exact ⟨ap,by simp [r6,r5,r4,r3,r2,r1,r0,loadRegisters,decoded,initialRegisters],ha⟩

theorem Initial.afterCompare {key : Walks.State Row → Bits n} {h : Heap} {regs : Registers}
    {ctx : WorkContext n} {a : CompiledTemplates.Template Row (ArcMetadata n cbits)}
    {tail : List (RawArc Ptr n cbits)} (hi : Initial key h regs ctx a tail) (x y : Bool) :
    Initial key h (bindResults regs [15,6] [.flag x,.flag y]) ctx a tail := by
  constructor
  · obtain ⟨p,hr,hp⟩ := hi.sourceKey; exact ⟨p,by simpa [bindResults] using hr,hp⟩
  · obtain ⟨p,hr,hp⟩ := hi.current; exact ⟨p,by simpa [bindResults] using hr,hp⟩
  · obtain ⟨p,hr,hp⟩ := hi.target; exact ⟨p,by simpa [bindResults] using hr,hp⟩
  · obtain ⟨p,hr,hp⟩ := hi.source; exact ⟨p,by simpa [bindResults] using hr,hp⟩
  · obtain ⟨p,hr,hp⟩ := hi.anchor; exact ⟨p,by simpa [bindResults] using hr,hp⟩
  · obtain ⟨r,p,d,hr,hc,hp,hd⟩ := hi.parityDigits
    exact ⟨r,p,d,by simpa [bindResults] using hr,hc,hp,hd⟩
  · obtain ⟨p,hr,hp⟩ := hi.metadata; exact ⟨p,by simpa [bindResults] using hr,hp⟩
  · obtain ⟨p,hr,hp⟩ := hi.arithmetic; exact ⟨p,by simpa [bindResults] using hr,hp⟩
  · obtain ⟨p,hr,hp⟩ := hi.tail; exact ⟨p,by simpa [bindResults] using hr,hp⟩

theorem parse_matched {key : Walks.State Row → Bits n} {h : Heap} {regs : Registers}
    {ctx : WorkContext n} {a : CompiledTemplates.Template Row (ArcMetadata n cbits)}
    {tail : List (RawArc Ptr n cbits)} (hi : Initial key h regs ctx a tail) :
    ∃ loaded, Reads h regs matchedReads loaded ∧ Matched h loaded ctx (key a.target) a.metadata tail := by
  obtain ⟨pd,pp,dp,r14,hpd,hparity,hdigits⟩ := hi.parityDigits
  obtain ⟨mp,r8,hm⟩ := hi.metadata
  obtain ⟨delta,pc,cost,hm0,hm1,hdeltas,hcost⟩ := hm
  obtain ⟨ar,r4,har⟩ := hi.arithmetic
  obtain ⟨base,t1,states,t2,block,t3,one,t4,two,zerop,
    ha0,ha1,ha2,ha3,ha4,hbase,hstates,hblock,hone,htwo,hzero⟩ := har
  let r1 := loadRegisters regs 13 14 15 (.pair pp dp)
  let r2 := loadRegisters r1 5 6 15 (.pair delta pc)
  let r3 := loadRegisters r2 0 3 15 (.pair base t1)
  let r4' := loadRegisters r3 1 3 15 (.pair states t2)
  let r5 := loadRegisters r4' 4 3 15 (.pair block t3)
  let r6 := loadRegisters r5 8 3 15 (.pair one t4)
  let r7 := loadRegisters r6 10 12 15 (.pair two zerop)
  have reads : Reads h regs matchedReads r7 := by
    refine Reads.cons r14 hpd ?_
    refine Reads.cons (ptr := mp) (by simpa [r1,loadRegisters,decoded] using r8) hm0 ?_
    refine Reads.cons (ptr := ar) (by simpa [r2,r1,loadRegisters,decoded] using r4) ha0 ?_
    refine Reads.cons (ptr := t1) (by simp [r3,loadRegisters,decoded]) ha1 ?_
    refine Reads.cons (ptr := t2) (by simp [r4',loadRegisters,decoded]) ha2 ?_
    refine Reads.cons (ptr := t3) (by simp [r5,loadRegisters,decoded]) ha3 ?_
    refine Reads.cons (ptr := t4) (by simp [r6,loadRegisters,decoded]) ha4 ?_
    exact Reads.nil r7
  refine ⟨r7,reads,?_⟩
  constructor
  · obtain ⟨p,hr,hp⟩ := hi.source
    exact ⟨p,by simpa [r7,r6,r5,r4',r3,r2,r1,loadRegisters,decoded] using hr,hp⟩
  · obtain ⟨p,hr,hp⟩ := hi.anchor
    exact ⟨p,by simpa [r7,r6,r5,r4',r3,r2,r1,loadRegisters,decoded] using hr,hp⟩
  · obtain ⟨p,hr,hp⟩ := hi.target
    exact ⟨p,by simpa [r7,r6,r5,r4',r3,r2,r1,loadRegisters,decoded] using hr,hp⟩
  · exact ⟨pp,by simp [r7,r6,r5,r4',r3,r2,r1,loadRegisters,decoded],hparity⟩
  · exact ⟨base,by simp [r7,r6,r5,r4',r3,loadRegisters,decoded],hbase⟩
  · exact ⟨states,by simp [r7,r6,r5,r4',loadRegisters,decoded],hstates⟩
  · exact ⟨block,by simp [r7,r6,r5,loadRegisters,decoded],hblock⟩
  · exact ⟨one,by simp [r7,r6,loadRegisters,decoded],hone⟩
  · exact ⟨two,by simp [r7,loadRegisters,decoded],htwo⟩
  · exact ⟨zerop,by simp [r7,loadRegisters,decoded],hzero⟩
  · exact ⟨dp,by simp [r7,r6,r5,r4',r3,r2,r1,loadRegisters,decoded],hdigits⟩
  · exact ⟨delta,by simp [r7,r6,r5,r4',r3,r2,loadRegisters,decoded],hdeltas⟩
  · exact ⟨pc,cost,by simp [r7,r6,r5,r4',r3,r2,loadRegisters,decoded],hm1,hcost⟩
  · obtain ⟨p,hr,hp⟩ := hi.tail
    exact ⟨p,by simpa [r7,r6,r5,r4',r3,r2,r1,loadRegisters,decoded] using hr,hp⟩

end WeightedMIS.RegisterCandidate
