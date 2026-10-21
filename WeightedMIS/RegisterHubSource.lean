module

public import WeightedMIS.RegisterHubEntries
public import WeightedMIS.ExpandedGenerationData
public import WeightedMIS.WordNodeCodec

/-!
# Hub-source generation from shared graph data

A fixed parser reads the source data, shares the arithmetic and connector-cost
records, constructs a hub context, and enumerates precisely its anchor states.
-/

@[expose] public section

namespace WeightedMIS.RegisterHubSource

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer ExpandedWords
open RegisterPairReads

variable {p n cbits : ℕ}

def context {Row : Type*} (source box parity : Bits n) (data : GenerationData Row n cbits) :
    RegisterHubEntries.Context n cbits :=
  ⟨source,box,parity,data.arithmetic,data.weight,data.label⟩

/-- Arguments are source, box, parity, arithmetic, and cost/label pointers. -/
def packBody : Command p :=
  .allocate 5 (.pair (.register 3) (.register 4))
    (.allocate 6 (.pair (.register 2) (.register 5))
      (.allocate 7 (.pair (.register 1) (.register 6))
        (.allocate 8 (.pair (.register 0) (.register 7)) (.ret [.register 8]))))

private theorem pair_safe {h : Heap} (hh : Valid h) {a b : Ptr}
    (ha : a < h.length) (hb : b < h.length) :
    Extends h (h ++ [.pair a b]) ∧ Valid (h ++ [.pair a b]) := by
  have hs := safe_allocate h hh (.pair a b) (by
    intro x hx
    simp only [Cell.references,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> assumption)
  exact ⟨hs.1,hs.2.1⟩

theorem pack_compiled (code : Code p) {h : Heap} (hh : Valid h)
    {sp bp pp arp cl : Ptr} {ctx : RegisterHubEntries.Context n cbits}
    (hs : BitsAt h sp ctx.source) (hb : BitsAt h bp ctx.box) (hp : BitsAt h pp ctx.parity)
    (ha : ArithmeticAt h arp ctx.arithmetic) (hc : CostLabelAt h cl ctx.weight ctx.label) :
    ∃ out result, Extends h out ∧ Valid out ∧ RegisterHubEntries.ContextAt out result ctx ∧
      Within code h (initialRegisters [.pointer sp,.pointer bp,.pointer pp,.pointer arp,.pointer cl])
        packBody [.pointer result] out 35 := by
  have har : arp < h.length := by
    obtain ⟨base,t1,s,t2,t,t3,o,t4,two,z,h0,_⟩ := ha
    exact List.getElem?_eq_some_iff.mp h0 |>.1
  have hcl : cl < h.length := by
    obtain ⟨wp,h0,_⟩ := hc
    exact List.getElem?_eq_some_iff.mp h0 |>.1
  let h1 := h ++ [.pair arp cl]
  have a1 : Extends h h1 ∧ Valid h1 := pair_safe hh har hcl
  let h2 := h1 ++ [.pair pp h.length]
  have a2 : Extends h1 h2 ∧ Valid h2 := pair_safe a1.2
    (hp.mono a1.1).allocated (by simp [h1])
  let h3 := h2 ++ [.pair bp h1.length]
  have a3 : Extends h2 h3 ∧ Valid h3 := pair_safe a2.2
    (hb.mono (a1.1.trans a2.1)).allocated (by simp [h2])
  let out := h3 ++ [.pair sp h2.length]
  have a4 : Extends h3 out ∧ Valid out := pair_safe a3.2
    (hs.mono (a1.1.trans (a2.1.trans a3.1))).allocated (by simp [h3])
  have ext := a1.1.trans (a2.1.trans (a3.1.trans a4.1))
  have c1 : h1[h.length]? = some (.pair arp cl) := by simp [h1]
  have c2 : h2[h1.length]? = some (.pair pp h.length) := by simp [h2]
  have c3 : h3[h2.length]? = some (.pair bp h1.length) := by simp [h3]
  have c4 : out[h3.length]? = some (.pair sp h2.length) := by simp [out]
  have ctxAt : RegisterHubEntries.ContextAt out h3.length ctx :=
    ⟨sp,h2.length,bp,h1.length,pp,h.length,arp,cl,c4,a4.1.lookup c3,
      (a3.1.trans a4.1).lookup c2,(a2.1.trans (a3.1.trans a4.1)).lookup c1,
      hs.mono ext,hb.mono ext,hp.mono ext,ha.mono ext,hc.mono ext⟩
  let r0 := initialRegisters [Value.pointer sp,.pointer bp,.pointer pp,.pointer arp,.pointer cl]
  let r1 := Function.update r0 5 (Value.pointer h.length)
  let r2 := Function.update r1 6 (Value.pointer h1.length)
  let r3 := Function.update r2 7 (Value.pointer h2.length)
  let r4 := Function.update r3 8 (Value.pointer h3.length)
  have last : Within code out r4 (.ret [.register 8]) [.pointer h3.length] out 3 := by
    simpa [r4,values,Atom.eval] using Within.ret code out r4 [.register 8]
  have p4 := Within.allocate (h := h3) (regs := r3) (dst := 8)
    (expr := .pair (.register 0) (.register 7))
    (by simp [CellExpr.eval,Atom.eval,r3,r2,r1,r0,initialRegisters,Value.asPointer]) last
  have p3 := Within.allocate (h := h2) (regs := r2) (dst := 7)
    (expr := .pair (.register 1) (.register 6))
    (by simp [CellExpr.eval,Atom.eval,r2,r1,r0,initialRegisters,Value.asPointer]) p4
  have p2 := Within.allocate (h := h1) (regs := r1) (dst := 6)
    (expr := .pair (.register 2) (.register 5))
    (by simp [CellExpr.eval,Atom.eval,r1,r0,initialRegisters,Value.asPointer]) p3
  have p1 := Within.allocate (h := h) (regs := r0) (dst := 5)
    (expr := .pair (.register 3) (.register 4))
    (by simp [CellExpr.eval,Atom.eval,r0,initialRegisters,Value.asPointer]) p2
  exact ⟨out,h3.length,ext,a4.2,ctxAt,p1⟩

def fields : List Fields :=
  [(3,5,6),(6,14,6),(6,14,7),(5,14,6),(6,8,6),(6,14,6),(6,9,6),(6,14,10)]

def finishBody (pack hubRange : Fin p) : Command p :=
  .call pack [.register 0,.register 1,.register 2,.register 5,.register 7] [11]
    (.call hubRange [.register 10,.register 8,.register 9,.register 11,.register 4] [12]
      (.ret [.register 12]))

/-- Arguments are source, box, parity, shared generation data, and accumulator. -/
def hubSourceBody (pack hubRange : Fin p) : Command p := readPairs fields (finishBody pack hubRange)

theorem compiled_range {Row : Type*} (code : Code p) (pack hubRange range scan item encode emit cmp : Fin p)
    (arith : RegisterHorner.Procedures p) (harith : arith.Matches code)
    (hpack : code pack = packBody) (hhubRange : code hubRange = RegisterHubEntries.rangeBody range scan)
    (hrange : code range = RegisterWordRange.rangeBody range arith.add cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hscan : code scan = RegisterListFlatMap.body scan item)
    (hitem : code item = RegisterHubEntries.body encode emit)
    (hencode : code encode = RegisterNodeEncode.encodeBody arith.mul arith.add)
    (hemit : code emit = RegisterArcEmitter.emitBody)
    {h : Heap} (hh : Valid h) {sp bp pp dp tail : Ptr}
    {source box parity : Bits n} {data : GenerationData Row n cbits}
    {entries : List (RawArc Ptr n cbits)} {key : Walks.State Row → Bits n}
    (hs : BitsAt h sp source) (hb : BitsAt h bp box) (hp : BitsAt h pp parity)
    (hd : GenerationAt key h dp data) (hone : data.arithmetic.one.value = 1)
    (hl : TraceAt h tail entries) :
    ∃ out result, ∃ words : List (Bits n), Extends h out ∧ Valid out ∧
      words.map Bits.value = List.range' 0 data.arithmetic.states.value ∧
      TraceAt out result (words.flatMap (fun a => [RegisterHubEntries.entry (context source box parity data) a]) ++ entries) ∧
      Within code h (initialRegisters [.pointer sp,.pointer bp,.pointer pp,.pointer dp,.pointer tail])
        (hubSourceBody pack hubRange) [.pointer result] out
        (RegisterHubEntries.rangeBudget n data.arithmetic.states.value + 150) := by
  obtain ⟨arp,t1,templates,t2,shape,cl,d0,d1,d2,ha,_ht,_hshape,hcl,_hlen⟩ := hd
  obtain ⟨base,a1,states,a2,block,a3,one,a4,two,zeroPtr,a0,ac1,ac2,ac3,ac4,
    _hbase,hS,_hT,h1,_h2,hz⟩ := ha
  have ha' : ArithmeticAt h arp data.arithmetic :=
    ⟨base,a1,states,a2,block,a3,one,a4,two,zeroPtr,a0,ac1,ac2,ac3,ac4,_hbase,hS,_hT,h1,_h2,hz⟩
  let ctx := context source box parity data
  obtain ⟨mid,cp,he,hm,hctx,packed⟩ := pack_compiled code hh (ctx := ctx) hs hb hp ha' hcl
  obtain ⟨out,result,words,heout,hout,hvalues,hresult,generated⟩ :=
    RegisterHubEntries.range_compiled code range scan item encode emit cmp arith harith
      hrange hcmp hscan hitem hencode hemit hm (hz.mono he) (hS.mono he) (h1.mono he)
      hone hctx (hl.mono he)
  let r0 := initialRegisters [Value.pointer sp,.pointer bp,.pointer pp,.pointer dp,.pointer tail]
  let r1 := loadRegisters r0 5 6 15 (.pair arp t1)
  let r2 := loadRegisters r1 14 6 15 (.pair templates t2)
  let r3 := loadRegisters r2 14 7 15 (.pair shape cl)
  let r4 := loadRegisters r3 14 6 15 (.pair base a1)
  let r5 := loadRegisters r4 8 6 15 (.pair states a2)
  let r6 := loadRegisters r5 14 6 15 (.pair block a3)
  let r7 := loadRegisters r6 9 6 15 (.pair one a4)
  let r8 := loadRegisters r7 14 10 15 (.pair two zeroPtr)
  have reads : Reads h r0 fields r8 := by
    refine .cons (by simp [r0,initialRegisters]) d0 ?_
    refine .cons (by simp [loadRegisters,decoded]) d1 ?_
    refine .cons (by simp [loadRegisters,decoded]) d2 ?_
    refine .cons (by simp [r3,r2,r1,loadRegisters,decoded]) a0 ?_
    refine .cons (by simp [loadRegisters,decoded]) ac1 ?_
    refine .cons (by simp [loadRegisters,decoded]) ac2 ?_
    refine .cons (by simp [loadRegisters,decoded]) ac3 ?_
    refine .cons (by simp [loadRegisters,decoded]) ac4 (.nil _)
  let r9 := bindResults r8 [11] [Value.pointer cp]
  let r10 := bindResults r9 [12] [Value.pointer result]
  have last : Within code out r10 (.ret [.register 12]) [.pointer result] out 3 := by
    simpa [r10,bindResults,values,Atom.eval] using Within.ret code out r10 [.register 12]
  have rangeArgs : values r9 [.register 10,.register 8,.register 9,.register 11,.register 4] =
      [.pointer zeroPtr,.pointer states,.pointer one,.pointer cp,.pointer tail] := by
    simp [r9,r8,r7,r6,r5,r4,r3,r2,r1,r0,values,Atom.eval,bindResults,loadRegisters,decoded,initialRegisters]
  have rangeCall := Within.call (procedure := hubRange)
    (arguments := [.register 10,.register 8,.register 9,.register 11,.register 4]) (results := [12]) (regs := r9)
    (by simpa only [rangeArgs,hhubRange] using generated) last
  have packArgs : values r8 [.register 0,.register 1,.register 2,.register 5,.register 7] =
      [.pointer sp,.pointer bp,.pointer pp,.pointer arp,.pointer cl] := by
    simp [r8,r7,r6,r5,r4,r3,r2,r1,r0,values,Atom.eval,loadRegisters,decoded,initialRegisters]
  have packCall := Within.call (procedure := pack)
    (arguments := [.register 0,.register 1,.register 2,.register 5,.register 7]) (results := [11]) (regs := r8)
    (by simpa only [packArgs,hpack] using packed) rangeCall
  refine ⟨out,result,words,he.trans heout,hout,hvalues,hresult,?_⟩
  exact (reads.within packCall).mono (by simp [fields,ctx,context]; omega)

def anchors {Row : Type*} (data : GenerationData Row n cbits) : List (Bits n) :=
  (List.range data.arithmetic.states.value).map (SparseSearchGraph.encodeBits n)

def arcs {Row : Type*} (data : GenerationData Row n cbits) (source box parity : Bits n) :
    List (RawArc Ptr n cbits) :=
  (anchors data).flatMap (fun a => [RegisterHubEntries.entry (context source box parity data) a])

/-- The bounded binary representation makes value-level interval enumeration
an exact list equality, reusable by the outer source enumerator. -/
theorem words_eq_encoded (limit : Bits n) (words : List (Bits n))
    (hw : words.map Bits.value = List.range' 0 limit.value) :
    words = (List.range limit.value).map (SparseSearchGraph.encodeBits n) := by
  apply (List.map_injective_iff.mpr (ScalarNodeCodec.bits_value_injective n))
  have he : ((List.range limit.value).map (SparseSearchGraph.encodeBits n)).map Bits.value =
      List.range limit.value := by
    simp only [List.map_map]
    conv_rhs => rw [← List.map_id (List.range limit.value)]
    apply List.map_congr_left
    intro i hi
    exact SparseSearchGraph.encodeBits_value n i ((List.mem_range.mp hi).trans (Bits.value_lt _))
  exact hw.trans (by simpa only [List.range_eq_range'] using he.symm)

theorem words_eq_anchors {Row : Type*} (data : GenerationData Row n cbits) (words : List (Bits n))
    (hw : words.map Bits.value = List.range' 0 data.arithmetic.states.value) : words = anchors data :=
  words_eq_encoded data.arithmetic.states words hw

theorem compiled {Row : Type*} (code : Code p) (pack hubRange range scan item encode emit cmp : Fin p)
    (arith : RegisterHorner.Procedures p) (harith : arith.Matches code)
    (hpack : code pack = packBody) (hhubRange : code hubRange = RegisterHubEntries.rangeBody range scan)
    (hrange : code range = RegisterWordRange.rangeBody range arith.add cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hscan : code scan = RegisterListFlatMap.body scan item)
    (hitem : code item = RegisterHubEntries.body encode emit)
    (hencode : code encode = RegisterNodeEncode.encodeBody arith.mul arith.add)
    (hemit : code emit = RegisterArcEmitter.emitBody)
    {h : Heap} (hh : Valid h) {sp bp pp dp tail : Ptr}
    {source box parity : Bits n} {data : GenerationData Row n cbits}
    {entries : List (RawArc Ptr n cbits)} {key : Walks.State Row → Bits n}
    (hs : BitsAt h sp source) (hb : BitsAt h bp box) (hp : BitsAt h pp parity)
    (hd : GenerationAt key h dp data) (hone : data.arithmetic.one.value = 1)
    (hl : TraceAt h tail entries) :
    ∃ out result, Extends h out ∧ Valid out ∧
      TraceAt out result (arcs data source box parity ++ entries) ∧
      Within code h (initialRegisters [.pointer sp,.pointer bp,.pointer pp,.pointer dp,.pointer tail])
        (hubSourceBody pack hubRange) [.pointer result] out
        (RegisterHubEntries.rangeBudget n data.arithmetic.states.value + 150) := by
  obtain ⟨out,result,words,he,ho,hwords,ht,hrun⟩ := compiled_range code pack hubRange range scan item
    encode emit cmp arith harith hpack hhubRange hrange hcmp hscan hitem hencode hemit
      hh hs hb hp hd hone hl
  rw [words_eq_anchors data words hwords] at ht
  exact ⟨out,result,he,ho,ht,hrun⟩

end WeightedMIS.RegisterHubSource
