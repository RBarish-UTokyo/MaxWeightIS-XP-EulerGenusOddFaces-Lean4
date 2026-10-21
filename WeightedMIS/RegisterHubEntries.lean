module

public import WeightedMIS.ExpandedContext
public import WeightedMIS.RegisterNodeEncode
public import WeightedMIS.RegisterArcEmitter
public import WeightedMIS.RegisterPairReads
public import WeightedMIS.RegisterListFlatMap
public import WeightedMIS.RegisterWordRange

/-!
# Closed generation of hub-entry arcs

Each enumerated signed-state key is used as both anchor and current state.
The positional encoder and raw-arc emitter construct exactly one outgoing
entry, retaining the hub's box and parity and sharing the cost/label record.
-/

@[expose] public section

namespace WeightedMIS.RegisterHubEntries

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer ExpandedWords
open RegisterPairReads

variable {p n cbits : ℕ}

structure Context (n cbits : ℕ) where
  source : Bits n
  box : Bits n
  parity : Bits n
  arithmetic : ArithmeticWords n
  weight : Bits cbits
  label : Ptr

/-- Four pair cells hold the source, box, parity, arithmetic record, and the
shared cost/label pair. -/
def ContextAt (h : Heap) (cp : Ptr) (ctx : Context n cbits) : Prop :=
  ∃ source t1 box t2 parity t3 arithmetic cost,
    h[cp]? = some (.pair source t1) ∧ h[t1]? = some (.pair box t2) ∧
    h[t2]? = some (.pair parity t3) ∧ h[t3]? = some (.pair arithmetic cost) ∧
    BitsAt h source ctx.source ∧ BitsAt h box ctx.box ∧ BitsAt h parity ctx.parity ∧
    ArithmeticAt h arithmetic ctx.arithmetic ∧ CostLabelAt h cost ctx.weight ctx.label

theorem ContextAt.mono {h out : Heap} (ext : Extends h out) {cp : Ptr}
    {ctx : Context n cbits} (hc : ContextAt h cp ctx) : ContextAt out cp ctx := by
  obtain ⟨s,t1,b,t2,p,t3,a,c,h0,h1,h2,h3,hs,hb,hp,ha,hc⟩ := hc
  exact ⟨s,t1,b,t2,p,t3,a,c,ext.lookup h0,ext.lookup h1,ext.lookup h2,ext.lookup h3,
    hs.mono ext,hb.mono ext,hp.mono ext,ha.mono ext,hc.mono ext⟩

def entry (ctx : Context n cbits) (anchor : Bits n) : RawArc Ptr n cbits :=
  (ctx.source, ⟨ScalarNodeCodec.encodeWords ctx.arithmetic.states ctx.arithmetic.block
    ctx.arithmetic.one ctx.arithmetic.two ⟨false,anchor,anchor,ctx.box,ctx.parity⟩,
    ctx.weight,ctx.label⟩)

def fields : List Fields :=
  [(1,3,4),(4,5,4),(4,6,4),(4,7,8),(7,14,4),(4,9,4),(4,10,4),(4,11,4),(4,12,14)]

def finishBody (encode emit : Fin p) : Command p :=
  .call encode [.flag false,.register 0,.register 0,.register 5,.register 6,
      .register 9,.register 10,.register 11,.register 12] [13]
    (.call emit [.register 3,.register 13,.register 8,.register 2] [14] (.ret [.register 14]))

/-- Arguments are anchor key, hub context, and raw-arc accumulator. -/
def body (encode emit : Fin p) : Command p := readPairs fields (finishBody encode emit)

theorem compiled (code : Code p) (encode emit : Fin p) (arith : RegisterHorner.Procedures p)
    (harith : arith.Matches code)
    (hencode : code encode = RegisterNodeEncode.encodeBody arith.mul arith.add)
    (hemit : code emit = RegisterArcEmitter.emitBody)
    {h : Heap} (hh : Valid h) {ap cp tail : Ptr} {anchor : Bits n}
    {ctx : Context n cbits} {entries : List (RawArc Ptr n cbits)}
    (ha : BitsAt h ap anchor) (hc : ContextAt h cp ctx) (hl : TraceAt h tail entries) :
    ∃ out result, Extends h out ∧ Valid out ∧ TraceAt out result (entry ctx anchor :: entries) ∧
      Within code h (initialRegisters [.pointer ap,.pointer cp,.pointer tail])
        (body encode emit) [.pointer result] out (1200 * (n + 1) ^ 2 + 150) := by
  obtain ⟨sp,t1,bp,t2,pp,t3,arp,cl,c0,c1,c2,c3,hs,hb,hp,har,hcl⟩ := hc
  obtain ⟨base,a1,states,a2,block,a3,one,a4,two,zeroPtr,a0,ac1,ac2,ac3,ac4,
    _hbase,hS,hT,h1,h2,_hz⟩ := har
  let node : ScalarNodeCodec.Words n := ⟨false,anchor,anchor,ctx.box,ctx.parity⟩
  let ptrs : RegisterNodeDecode.Pointers := ⟨false,ap,ap,bp,pp⟩
  have hn : RegisterNodeDecode.At h ptrs node := ⟨rfl,ha,ha,hb,hp⟩
  obtain ⟨mid,dest,he,hm,hd,enc⟩ :=
    RegisterNodeEncode.compiled code arith harith hh node ptrs hn hS hT h1 h2
  obtain ⟨out,result,heout,ho,hresult,emitted⟩ := RegisterArcEmitter.compiled code hm
    (hs.mono he) hd (hcl.mono he) (hl.mono he)
  let r0 := initialRegisters [Value.pointer ap,.pointer cp,.pointer tail]
  let r1 := loadRegisters r0 3 4 15 (.pair sp t1)
  let r2 := loadRegisters r1 5 4 15 (.pair bp t2)
  let r3 := loadRegisters r2 6 4 15 (.pair pp t3)
  let r4 := loadRegisters r3 7 8 15 (.pair arp cl)
  let r5 := loadRegisters r4 14 4 15 (.pair base a1)
  let r6 := loadRegisters r5 9 4 15 (.pair states a2)
  let r7 := loadRegisters r6 10 4 15 (.pair block a3)
  let r8 := loadRegisters r7 11 4 15 (.pair one a4)
  let r9 := loadRegisters r8 12 14 15 (.pair two zeroPtr)
  have reads : Reads h r0 fields r9 := by
    refine .cons (by simp [r0,initialRegisters]) c0 ?_
    refine .cons (by simp [r1,loadRegisters,decoded]) c1 ?_
    refine .cons (by simp [r2,loadRegisters,decoded]) c2 ?_
    refine .cons (by simp [r3,loadRegisters,decoded]) c3 ?_
    refine .cons (by simp [r4,loadRegisters,decoded]) a0 ?_
    refine .cons (by simp [r5,loadRegisters,decoded]) ac1 ?_
    refine .cons (by simp [r6,loadRegisters,decoded]) ac2 ?_
    refine .cons (by simp [r7,loadRegisters,decoded]) ac3 ?_
    refine .cons (by simp [r8,loadRegisters,decoded]) ac4 (.nil _)
  let r10 := bindResults r9 [13] [Value.pointer dest]
  let r11 := bindResults r10 [14] [Value.pointer result]
  have last : Within code out r11 (.ret [.register 14]) [.pointer result] out 3 := by
    simpa [values,Atom.eval,r11,bindResults] using Within.ret code out r11 [.register 14]
  have emitArgs : values r10 [.register 3,.register 13,.register 8,.register 2] =
      [.pointer sp,.pointer dest,.pointer cl,.pointer tail] := by
    simp [values,Atom.eval,r10,r9,r8,r7,r6,r5,r4,r3,r2,r1,r0,bindResults,
      loadRegisters,decoded,initialRegisters]
  have emitCall := Within.call (procedure := emit)
    (arguments := [.register 3,.register 13,.register 8,.register 2]) (results := [14]) (regs := r10)
    (by simpa only [emitArgs,hemit] using emitted) last
  have encodeArgs : values r9 [.flag false,.register 0,.register 0,.register 5,.register 6,
      .register 9,.register 10,.register 11,.register 12] =
      ptrs.outputs ++ [.pointer states,.pointer block,.pointer one,.pointer two] := by
    simp [values,Atom.eval,r9,r8,r7,r6,r5,r4,r3,r2,r1,r0,loadRegisters,decoded,
      initialRegisters,ptrs,RegisterNodeDecode.Pointers.outputs]
  have encodeCall := Within.call (procedure := encode)
    (arguments := [.flag false,.register 0,.register 0,.register 5,.register 6,
      .register 9,.register 10,.register 11,.register 12]) (results := [13]) (regs := r9)
    (by simpa only [encodeArgs,hencode] using enc) emitCall
  refine ⟨out,result,he.trans heout,ho,hresult,?_⟩
  exact (reads.within encodeCall).mono (by simp [fields]; omega)

/-- Scan the explicitly represented anchor list with the fixed hub-entry body. -/
theorem scan_compiled (code : Code p) (scan item encode emit : Fin p)
    (arith : RegisterHorner.Procedures p) (harith : arith.Matches code)
    (hscan : code scan = RegisterListFlatMap.body scan item)
    (hitem : code item = body encode emit)
    (hencode : code encode = RegisterNodeEncode.encodeBody arith.mul arith.add)
    (hemit : code emit = RegisterArcEmitter.emitBody)
    {h : Heap} (hh : Valid h) {anchors cp tail : Ptr} {words : List (Bits n)}
    {ctx : Context n cbits} {entries : List (RawArc Ptr n cbits)}
    (ha : WordsAt h anchors words) (hc : ContextAt h cp ctx) (hl : TraceAt h tail entries) :
    ∃ out result, Extends h out ∧ Valid out ∧
      TraceAt out result (words.flatMap (fun a => [entry ctx a]) ++ entries) ∧
      Within code h (initialRegisters [.pointer anchors,.pointer cp,.pointer tail]) (code scan)
        [.pointer result] out ((1200 * (n + 1) ^ 2 + 177) * words.length + 13) := by
  have itemCompiled : ∀ {heap : Heap}, Valid heap →
      ∀ {ap cp tail : Ptr} {anchor : Bits n} {ctx : Context n cbits} {entries : List (RawArc Ptr n cbits)},
      BitsAt heap ap anchor → ContextAt heap cp ctx → TraceAt heap tail entries →
      ∃ out result, Extends heap out ∧ Valid out ∧
        TraceAt out result ([entry ctx anchor] ++ entries) ∧
        Within code heap (initialRegisters [.pointer ap,.pointer cp,.pointer tail]) (code item)
          [.pointer result] out (1200 * (n + 1) ^ 2 + 150) := by
    intro heap valid ap cp tail anchor ctx entries ha hc hl
    simpa only [hitem,List.singleton_append] using
      compiled code encode emit arith harith hencode hemit valid ha hc hl
  simpa only [Nat.add_assoc] using RegisterListFlatMap.compiled code scan item hscan
    (fun heap ptr (word : Bits n) => BitsAt heap ptr word)
    (fun heap ptr (ctx : Context n cbits) => ContextAt heap ptr ctx)
    (fun heap ptr (entries : List (RawArc Ptr n cbits)) => TraceAt heap ptr entries)
    (fun ext _ _ h => BitsAt.mono ext h) (fun ext _ _ h => ContextAt.mono ext h)
    (fun ctx anchor => [entry ctx anchor]) (1200 * (n + 1) ^ 2 + 150)
    (fun {heap} => itemCompiled (heap := heap)) hh ha hc hl

/-- Enumerate anchors from zero to the signed-state count, then emit their
hub-entry arcs. The arguments are zero, state count, one, context, and tail. -/
def rangeBody (range scan : Fin p) : Command p :=
  .call range [.register 0,.register 1,.register 2] [5]
    (.call scan [.register 5,.register 3,.register 4] [6] (.ret [.register 6]))

def rangeBudget (width states : ℕ) : ℕ :=
  RegisterWordRange.budget width states + (1200 * (width + 1) ^ 2 + 177) * states + 30

theorem range_compiled (code : Code p) (range scan item encode emit cmp : Fin p)
    (arith : RegisterHorner.Procedures p) (harith : arith.Matches code)
    (hrange : code range = RegisterWordRange.rangeBody range arith.add cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hscan : code scan = RegisterListFlatMap.body scan item)
    (hitem : code item = body encode emit)
    (hencode : code encode = RegisterNodeEncode.encodeBody arith.mul arith.add)
    (hemit : code emit = RegisterArcEmitter.emitBody)
    {h : Heap} (hh : Valid h) {zp sp op cp tail : Ptr}
    {ctx : Context n cbits} {entries : List (RawArc Ptr n cbits)}
    (hz : BitsAt h zp (Bits.zero n)) (hs : BitsAt h sp ctx.arithmetic.states)
    (ho : BitsAt h op ctx.arithmetic.one) (hone : ctx.arithmetic.one.value = 1)
    (hc : ContextAt h cp ctx) (hl : TraceAt h tail entries) :
    ∃ out result, ∃ words : List (Bits n), Extends h out ∧ Valid out ∧
      words.map Bits.value = List.range' 0 ctx.arithmetic.states.value ∧
      TraceAt out result (words.flatMap (fun a => [entry ctx a]) ++ entries) ∧
      Within code h (initialRegisters [.pointer zp,.pointer sp,.pointer op,.pointer cp,.pointer tail])
        (rangeBody range scan) [.pointer result] out (rangeBudget n ctx.arithmetic.states.value) := by
  have hadd := harith.2.2.2.2.2.2
  obtain ⟨mid,anchors,words,he,hm,hw,hvalues,enumerate⟩ :=
    RegisterWordRange.compiled code range arith.add cmp hrange hadd hcmp hh hz hs ho hone
  have hvalues' : words.map Bits.value = List.range' 0 ctx.arithmetic.states.value := by
    simpa only [Bits.value_zero,Nat.sub_zero] using hvalues
  have hlen : words.length = ctx.arithmetic.states.value := by
    have he := congrArg List.length hvalues'
    simpa using he
  obtain ⟨out,result,heout,hout,hresult,scanned⟩ := scan_compiled code scan item encode emit
    arith harith hscan hitem hencode hemit hm hw (hc.mono he) (hl.mono he)
  let r0 := initialRegisters [Value.pointer zp,.pointer sp,.pointer op,.pointer cp,.pointer tail]
  let r1 := bindResults r0 [5] [Value.pointer anchors]
  let r2 := bindResults r1 [6] [Value.pointer result]
  have last : Within code out r2 (.ret [.register 6]) [.pointer result] out 3 := by
    simpa [r2,bindResults,values,Atom.eval] using Within.ret code out r2 [.register 6]
  have scanArgs : values r1 [.register 5,.register 3,.register 4] =
      [.pointer anchors,.pointer cp,.pointer tail] := by
    simp [r1,r0,bindResults,initialRegisters,values,Atom.eval]
  have scanCall := Within.call (procedure := scan) (arguments := [.register 5,.register 3,.register 4])
    (results := [6]) (regs := r1) (by simpa only [scanArgs] using scanned) last
  have rangeArgs : values r0 [.register 0,.register 1,.register 2] =
      [.pointer zp,.pointer sp,.pointer op] := by
    simp [r0,initialRegisters,values,Atom.eval]
  have rangeCall := Within.call (procedure := range) (arguments := [.register 0,.register 1,.register 2])
    (results := [5]) (regs := r0) (by simpa only [rangeArgs] using enumerate) scanCall
  refine ⟨out,result,words,he.trans heout,hout,hvalues',hresult,?_⟩
  exact rangeCall.mono (by simp only [Bits.value_zero,Nat.sub_zero,hlen,rangeBudget,List.length_cons,List.length_nil]; omega)

end WeightedMIS.RegisterHubEntries
