module

public import WeightedMIS.RegisterAllSources

/-! # Uniform finite-code composition of the expanded raw-arc enumerator -/

@[expose] public section

namespace WeightedMIS.RegisterGraphEnumeration

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.EfficientSearch.Pointer

variable {p n cbits : ℕ} {Row : Type*}

structure Procedures (p : ℕ) where
  work : RegisterWorkSource.Procedures p
  moves : RegisterCandidate.Procedures p
  arithmetic : RegisterHorner.Procedures p
  division : RegisterDivision.Procedures p
  digit : Fin p
  complement : Fin p
  quotRem : Fin p
  nodeDecode : Fin p
  hubPack : Fin p
  hubRange : Fin p
  range : Fin p
  hubScan : Fin p
  hubItem : Fin p
  hubSource : Fin p
  workSource : Fin p
  source : Fin p
  scan : Fin p

structure Procedures.Matches (ids : Procedures p) (code : Code p) : Prop where
  work : ids.work.Matches code ids.moves ids.arithmetic ids.digit ids.complement ids.division
  quotRem : code ids.quotRem = RegisterQuotRem.body ids.division.divide
  nodeDecode : code ids.nodeDecode = RegisterNodeDecode.decodeBody ids.quotRem ids.division.cmp ids.division.sub
  hubPack : code ids.hubPack = RegisterHubSource.packBody
  hubRange : code ids.hubRange = RegisterHubEntries.rangeBody ids.range ids.hubScan
  range : code ids.range = RegisterWordRange.rangeBody ids.range ids.arithmetic.add ids.moves.compare
  hubScan : code ids.hubScan = RegisterListFlatMap.body ids.hubScan ids.hubItem
  hubItem : code ids.hubItem = RegisterHubEntries.body ids.moves.encode ids.moves.emit
  hubSource : code ids.hubSource = RegisterHubSource.hubSourceBody ids.hubPack ids.hubRange
  workSource : code ids.workSource = RegisterWorkSource.body ids.work
  source : code ids.source = RegisterSourceDispatch.body ids.nodeDecode ids.hubSource ids.workSource
  scan : code ids.scan = RegisterListFlatMap.body ids.scan ids.source

def sourceBudget (n d m s : ℕ) : ℕ :=
  1600*(n+1)^2 + (RegisterHubEntries.rangeBudget n s+150) + RegisterWorkSource.budget n d m + 100

def budget (n d m s total : ℕ) : ℕ :=
  200*(n+1)*(total+1)+(sourceBudget n d m s+27)*total+30

def outgoing (key : Walks.State Row → Bits n) (data : GenerationData Row n cbits) (source : Bits n) :
    List (RawArc Ptr n cbits) := RegisterSourceDispatch.arcs RegisterHubSource.arcs key data source

def entries (key : Walks.State Row → Bits n) (data : GenerationData Row n cbits) (limit : Bits n) :
    List (RawArc Ptr n cbits) := (RegisterAllSources.sourceWords limit).flatMap (outgoing key data)

theorem source_compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    {key : Walks.State Row → Bits n} {data : GenerationData Row n cbits} {h : Heap} (hh : Valid h)
    {sp dp acc : Ptr} {source : Bits n} {tail : List (RawArc Ptr n cbits)}
    (hs : BitsAt h sp source) (hg : GenerationAt key h dp data)
    (hone : data.arithmetic.one.value = 1) (ht : TraceAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (outgoing key data source ++ tail) ∧
      Within code h (initialRegisters [.pointer sp,.pointer dp,.pointer acc]) (code ids.source)
        [.pointer q] out (sourceBudget n data.shape.length data.templates.length data.arithmetic.states.value) := by
  have hubCompiled : ∀ {h : Heap}, Valid h → ∀ {key : Walks.State Row → Bits n}
      {data : GenerationData Row n cbits} {source box parity : Bits n} {sp bp pp dp acc : Ptr}
      {tail : List (RawArc Ptr n cbits)},
      BitsAt h sp source → BitsAt h bp box → BitsAt h pp parity → GenerationAt key h dp data →
      data.arithmetic.one.value = 1 → TraceAt h acc tail →
      ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (RegisterHubSource.arcs data source box parity ++ tail) ∧
        Within code h (initialRegisters [.pointer sp,.pointer bp,.pointer pp,.pointer dp,.pointer acc])
          (code ids.hubSource) [.pointer q] out (RegisterHubEntries.rangeBudget n data.arithmetic.states.value+150) := by
    intro heap valid key data source box parity sp bp pp dp acc tail hs hb hp hd hone ht
    obtain ⟨out,q,he,ho,hq,run⟩ := RegisterHubSource.compiled code ids.hubPack ids.hubRange ids.range ids.hubScan ids.hubItem
      ids.moves.encode ids.moves.emit ids.moves.compare ids.arithmetic hc.work.moveCode.arithmetic
      hc.hubPack hc.hubRange hc.range hc.work.moveCode.compare hc.hubScan hc.hubItem
      hc.work.moveCode.encode hc.work.moveCode.emit valid hs hb hp hd hone ht
    exact ⟨out,q,he,ho,hq,by simpa only [hc.hubSource] using run⟩
  obtain ⟨out,q,he,ho,hq,run⟩ := RegisterSourceDispatch.compiled code ids.nodeDecode ids.hubSource ids.workSource ids.quotRem
    ids.work ids.moves ids.arithmetic ids.digit ids.complement ids.division hc.workSource hc.work hc.nodeDecode hc.quotRem
    RegisterHubSource.arcs (fun data => RegisterHubEntries.rangeBudget n data.arithmetic.states.value+150)
    hubCompiled hh hs hg hone ht
  exact ⟨out,q,he,ho,hq,by simpa only [hc.source,sourceBudget] using run⟩

/-- Every arithmetic operation, loop branch, pointer read and allocation is an
execution of the specified finite table. No finite-type enumerator is an
instruction: all source IDs are generated by the compiled binary range loop. -/
theorem compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    {key : Walks.State Row → Bits n} {data : GenerationData Row n cbits} {h : Heap} (hh : Valid h)
    {dp lp zp op acc : Ptr} {limit one : Bits n} {tail : List (RawArc Ptr n cbits)}
    (hg : GenerationAt key h dp data) (hl : BitsAt h lp limit) (hz : BitsAt h zp (Bits.zero n))
    (ho : BitsAt h op one) (hone : one.value = 1) (hdataOne : data.arithmetic.one.value = 1)
    (ht : TraceAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (entries key data limit ++ tail) ∧
      Within code h (initialRegisters [.pointer dp,.pointer lp,.pointer zp,.pointer op,.pointer acc])
        (RegisterAllSources.body ids.range ids.scan) [.pointer q] out
          (budget n data.shape.length data.templates.length data.arithmetic.states.value limit.value) := by
  apply RegisterAllSources.compiled code ids.range ids.scan ids.source ids.arithmetic.add ids.moves.compare
    hc.range hc.scan hc.work.moveCode.arithmetic.2.2.2.2.2.2 hc.work.moveCode.compare
    key data (outgoing key data) (sourceBudget n data.shape.length data.templates.length data.arithmetic.states.value)
  · intro heap valid sp dp acc word tail hw hd ht
    exact source_compiled code ids hc valid hw hd hdataOne ht
  · exact hh
  · exact hg
  · exact hl
  · exact hz
  · exact ho
  · exact hone
  · exact ht

end WeightedMIS.RegisterGraphEnumeration
