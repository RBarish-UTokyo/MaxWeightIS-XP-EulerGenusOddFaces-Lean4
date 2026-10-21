module

public import WeightedMIS.RegisterGenerationPack
public import WeightedMIS.ExpandedEnumerationSize
public import WeightedMIS.CompiledTemplateSemantics
public import WeightedMIS.CompiledGraphConstruction

/-! # Finite sparse-column input to an actual expanded adjacency trie -/

@[expose] public section

namespace WeightedMIS.SparseGraphConstruction

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.EfficientSearch.Pointer WeightedMIS.Walks

variable {p r m n cbits : ℕ}

def data (C : Fin m → Column (Fin r)) (metadata : Fin m → ArcMetadata n cbits)
    (arithmetic : ArithmeticWords n) (shape : List (Bits n)) (weight : Bits cbits) (label : Ptr) :
    GenerationData (Fin r) n cbits :=
  ⟨arithmetic,(SearchConstruction.signedArcs C).map (fun a =>
    ⟨source C a,target C a,metadata a.val.1⟩),shape,weight,label⟩

/-- Arguments: edge records, hub key, arithmetic, dimension shape, connector
cost/label record, node-count word, zero word, one word. -/
def body (templates pack enumerate graph : Fin p) : Command p :=
  .call templates [.register 0,.register 1,.null] [9]
    (.call pack [.register 2,.register 9,.register 3,.register 4] [10]
      (.call enumerate [.register 10,.register 5,.register 6,.register 7,.null] [11]
        (.call graph [.register 11,.null] [12] (.ret [.register 12]))))

def budget (m n d t s total : ℕ) : ℕ :=
  186*m + RegisterGraphEnumeration.budget n d t s total +
    (80*n+135)*(total*(s+t+1)) + 100

theorem compiled (code : Code p) (ids : RegisterGraphEnumeration.Procedures p) (hc : ids.Matches code)
    (templates column stub emit pack enumerate graph insert : Fin p)
    (htemplates : code templates = CompiledTemplates.listBody templates column)
    (hcolumn : code column = CompiledTemplates.columnBody stub emit)
    (hstub : code stub = CompiledTemplates.stubBody) (hemit : code emit = CompiledTemplates.emitBody)
    (hpack : code pack = RegisterGenerationPack.body)
    (henumerate : code enumerate = RegisterAllSources.body ids.range ids.scan)
    (hgraph : code graph = CompiledGraphConstruction.graphBody graph insert)
    (hinsert : code insert = CompiledTrie.insertBody insert)
    (key : State (Fin r) → Bits n) (C : Fin m → Column (Fin r)) (metadata : Fin m → ArcMetadata n cbits)
    {h : Heap} (hh : Valid h) {input hub arp shapePtr cost lp zp op : Ptr} {pointers : List Ptr}
    {arithmetic : ArithmeticWords n} {shape : List (Bits n)} {weight : Bits cbits} {label : Ptr}
    {limit one : Bits n}
    (hl : ListAt h input pointers)
    (hedges : List.Forall₂ (CompiledTemplates.EdgeAt key MetadataAt h) pointers (CompiledTemplates.edgeEntries C metadata))
    (hhub : BitsAt h hub (key none)) (har : ArithmeticAt h arp arithmetic) (hshape : WordsAt h shapePtr shape)
    (hcost : CostLabelAt h cost weight label) (hlimit : BitsAt h lp limit) (hzero : BitsAt h zp (Bits.zero n))
    (honeWord : BitsAt h op one) (hone : one.value = 1) (harOne : arithmetic.one.value = 1)
    (hdim : ∀ e, (metadata e).deltas.length = shape.length) :
    let gd := data C metadata arithmetic shape weight label
    ∃ out q, Extends h out ∧ Valid out ∧ GraphAt out q (Radix.fromEntries (RegisterGraphEnumeration.entries key gd limit)) ∧
      Within code h (initialRegisters [.pointer input,.pointer hub,.pointer arp,.pointer shapePtr,
        .pointer cost,.pointer lp,.pointer zp,.pointer op]) (body templates pack enumerate graph) [.pointer q] out
          (budget m n shape.length gd.templates.length arithmetic.states.value limit.value) := by
  dsimp only
  let gd := data C metadata arithmetic shape weight label
  obtain ⟨tp,h1,templateRun,v1,e1,ht⟩ := CompiledTemplates.compiled_signed_arcs code templates column stub emit
    htemplates hcolumn hstub hemit key C metadata hh hl hedges hhub
  have hdim' : ∀ a ∈ gd.templates, a.metadata.deltas.length = gd.shape.length := by
    intro a ha
    obtain ⟨arc,_,rfl⟩ := List.mem_map.mp ha
    exact hdim arc.val.1
  obtain ⟨h2,dp,e2,v2,hg,packRun⟩ := RegisterGenerationPack.compiled code v1 (data := gd)
    (har.mono e1) ht (hshape.mono e1) (hcost.mono e1) hdim'
  have e02 := e1.trans e2
  have empty : TraceAt h2 0 ([] : List (RawArc Ptr n cbits)) := ⟨[],.nil v2.1,.nil⟩
  obtain ⟨h3,raw,e3,v3,hraw,enumerationRun⟩ := RegisterGraphEnumeration.compiled code ids hc v2 hg
    (hlimit.mono e02) (hzero.mono e02) (honeWord.mono e02) hone harOne empty
  have hraw' : TraceAt h3 raw (RegisterGraphEnumeration.entries key gd limit) := by simpa using hraw
  obtain ⟨q,out,graphRun,vo,e4,hgraphAt⟩ := CompiledGraphConstruction.compiled code graph insert hgraph hinsert v3 hraw'
  refine ⟨out,q,((e1.trans e2).trans e3).trans e4,vo,hgraphAt,?_⟩
  let r0 := initialRegisters [Value.pointer input,.pointer hub,.pointer arp,.pointer shapePtr,
    .pointer cost,.pointer lp,.pointer zp,.pointer op]
  let r1 := bindResults r0 [9] [.pointer tp]
  let r2 := bindResults r1 [10] [.pointer dp]
  let r3 := bindResults r2 [11] [.pointer raw]
  let r4 := bindResults r3 [12] [.pointer q]
  have ret : Within code out r4 (.ret [.register 12]) [.pointer q] out 3 := by
    simpa [values,Atom.eval,r4,bindResults] using Within.ret code out r4 [.register 12]
  have graphArgs : values r3 [.register 11,.null] = [.pointer raw,.pointer 0] := by
    simp [values,Atom.eval,r3,bindResults]
  have graphCall := Within.call (procedure := graph) (arguments := [.register 11,.null])
    (results := [12]) (regs := r3) (by simpa only [graphArgs] using graphRun) ret
  have enumerationArgs : values r2 [.register 10,.register 5,.register 6,.register 7,.null] =
      [.pointer dp,.pointer lp,.pointer zp,.pointer op,.pointer 0] := by
    simp [values,Atom.eval,r2,r1,r0,bindResults,initialRegisters]
  have enumerationCall := Within.call (procedure := enumerate)
    (arguments := [.register 10,.register 5,.register 6,.register 7,.null]) (results := [11]) (regs := r2)
    (by simpa only [enumerationArgs,henumerate] using enumerationRun) graphCall
  have packArgs : values r1 [.register 2,.register 9,.register 3,.register 4] =
      [.pointer arp,.pointer tp,.pointer shapePtr,.pointer cost] := by
    simp [values,Atom.eval,r1,r0,bindResults,initialRegisters]
  have packCall := Within.call (procedure := pack) (arguments := [.register 2,.register 9,.register 3,.register 4])
    (results := [10]) (regs := r1) (by simpa only [packArgs,hpack] using packRun) enumerationCall
  have templateArgs : values r0 [.register 0,.register 1,.null] = [.pointer input,.pointer hub,.pointer 0] := by
    simp [values,Atom.eval,r0,initialRegisters]
  have templateCall := Within.call (procedure := templates) (arguments := [.register 0,.register 1,.null])
    (results := [9]) (regs := r0) (by simpa only [templateArgs] using templateRun) packCall
  have hlen := RegisterGraphEnumeration.entries_length_le key gd limit
  have hcostBound := Nat.mul_le_mul_left (80*n+135) hlen
  have hgd : gd = data C metadata arithmetic shape weight label := rfl
  simp only [hgd, data] at hcostBound templateCall ⊢
  exact templateCall.mono (by simp only [List.length_cons,List.length_nil,budget]; omega)

end WeightedMIS.SparseGraphConstruction
