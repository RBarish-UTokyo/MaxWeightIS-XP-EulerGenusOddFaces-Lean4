module

public import WeightedMIS.SparseGraphConstruction
public import WeightedMIS.RegisterMachineFrames

/-! # One fixed sparse-column-to-adjacency-trie register program -/

@[expose] public section

namespace WeightedMIS.SparseConstructionProgram

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.EfficientSearch.Pointer WeightedMIS.Walks

/-- The procedure table is independent of graph size, genus and word width. -/
def arithmetic : RegisterHorner.Procedures 41 := ⟨0,1,2,3,4,5,6⟩
def division : RegisterDivision.Procedures 41 := ⟨2,7,8,4,5,9,10,6,11⟩
def moves : RegisterCandidate.Procedures 41 := ⟨7,15,0,9,16,17⟩
def work : RegisterWorkSource.Procedures 41 := ⟨20,21,19,18,22⟩
def procedures : RegisterGraphEnumeration.Procedures 41 :=
  ⟨work,moves,arithmetic,division,14,10,12,13,24,28,27,26,25,29,23,30,31⟩

def program : Code 41 := fun i => match i.val with
  | 0 => RegisterHorner.hornerBody 0 1 6
  | 1 => RegisterMultiplier.multiplyBody 2 3
  | 2 => RegisterZero.zeroBody 2
  | 3 => RegisterMultiplier.multiplyAccBody 3 4 6
  | 4 => RegisterShift.shiftInBody 5
  | 5 => RegisterShift.snocBody 5
  | 6 => RegisterAdder.adderBody 6
  | 7 => RegisterComparator.comparatorBody 7
  | 8 => RegisterDivision.auxBody 8 4 7 9
  | 9 => RegisterSubtractor.subtractorBody 10 6
  | 10 => RegisterComplement.complementBody 10
  | 11 => RegisterDivision.divideBody 2 7 8
  | 12 => RegisterQuotRem.body 11
  | 13 => RegisterNodeDecode.decodeBody 12 7 9
  | 14 => RegisterCoordinate.digitBody 6 7 9
  | 15 => RegisterCoordinates.wordsBody 15 14
  | 16 => RegisterNodeEncode.encodeBody 1 6
  | 17 => RegisterArcEmitter.emitBody
  | 18 => RegisterCandidate.candidateBody moves
  | 19 => RegisterListFlatMap.body 19 18
  | 20 => RegisterDigits.decodeBody 20 11
  | 21 => RegisterContextPack.body
  | 22 => RegisterExit.body 7 16 17
  | 23 => RegisterWorkSource.body work
  | 24 => RegisterHubSource.packBody
  | 25 => RegisterHubEntries.body 16 17
  | 26 => RegisterListFlatMap.body 26 25
  | 27 => RegisterWordRange.rangeBody 27 6 7
  | 28 => RegisterHubEntries.rangeBody 27 26
  | 29 => RegisterHubSource.hubSourceBody 24 28
  | 30 => RegisterSourceDispatch.body 13 29 23
  | 31 => RegisterListFlatMap.body 31 30
  | 32 => RegisterAllSources.body 27 31
  | 33 => CompiledTemplates.emitBody
  | 34 => CompiledTemplates.stubBody
  | 35 => CompiledTemplates.columnBody 34 33
  | 36 => CompiledTemplates.listBody 36 35
  | 37 => RegisterGenerationPack.body
  | 38 => CompiledTrie.insertBody 38
  | 39 => CompiledGraphConstruction.graphBody 39 38
  | _ => SparseGraphConstruction.body 36 37 32 39

theorem program_matches : procedures.Matches program := by
  refine ⟨?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  refine ⟨?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · exact ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Entry point 40 computes templates, enumerates actual outgoing arcs, and
constructs the radix adjacency graph, all within this same fixed finite table. -/
theorem correct {r m n cbits : ℕ}
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
    let gd := SparseGraphConstruction.data C metadata arithmetic shape weight label
    ∃ out q, Extends h out ∧ Valid out ∧ GraphAt out q (Radix.fromEntries (RegisterGraphEnumeration.entries key gd limit)) ∧
      Within program h (initialRegisters [.pointer input,.pointer hub,.pointer arp,.pointer shapePtr,
        .pointer cost,.pointer lp,.pointer zp,.pointer op]) (program 40) [.pointer q] out
          (SparseGraphConstruction.budget m n shape.length gd.templates.length arithmetic.states.value limit.value) :=
  SparseGraphConstruction.compiled program procedures program_matches 36 35 34 33 37 32 39 38
    rfl rfl rfl rfl rfl rfl rfl rfl key C metadata hh hl hedges hhub har hshape hcost hlimit hzero honeWord hone harOne hdim

/-- Full pointer-address and saved-register-stack bit cost of the fixed graph
construction program, with the exact generated adjacency trie as its result. -/
theorem bit_cost {r m n cbits : ℕ}
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
    let gd := SparseGraphConstruction.data C metadata arithmetic shape weight label
    let steps := SparseGraphConstruction.budget m n shape.length gd.templates.length arithmetic.states.value limit.value
    ∃ out q events tree,
      FramedExec program h (initialRegisters [.pointer input,.pointer hub,.pointer arp,.pointer shapePtr,
        .pointer cost,.pointer lp,.pointer zp,.pointer op]) (program 40) ⟨[.pointer q],out,events⟩ tree ∧
      events.length ≤ steps ∧ (∀ stack, StackExec h stack tree.compile out stack) ∧
      stackBitCost tree.compile ≤ steps*(102+35*(h.length+steps).size) ∧
      GraphAt out q (Radix.fromEntries (RegisterGraphEnumeration.entries key gd limit)) := by
  dsimp only
  obtain ⟨out,q,he,vo,hq,events,run,hlen⟩ := correct key C metadata hh hl hedges hhub har hshape hcost hlimit hzero honeWord hone harOne hdim
  have harp : arp < h.length := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hcell,_⟩ := har
    exact List.getElem?_eq_some_iff.mp hcell |>.1
  have hargs : ValuesBound h.length [.pointer input,.pointer hub,.pointer arp,.pointer shapePtr,
      .pointer cost,.pointer lp,.pointer zp,.pointer op] := by
    intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hl.allocated
    · exact hhub.allocated
    · exact harp
    · exact hshape.allocated
    · exact hcost.allocated
    · exact hlimit.allocated
    · exact hzero.allocated
    · exact honeWord.allocated
  have hr := initialRegisters_bounded (null_allocated hh) hargs
  obtain ⟨tree,framed⟩ := run.framed
  exact ⟨out,q,events,tree,framed,hlen,framed.stack_exec,
    framed.bitCost_le_of_length_le hh hr hlen,hq⟩

end WeightedMIS.SparseConstructionProgram
