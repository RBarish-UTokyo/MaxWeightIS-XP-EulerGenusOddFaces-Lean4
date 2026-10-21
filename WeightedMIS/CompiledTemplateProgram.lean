module

public import WeightedMIS.CompiledTemplateSemantics

/-! # A concrete four-procedure signed-column preprocessor -/

@[expose] public section

namespace WeightedMIS.CompiledTemplates

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.Walks WeightedMIS.ExpandedWords WeightedMIS.SearchConstruction

/-- A single fixed table of four finite register bodies: emit, read a stub,
convert one column, and convert the input edge list. -/
def program : Code 4 := ![emitBody, stubBody, columnBody 1 0, listBody 3 2]

/-- The fixed program emits the exact signed-arc list from represented input. -/
theorem program_correct {r m vbits cbits : ℕ}
    (key : State (Fin r) → Bits vbits) (C : Fin m → Column (Fin r))
    (metadata : Fin m → ArcMetadata vbits cbits)
    {h : Heap} (hh : Valid h) {input hub : Ptr} {pointers : List Ptr}
    (listAt : ListAt h input pointers)
    (entriesAt : List.Forall₂ (EdgeAt key MetadataAt h) pointers (edgeEntries C metadata))
    (hubAt : BitsAt h hub (key none)) :
    ∃ out final, Within program h (initialRegisters [.pointer input, .pointer hub, .pointer 0])
      (program 3) [.pointer out] final (186 * m + 13) ∧
      Valid final ∧ Extends h final ∧
      TemplatesAt key MetadataAt final out ((signedArcs C).map (fun a =>
        ⟨source C a, target C a, metadata a.val.1⟩)) :=
  compiled_signed_arcs program 3 2 1 0 rfl rfl rfl rfl key C metadata hh listAt entriesAt hubAt

/-- The actual machine run includes all heap events and concrete sixteen-word
caller saves/restores; its bit cost is linear in the edge count times the
allocated-address width. -/
theorem program_bit_cost {r m vbits cbits : ℕ}
    (key : State (Fin r) → Bits vbits) (C : Fin m → Column (Fin r))
    (metadata : Fin m → ArcMetadata vbits cbits)
    {h : Heap} (hh : Valid h) {input hub : Ptr} {pointers : List Ptr}
    (listAt : ListAt h input pointers)
    (entriesAt : List.Forall₂ (EdgeAt key MetadataAt h) pointers (edgeEntries C metadata))
    (hubAt : BitsAt h hub (key none)) :
    ∃ out final events tree,
      FramedExec program h (initialRegisters [.pointer input, .pointer hub, .pointer 0])
        (program 3) ⟨[.pointer out], final, events⟩ tree ∧
      events.length ≤ 186 * m + 13 ∧
      (∀ stack, StackExec h stack tree.compile final stack) ∧
      stackBitCost tree.compile ≤
        (186 * m + 13) * (102 + 35 * (h.length + (186 * m + 13)).size) ∧
      TemplatesAt key MetadataAt final out ((signedArcs C).map (fun a =>
        ⟨source C a, target C a, metadata a.val.1⟩)) := by
  obtain ⟨out, final, ⟨events, he, bound⟩, _, _, result⟩ :=
    program_correct key C metadata hh listAt entriesAt hubAt
  have hargs : ValuesBound h.length [.pointer input, .pointer hub, .pointer 0] := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact listAt.allocated
    · exact hubAt.allocated
    · exact null_allocated hh
  have hr := initialRegisters_bounded (null_allocated hh) hargs
  obtain ⟨tree, framed⟩ := he.framed
  exact ⟨out, final, events, tree, framed, bound, framed.stack_exec,
    framed.bitCost_le_of_length_le hh hr bound, result⟩

end WeightedMIS.CompiledTemplates
