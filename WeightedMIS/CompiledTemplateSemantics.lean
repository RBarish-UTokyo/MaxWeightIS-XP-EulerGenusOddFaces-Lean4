module

public import WeightedMIS.CompiledTemplateList
public import WeightedMIS.ExpandedRecords
public import WeightedMIS.SearchConstruction

/-! # Exact signed-arc semantics of the finite template preprocessor -/

@[expose] public section

namespace WeightedMIS.CompiledTemplates

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.Walks WeightedMIS.ExpandedWords WeightedMIS.SearchConstruction

/-- The explicit original-edge list supplied to the finite preprocessor. -/
def edgeEntries {r m : ℕ} {Metadata : Type*}
    (C : Fin m → Column (Fin r)) (metadata : Fin m → Metadata) : List (Column (Fin r) × Metadata) :=
  (List.finRange m).map (fun e => (C e, metadata e))

@[simp] theorem edgeEntries_length {r m : ℕ} {Metadata : Type*}
    (C : Fin m → Column (Fin r)) (metadata : Fin m → Metadata) :
    (edgeEntries C metadata).length = m := by simp [edgeEntries]

/-- The output is exactly the genuine signed arcs used in the expanded graph,
including their original label's shared metadata and all coincident arcs. -/
theorem allTemplates_edgeEntries {r m : ℕ} {Metadata : Type*}
    (C : Fin m → Column (Fin r)) (metadata : Fin m → Metadata) :
    allTemplates (edgeEntries C metadata) = (signedArcs C).map (fun a =>
      (⟨source C a, target C a, metadata a.val.1⟩ : Template (Fin r) Metadata)) := by
  simp only [allTemplates, edgeEntries, List.flatMap_map, signedArcs, List.map_flatMap]
  apply List.flatMap_congr
  intro e he
  split_ifs with hz
  · simp [hz, templates, source, target]
  · simp only [List.map_cons, List.map_nil, source, target]
    cases hc : C e <;> simp_all [templates]

/-- Instantiation with the actual shared signature/parity/cost/label records. -/
theorem compiled_signed_arcs {p r m vbits cbits : ℕ} (code : Code p)
    (self column stub emit : Fin p)
    (listCode : code self = listBody self column)
    (columnCode : code column = columnBody stub emit)
    (stubCode : code stub = stubBody) (emitCode : code emit = emitBody)
    (key : State (Fin r) → Bits vbits) (C : Fin m → Column (Fin r))
    (metadata : Fin m → ArcMetadata vbits cbits)
    {h : Heap} (hh : Valid h) {input hub : Ptr} {pointers : List Ptr}
    (listAt : ListAt h input pointers)
    (entriesAt : List.Forall₂ (EdgeAt key MetadataAt h) pointers (edgeEntries C metadata))
    (hubAt : BitsAt h hub (key none)) :
    ∃ out final, Within code h (initialRegisters [.pointer input, .pointer hub, .pointer 0])
      (code self) [.pointer out] final (186 * m + 13) ∧
      Valid final ∧ Extends h final ∧
      TemplatesAt key MetadataAt final out ((signedArcs C).map (fun a =>
        ⟨source C a, target C a, metadata a.val.1⟩)) := by
  simpa [edgeEntries_length, allTemplates_edgeEntries] using
    (list_compiled (metaAt := MetadataAt) code self column stub emit
      listCode columnCode stubCode emitCode (fun ext ha => MetadataAt.mono ext ha)
      hh listAt entriesAt hubAt)

end WeightedMIS.CompiledTemplates
