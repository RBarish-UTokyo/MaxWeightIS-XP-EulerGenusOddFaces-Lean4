module

public import WeightedMIS.CompiledTemplatePrimitives

/-! # Representation-preserving finite template insertion -/

@[expose] public section

namespace WeightedMIS.CompiledTemplates

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.Walks

variable {p : ℕ} {Row Metadata : Type*} {width : ℕ}
    {key : State Row → Bits width} {metaAt : Heap → Ptr → Metadata → Prop}

/-- A represented list of the actual immutable source/target/metadata records. -/
def TemplatesAt (key : State Row → Bits width) (metaAt : Heap → Ptr → Metadata → Prop)
    (h : Heap) (ptr : Ptr) (as : List (Template Row Metadata)) : Prop :=
  ∃ ptrs, ListAt h ptr ptrs ∧ List.Forall₂ (TemplateAt key metaAt h) ptrs as

theorem TemplatesAt.mono
    (mono : ∀ {h h' ptr a}, Extends h h' → metaAt h ptr a → metaAt h' ptr a)
    {h h' : Heap} (ext : Extends h h') {ptr as} (ht : TemplatesAt key metaAt h ptr as) :
    TemplatesAt key metaAt h' ptr as := by
  obtain ⟨ptrs, hl, hr⟩ := ht
  exact ⟨ptrs, hl.mono ext, hr.imp (fun _ _ ha => TemplateAt.mono (metaAt := metaAt) mono ext ha)⟩

theorem TemplatesAt.allocated {h : Heap} {ptr as}
    (ht : TemplatesAt key metaAt h ptr as) : ptr < h.length := by
  obtain ⟨_, hl, _⟩ := ht
  exact hl.allocated

/-- The three allocations emit a single actual template and share the old tail. -/
theorem emit_compiled (code : Code p)
    (mono : ∀ {h h' ptr a}, Extends h h' → metaAt h ptr a → metaAt h' ptr a)
    {h : Heap} (hh : Valid h) {source target mp tail : Ptr}
    {a : Template Row Metadata} {as : List (Template Row Metadata)}
    (hs : BitsAt h source (key a.source)) (ht : BitsAt h target (key a.target))
    (hm : metaAt h mp a.metadata) (hmalloc : mp < h.length)
    (hl : TemplatesAt key metaAt h tail as) :
    ∃ out final, Within code h (initialRegisters [.pointer source, .pointer target,
        .pointer mp, .pointer tail]) emitBody [.pointer out] final 27 ∧
      Valid final ∧ Extends h final ∧ TemplatesAt key metaAt final out (a :: as) := by
  obtain ⟨ptrs, list, records⟩ := hl
  obtain ⟨valid, ext, outlist, record⟩ := emit_refines (metaAt := metaAt) mono hh hs ht hm hmalloc list
  refine ⟨h.length + 2, emittedHeap h source target mp tail, ?_, valid, ext, ?_⟩
  · exact emit_within code h _ source target mp tail (by simp [initialRegisters])
      (by simp [initialRegisters]) (by simp [initialRegisters]) (by simp [initialRegisters])
  · exact ⟨_, outlist, .cons record (records.imp (fun _ _ ha => TemplateAt.mono (metaAt := metaAt) mono ext ha))⟩

end WeightedMIS.CompiledTemplates
