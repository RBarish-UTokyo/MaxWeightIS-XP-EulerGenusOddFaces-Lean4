module

public import WeightedMIS.ExpandedGenerationData
public import WeightedMIS.RegisterContextPack

/-! # Packing shared enumeration data without copying its stored arrays -/

@[expose] public section

namespace WeightedMIS.RegisterGenerationPack

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.EfficientSearch.Pointer WeightedMIS.RegisterContextPack

variable {p n cbits : ℕ} {Row : Type*}

def body : Command p :=
  .allocate 4 (.pair (.register 2) (.register 3))
    (.allocate 4 (.pair (.register 1) (.register 4))
      (.allocate 4 (.pair (.register 0) (.register 4)) (.ret [.register 4])))

theorem compiled (code : Code p) {h : Heap} (hh : Valid h)
    {key : Walks.State Row → Bits n} {data : GenerationData Row n cbits}
    {arp tp sp cp : Ptr} (ha : ArithmeticAt h arp data.arithmetic)
    (ht : ListRep (CompiledTemplates.TemplateAt key MetadataAt) h tp data.templates)
    (hs : WordsAt h sp data.shape) (hc : CostLabelAt h cp data.weight data.label)
    (hlen : ∀ a ∈ data.templates, a.metadata.deltas.length = data.shape.length) :
    ∃ out q, Extends h out ∧ Valid out ∧ GenerationAt key out q data ∧
      Within code h (initialRegisters [.pointer arp,.pointer tp,.pointer sp,.pointer cp]) body
        [.pointer q] out 27 := by
  have harp : arp < h.length := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hcell,_⟩ := ha
    exact List.getElem?_eq_some_iff.mp hcell |>.1
  let h1 := h ++ [.pair sp cp]
  have s1 := safe_pair hh hs.allocated hc.allocated
  let h2 := h1 ++ [.pair tp h.length]
  have s2 := safe_pair s1.2 (ht.allocated.trans_le s1.1.length_le)
    (show h.length < h1.length by simp [h1])
  have e2 : Extends h h2 := s1.1.trans s2.1
  let h3 := h2 ++ [.pair arp h1.length]
  have s3 := safe_pair s2.2 (harp.trans_le e2.length_le)
    (show h1.length < h2.length by simp [h2])
  have e3 : Extends h h3 := e2.trans s3.1
  refine ⟨h3,h2.length,e3,s3.2,?_,?_⟩
  · refine ⟨arp,h1.length,tp,h.length,sp,cp,last_cell h2 _,
      s3.1.lookup (last_cell h1 _),(s2.1.trans s3.1).lookup (last_cell h _),
      ha.mono e3,?_,hs.mono e3,hc.mono e3,hlen⟩
    exact ht.mono e3 (fun _ _ ht => CompiledTemplates.TemplateAt.mono (metaAt := MetadataAt)
      (fun he ht => MetadataAt.mono he ht) e3 ht)
  · unfold body
    apply Within.allocate (budget := 19) (c := .pair sp cp)
    · simp [CellExpr.eval,Atom.eval,initialRegisters,Value.asPointer]
    · apply Within.allocate (budget := 11) (c := .pair tp h.length)
      · simp [CellExpr.eval,Atom.eval,initialRegisters,Value.asPointer]
      · apply Within.allocate (budget := 3) (c := .pair arp h1.length)
        · simp [CellExpr.eval,Atom.eval,initialRegisters,Value.asPointer,h1]
        · simpa [values,Atom.eval,h1,h2,h3,List.append_assoc] using
            Within.ret code h3 (Function.update (Function.update (Function.update
              (initialRegisters [.pointer arp,.pointer tp,.pointer sp,.pointer cp])
                4 (.pointer h.length)) 4 (.pointer h1.length)) 4 (.pointer h2.length)) [.register 4]

end WeightedMIS.RegisterGenerationPack
