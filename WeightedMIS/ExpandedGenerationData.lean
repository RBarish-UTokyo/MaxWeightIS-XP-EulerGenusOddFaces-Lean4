module

public import WeightedMIS.ExpandedContext
public import WeightedMIS.CompiledTemplatePrimitives

/-! # Shared stored input to the expanded-source enumerator -/

@[expose] public section

namespace WeightedMIS.ExpandedWords

open WeightedMIS.PointerMemory WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer

structure GenerationData (Row : Type*) (n cbits : ℕ) where
  arithmetic : ArithmeticWords n
  templates : List (CompiledTemplates.Template Row (ArcMetadata n cbits))
  shape : List (Bits n)
  weight : Bits cbits
  label : Ptr

/-- Three actual pair records reference arithmetic, templates, dimension shape,
and a shared connector-arc cost/label record. -/
def GenerationAt {Row : Type*} {n cbits : ℕ} (key : Walks.State Row → Bits n)
    (h : Heap) (p : Ptr) (data : GenerationData Row n cbits) : Prop :=
  ∃ ar t1 templates t2 shape cost,
    h[p]? = some (.pair ar t1) ∧ h[t1]? = some (.pair templates t2) ∧
    h[t2]? = some (.pair shape cost) ∧ ArithmeticAt h ar data.arithmetic ∧
    ListRep (CompiledTemplates.TemplateAt key MetadataAt) h templates data.templates ∧
    WordsAt h shape data.shape ∧ CostLabelAt h cost data.weight data.label ∧
    ∀ a ∈ data.templates, a.metadata.deltas.length = data.shape.length

theorem GenerationAt.mono {Row : Type*} {n cbits : ℕ} {key : Walks.State Row → Bits n}
    {h h' : Heap} (he : Extends h h') {p : Ptr} {data : GenerationData Row n cbits}
    (hg : GenerationAt key h p data) : GenerationAt key h' p data := by
  obtain ⟨ar,t1,templates,t2,shape,cost,h0,h1,h2,har,ht,hs,hc,hlen⟩ := hg
  refine ⟨ar,t1,templates,t2,shape,cost,he.lookup h0,he.lookup h1,he.lookup h2,
    har.mono he,?_,hs.mono he,hc.mono he,hlen⟩
  exact ht.mono he (fun _ _ ht => CompiledTemplates.TemplateAt.mono (metaAt := MetadataAt)
    (fun he hm => MetadataAt.mono he hm) he ht)

end WeightedMIS.ExpandedWords
