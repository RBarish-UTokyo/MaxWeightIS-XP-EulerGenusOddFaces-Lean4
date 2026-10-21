module

public import WeightedMIS.RegisterGraphEnumeration

/-! # Bounds for the lists actually emitted by finite enumeration -/

@[expose] public section

namespace WeightedMIS.RegisterGraphEnumeration

open WeightedMIS.EfficientSearch WeightedMIS.ExpandedWords WeightedMIS.PointerMemory

variable {Row : Type*} {n cbits : ℕ}

theorem flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β) (bound : ℕ)
    (hf : ∀ x, (f x).length ≤ bound) : (xs.flatMap f).length ≤ xs.length*bound := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons,List.length_append,List.length_cons]; have := hf x; nlinarith

theorem candidate_length_le (key : Walks.State Row → Bits n) (ctx : WorkContext n)
    (a : CompiledTemplates.Template Row (ArcMetadata n cbits)) : (candidate key ctx a).length ≤ 1 := by
  unfold candidate
  split
  · split <;> simp
  · simp

theorem outgoing_length_le (key : Walks.State Row → Bits n) (data : GenerationData Row n cbits)
    (source : Bits n) : (outgoing key data source).length ≤
      data.arithmetic.states.value + data.templates.length + 1 := by
  unfold outgoing RegisterSourceDispatch.arcs
  dsimp only
  split
  · simp [RegisterHubSource.arcs,RegisterHubSource.anchors,Function.comp_def]; omega
  · simp only [RegisterWorkSource.arcs,List.length_append]
    have ht := flatMap_length_le data.templates (candidate key
      (RegisterWorkSource.context data source (RegisterSourceDispatch.node data source).anchor
        (RegisterSourceDispatch.node data source).current (RegisterSourceDispatch.node data source).box
        (RegisterSourceDispatch.node data source).parity)) 1 (candidate_length_le _ _)
    have he : (RegisterExit.arcs data.arithmetic source (RegisterSourceDispatch.node data source).anchor
        (RegisterSourceDispatch.node data source).current (RegisterSourceDispatch.node data source).box
        (RegisterSourceDispatch.node data source).parity data.weight data.label).length ≤ 1 := by
      unfold RegisterExit.arcs
      split <;> simp
    omega

theorem entries_length_le (key : Walks.State Row → Bits n) (data : GenerationData Row n cbits)
    (limit : Bits n) : (entries key data limit).length ≤
      limit.value * (data.arithmetic.states.value + data.templates.length + 1) := by
  have hf := flatMap_length_le (RegisterAllSources.sourceWords limit) (outgoing key data)
    (data.arithmetic.states.value+data.templates.length+1) (outgoing_length_le key data)
  simpa only [entries,RegisterAllSources.sourceWords,List.length_map,List.length_range'] using hf

end WeightedMIS.RegisterGraphEnumeration
