module

public import WeightedMIS.ExpandedHubSourceSemantics
public import WeightedMIS.RegisterGraphEnumeration
public import WeightedMIS.WordNodeCodec
public import WeightedMIS.SparseSearchLabeled

/-!
# Exact semantics of the decoded-source enumeration

The compiled enumerator decodes every binary source identifier below the node
count, dispatches to the hub or working-source generator, and concatenates the
results in increasing identifier order. This file identifies that list with the
encoded outgoing lists of the expanded graph, and at the canonical vertex and
cost widths with `SparseSearchGraph.Labeled.entries`.
-/

@[expose] public section

namespace WeightedMIS.ExpandedWords

open WeightedMIS.EfficientSearch WeightedMIS.SparseSearchGraph WeightedMIS.NodeEncoding
open WeightedMIS.Expanded WeightedMIS.SearchConstruction WeightedMIS.PointerMemory WeightedMIS.Walks

/-- The stored-input hypotheses shared by every source of the enumerator. -/
structure SourceInterface {width cbits r m d : ℕ} (radius : ℕ)
    (key : State (Fin r) → Bits width)
    (C : Fin m → Column (Fin r)) (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2)
    (data : GenerationData (Fin r) width cbits)
    (weight : Option (Fin m) → Bits cbits) (label : Option (Fin m) → Ptr)
    (metadata : Fin m → ArcMetadata width cbits) (deltas : Fin m → Fin d → SignedWord width) :
    Prop where
  key : ∀ v, (key v).value = (stateEquiv r v).val
  templates : data.templates = (signedArcs C).map (fun a =>
    ⟨Walks.source C a, target C a, metadata a.val.1⟩)
  deltaList : ∀ e, (metadata e).deltas = List.ofFn (deltas e)
  delta : ∀ e i, (deltas e i).value = W e i
  parity : ∀ e, (if (metadata e).parity then 1 else 0 : ZMod 2) = π e
  edgeWeight : ∀ e, (metadata e).weight = weight (some e)
  edgeLabel : ∀ e, (metadata e).label = label (some e)
  connectorWeight : data.weight = weight none
  connectorLabel : data.label = label none
  arithmetic : ArithmeticRepresents data.arithmetic r d radius
  shape : data.shape.length = d
  capacity : nodeCount r d radius ≤ 2 ^ width

/-- Encode one numbered outgoing entry at an arbitrary vertex width. -/
def rawEntry {width cbits r m d radius : ℕ} (weight : Option (Fin m) → Bits cbits)
    (label : Option (Fin m) → Ptr) (s : Fin (nodeCount r d radius))
    (e : Option (Fin m) × Fin (nodeCount r d radius)) : RawArc Ptr width cbits :=
  (encodeBits width s.val, ⟨encodeBits width e.2.val, weight e.1, label e.1⟩)

/-- The decoded fields of an actual numbered source. -/
theorem node_values {width cbits r d radius : ℕ} (data : GenerationData (Fin r) width cbits)
    (ha : ArithmeticRepresents data.arithmetic r d radius)
    (hcap : nodeCount r d radius ≤ 2 ^ width) (s : Fin (nodeCount r d radius)) :
    (RegisterSourceDispatch.node data (encodeBits width s.val)).values =
      ScalarNodeCodec.coordinates ((nodeEquiv r d radius).symm s) := by
  apply ScalarNodeCodec.decodeWords_node _ _ _ _ _ _ _ ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2
  rw [Equiv.apply_symm_apply]
  exact encodeBits_value _ _ (s.isLt.trans_le hcap)

/-- The outer decoded-source dispatch emits exactly the encoded outgoing list
of the numbered source node, in order and with the supplied labels. -/
theorem source_arcs_eq {width cbits r m d radius : ℕ}
    {key : State (Fin r) → Bits width}
    {C : Fin m → Column (Fin r)} {W : Fin m → Fin d → ℤ} {π : Fin m → ZMod 2}
    {data : GenerationData (Fin r) width cbits}
    {weight : Option (Fin m) → Bits cbits} {label : Option (Fin m) → Ptr}
    {metadata : Fin m → ArcMetadata width cbits} {deltas : Fin m → Fin d → SignedWord width}
    (hi : SourceInterface radius key C W π data weight label metadata deltas)
    (s : Fin (nodeCount r d radius)) :
    RegisterGraphEnumeration.outgoing key data (encodeBits width s.val) =
      (encodedOutgoing C W π radius s).map (rawEntry weight label s) := by
  have hv := node_values data hi.arithmetic hi.capacity s
  have hmap : ∀ x : Option (Fin m) × Node (Fin r) (Fin d) radius,
      rawEntry (width := width) weight label s (x.1, nodeEquiv r d radius x.2) =
        (encodeBits width s.val, ⟨encodeBits width (nodeEquiv r d radius x.2).val,
          weight x.1, label x.1⟩) := fun _ => rfl
  unfold RegisterGraphEnumeration.outgoing RegisterSourceDispatch.arcs encodedOutgoing
  dsimp only
  rw [List.map_map]
  generalize hnode : (nodeEquiv r d radius).symm s = node at hv
  generalize hout : RegisterSourceDispatch.node data (encodeBits width s.val) = out at hv
  cases node with
  | hub z parity =>
    simp only [ScalarNodeCodec.coordinates, ScalarNodeCodec.Words.values,
      ScalarNodeCodec.Coordinates.mk.injEq] at hv
    obtain ⟨hhub, -, -, hbox, hparity⟩ := hv
    simp only [hhub, ↓reduceIte]
    rw [hub_arcs_eq_outgoing C W π data weight label hi.connectorWeight
      hi.connectorLabel _ _ _ z parity hi.arithmetic hbox hparity hi.capacity]
    exact List.map_congr_left (fun x _ => (hmap x).symm)
  | work a v z parity =>
    simp only [ScalarNodeCodec.coordinates, ScalarNodeCodec.Words.values,
      ScalarNodeCodec.Coordinates.mk.injEq] at hv
    obtain ⟨hhub, hanchor, hcurrent, hbox, hparity⟩ := hv
    simp only [hhub, Bool.false_eq_true, ↓reduceIte]
    rw [work_arcs_eq_outgoing key hi.key C W π data metadata
      weight label deltas hi.templates hi.deltaList hi.delta hi.parity hi.edgeWeight
      hi.edgeLabel hi.connectorWeight hi.connectorLabel _ _ _ _ _ a v z parity hi.arithmetic
      hi.shape hanchor hcurrent hbox hparity hi.capacity]
    exact List.map_congr_left (fun x _ => (hmap x).symm)

theorem range'_eq_finRange (N : ℕ) : List.range' 0 N = (List.finRange N).map Fin.val := by
  rw [← List.range_eq_range', List.map_coe_finRange_eq_range]

/-- The complete compiled enumeration list is the source-ordered concatenation
of all encoded outgoing lists. -/
theorem entries_eq {width cbits r m d radius : ℕ}
    {key : State (Fin r) → Bits width}
    {C : Fin m → Column (Fin r)} {W : Fin m → Fin d → ℤ} {π : Fin m → ZMod 2}
    {data : GenerationData (Fin r) width cbits}
    {weight : Option (Fin m) → Bits cbits} {label : Option (Fin m) → Ptr}
    {metadata : Fin m → ArcMetadata width cbits} {deltas : Fin m → Fin d → SignedWord width}
    (hi : SourceInterface radius key C W π data weight label metadata deltas)
    (limit : Bits width) (hlimit : limit.value = nodeCount r d radius) :
    RegisterGraphEnumeration.entries key data limit =
      (List.finRange (nodeCount r d radius)).flatMap fun s =>
        (encodedOutgoing C W π radius s).map (rawEntry weight label s) := by
  unfold RegisterGraphEnumeration.entries RegisterAllSources.sourceWords
  rw [hlimit, range'_eq_finRange, List.map_map, List.flatMap_map]
  exact List.flatMap_congr (fun s _ => source_arcs_eq hi s)

/-- At the canonical vertex and cost widths, with stored weights equal to the
encoded label values, the compiled list is exactly the labeled sparse list. -/
theorem entries_eq_labeled {r m d radius : ℕ} (w : Fin m → ℕ)
    {key : State (Fin r) → Bits (vertexWidth r d radius)}
    {C : Fin m → Column (Fin r)} {W : Fin m → Fin d → ℤ} {π : Fin m → ZMod 2}
    {data : GenerationData (Fin r) (vertexWidth r d radius) (costWidth r d radius w)}
    {label : Option (Fin m) → Ptr}
    {metadata : Fin m → ArcMetadata (vertexWidth r d radius) (costWidth r d radius w)}
    {deltas : Fin m → Fin d → SignedWord (vertexWidth r d radius)}
    (hi : SourceInterface radius key C W π data
      (fun l => encodeBits (costWidth r d radius w) (labelValue w l)) label metadata deltas)
    (limit : Bits (vertexWidth r d radius)) (hlimit : limit.value = nodeCount r d radius) :
    RegisterGraphEnumeration.entries key data limit = Labeled.entries label C W π radius w := by
  rw [entries_eq hi limit hlimit]
  rfl

/-- The canonical vertex width satisfies the capacity premise. -/
theorem capacity_vertexWidth (r d radius : ℕ) :
    nodeCount r d radius ≤ 2 ^ vertexWidth r d radius :=
  (Nat.lt_size_self _).le

end WeightedMIS.ExpandedWords
