module

public import WeightedMIS.ExpandedWorkSourceSemantics
public import WeightedMIS.RegisterHubSource

/-! # Exact outgoing-list semantics of the compiled hub-source generator -/

@[expose] public section

namespace WeightedMIS.ExpandedWords

open WeightedMIS.EfficientSearch WeightedMIS.SparseSearchGraph WeightedMIS.NodeEncoding
open WeightedMIS.Expanded WeightedMIS.SearchConstruction WeightedMIS.PointerMemory WeightedMIS.Walks

@[simp] theorem stateEquiv_none_value (r : ℕ) : (stateEquiv r none).val = 0 := by
  simp [stateEquiv]

@[simp] theorem stateEquiv_some_value {r : ℕ} (v : Fin r) (b : Bool) :
    (stateEquiv r (some (v, b))).val = 2 * v.val + (if b then 1 else 0) + 1 := by
  cases b <;> simp [stateEquiv, boolEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- The signed-state list is ordered by its actual numeric codec. -/
theorem signedStates_values (r : ℕ) :
    (signedStates r).map (fun v => (stateEquiv r v).val) = List.range (2 * r + 1) := by
  have hp (r : ℕ) :
      (List.finRange r).flatMap (fun v => [2 * v.val + 1, 2 * v.val + 2]) =
        (List.range (2 * r)).map (· + 1) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
      simp only [Function.comp_def, Fin.val_castSucc, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, Fin.val_last]
      rw [ih]
      have he : 2 * (r + 1) = 2 * r + 2 := by omega
      rw [he, List.range_add, List.map_append, List.map_map]
      simp [List.range_succ, Nat.add_assoc]
  simp only [signedStates, List.map_cons, stateEquiv_none_value, List.map_flatMap,
    List.map_cons, List.map_nil, stateEquiv_some_value, Bool.false_eq_true,
    ↓reduceIte, Nat.add_zero]
  change 0 :: (List.finRange r).flatMap (fun v => [2 * v.val + 1, 2 * v.val + 2]) = _
  rw [hp]
  exact List.range_succ_eq_map.symm

/-- The actual finite counter produces the keys of all signed states in the
same order as the mathematical graph's outgoing list. -/
theorem hub_anchors_eq {width cbits r d radius : ℕ}
    (data : GenerationData (Fin r) width cbits) (ha : ArithmeticRepresents data.arithmetic r d radius) :
    RegisterHubSource.anchors data =
      (signedStates r).map (fun a => encodeBits width (stateEquiv r a).val) := by
  unfold RegisterHubSource.anchors
  rw [ha.2.1, ← signedStates_values r, List.map_map]
  rfl

/-- The closed hub counter and node arithmetic emit exactly every actual hub
entry, with the connector weight and label shared unchanged. -/
theorem hub_arcs_eq_outgoing {width cbits r m d radius : ℕ}
    (C : Fin m → Column (Fin r)) (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2)
    (data : GenerationData (Fin r) width cbits)
    (weight : Option (Fin m) → Bits cbits) (label : Option (Fin m) → Ptr)
    (hweight : data.weight = weight none) (hlabel : data.label = label none)
    (source boxWord parityWord : Bits width) (z : Box (Fin d) radius) (parity : ZMod 2)
    (ha : ArithmeticRepresents data.arithmetic r d radius)
    (hbox : boxWord.value = (boxEquiv d radius z).val) (hparity : parityWord.value = parity.val)
    (hcap : nodeCount r d radius ≤ 2 ^ width) :
    RegisterHubSource.arcs data source boxWord parityWord =
      (SearchConstruction.outgoing C W π radius (.hub z parity)).map (fun x =>
        (source, ⟨encodeBits width (nodeEquiv r d radius x.2).val, weight x.1, label x.1⟩)) := by
  unfold RegisterHubSource.arcs
  rw [hub_anchors_eq data ha]
  simp only [List.flatMap_map, SearchConstruction.outgoing, List.map_map]
  rw [← List.map_eq_flatMap]
  apply List.map_congr_left
  intro a _
  have hfit : (stateEquiv r a).val < 2 ^ width := by
    have hs : 2 * r + 1 < 2 ^ width := by
      rw [← ha.2.1]
      exact Bits.value_lt data.arithmetic.states
    exact (stateEquiv r a).isLt.trans hs
  have he := encode_target_word data.arithmetic ha
    (encodeBits width (stateEquiv r a).val) (encodeBits width (stateEquiv r a).val)
    boxWord parityWord a a z parity (encodeBits_value _ _ hfit)
    (encodeBits_value _ _ hfit) hbox hparity hcap
  simp only [Function.comp_def, RegisterHubEntries.entry, RegisterHubSource.context, hweight, hlabel]
  rw [he]

end WeightedMIS.ExpandedWords
