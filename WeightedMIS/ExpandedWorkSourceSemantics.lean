module

public import WeightedMIS.ExpandedCandidateSemantics
public import WeightedMIS.RegisterWorkSource

/-! # Exact outgoing-list semantics of the compiled working-source generator -/

@[expose] public section

namespace WeightedMIS.ExpandedWords

open WeightedMIS.EfficientSearch WeightedMIS.SparseSearchGraph WeightedMIS.NodeEncoding
open WeightedMIS.Expanded WeightedMIS.SearchConstruction WeightedMIS.PointerMemory WeightedMIS.Walks

/-- The hub branch of the node encoder ignores the two signed-state fields. -/
theorem encode_hub_word {width r d radius : ℕ} (ar : ArithmeticWords width)
    (ha : ArithmeticRepresents ar r d radius) (anchorWord currentWord boxWord parityWord : Bits width)
    (z : Box (Fin d) radius) (parity : ZMod 2)
    (hbox : boxWord.value = (boxEquiv d radius z).val) (hparity : parityWord.value = parity.val)
    (hcap : nodeCount r d radius ≤ 2 ^ width) :
    ScalarNodeCodec.encodeWords ar.states ar.block ar.one ar.two
      ⟨true, anchorWord, currentWord, boxWord, parityWord⟩ =
        encodeBits width (nodeEquiv r d radius (.hub z parity)).val := by
  have he : ScalarNodeCodec.encode ar.states.value ar.block.value
      (ScalarNodeCodec.Words.values ⟨true, anchorWord, currentWord, boxWord, parityWord⟩) =
      (nodeEquiv r d radius (.hub z parity)).val := by
    simp [ScalarNodeCodec.encode, ScalarNodeCodec.Words.values, hbox, hparity,
      ScalarNodeCodec.nodeEquiv_hub]
  have hfit := (nodeEquiv r d radius (.hub z parity)).isLt.trans_le hcap
  apply bits_value_injective
  rw [ScalarNodeCodec.encodeWords_exact _ _ _ _ _ ha.2.2.2.1 ha.2.2.2.2
    (by rw [he]; exact hfit), he]
  exact (encodeBits_value _ _ hfit).symm

/-- Actual scalar node fields decode to the working context used by candidates. -/
theorem work_context_represents {width cbits r d radius : ℕ}
    (data : GenerationData (Fin r) width cbits) (source anchorWord currentWord boxWord parityWord : Bits width)
    (anchor current : State (Fin r)) (z : Box (Fin d) radius) (parity : ZMod 2)
    (ha : ArithmeticRepresents data.arithmetic r d radius) (hlen : data.shape.length = d)
    (hanchor : anchorWord.value = (stateEquiv r anchor).val)
    (hcurrent : currentWord.value = (stateEquiv r current).val)
    (hbox : boxWord.value = (boxEquiv d radius z).val) (hparity : parityWord.value = parity.val) :
    ContextRepresents (RegisterWorkSource.context data source anchorWord currentWord boxWord parityWord)
      anchor current z parity := by
  refine ⟨hanchor, hcurrent, hparity, ?_, ha⟩
  change RegisterDigits.decodeWords data.arithmetic.base data.shape.length boxWord = _
  rw [hlen]
  exact decodeWords_box_or_empty _ _ _ ha.1 hbox

/-- The optional exit is present exactly at the anchor and targets the actual
hub with the unchanged box and parity. -/
theorem exit_arcs_eq {width cbits r d radius : ℕ} (ar : ArithmeticWords width)
    (ha : ArithmeticRepresents ar r d radius) (source anchorWord currentWord boxWord parityWord : Bits width)
    (anchor current : State (Fin r)) (z : Box (Fin d) radius) (parity : ZMod 2)
    (weight : Bits cbits) (label : Ptr)
    (hanchor : anchorWord.value = (stateEquiv r anchor).val)
    (hcurrent : currentWord.value = (stateEquiv r current).val)
    (hbox : boxWord.value = (boxEquiv d radius z).val) (hparity : parityWord.value = parity.val)
    (hcap : nodeCount r d radius ≤ 2 ^ width) :
    RegisterExit.arcs ar source anchorWord currentWord boxWord parityWord weight label =
      if current = anchor then
        [(source, ⟨encodeBits width (nodeEquiv r d radius (.hub z parity)).val, weight, label⟩)]
      else [] := by
  have hc : (Bits.compare currentWord anchorWord).1 = .eq ↔ current = anchor := by
    rw [(Bits.compare_correct _ _).2.1, hcurrent, hanchor]
    exact ⟨fun h => (stateEquiv r).injective (Fin.ext h), fun h => by rw [h]⟩
  unfold RegisterExit.arcs
  by_cases he : current = anchor
  · rw [if_pos (hc.mpr he), if_pos he,
      encode_hub_word ar ha anchorWord currentWord boxWord parityWord z parity hbox hparity hcap]
  · rw [if_neg (mt hc.mp he), if_neg he]

/-- Every list entry produced by the compiled working-source routine is exactly
an outgoing arc of the actual expanded graph, in the same order and with the
same original edge or connector metadata. -/
theorem work_arcs_eq_outgoing {width cbits r m d radius : ℕ}
    (key : State (Fin r) → Bits width) (hkey : ∀ v, (key v).value = (stateEquiv r v).val)
    (C : Fin m → Column (Fin r)) (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2)
    (data : GenerationData (Fin r) width cbits) (metadata : Fin m → ArcMetadata width cbits)
    (weight : Option (Fin m) → Bits cbits) (label : Option (Fin m) → Ptr)
    (deltas : Fin m → Fin d → SignedWord width)
    (htemplates : data.templates = (signedArcs C).map (fun a =>
      ⟨Walks.source C a, target C a, metadata a.val.1⟩))
    (hdeltas : ∀ e, (metadata e).deltas = List.ofFn (deltas e))
    (hdelta : ∀ e i, (deltas e i).value = W e i)
    (hmetaParity : ∀ e, (if (metadata e).parity then 1 else 0 : ZMod 2) = π e)
    (hmetaWeight : ∀ e, (metadata e).weight = weight (some e))
    (hmetaLabel : ∀ e, (metadata e).label = label (some e))
    (hweight : data.weight = weight none) (hlabel : data.label = label none)
    (source anchorWord currentWord boxWord parityWord : Bits width)
    (anchor current : State (Fin r)) (z : Box (Fin d) radius) (parity : ZMod 2)
    (ha : ArithmeticRepresents data.arithmetic r d radius) (hlen : data.shape.length = d)
    (hanchor : anchorWord.value = (stateEquiv r anchor).val)
    (hcurrent : currentWord.value = (stateEquiv r current).val)
    (hbox : boxWord.value = (boxEquiv d radius z).val) (hparity : parityWord.value = parity.val)
    (hcap : nodeCount r d radius ≤ 2 ^ width) :
    RegisterWorkSource.arcs key data source anchorWord currentWord boxWord parityWord =
      (SearchConstruction.outgoing C W π radius (.work anchor current z parity)).map (fun x =>
        (source, ⟨encodeBits width (nodeEquiv r d radius x.2).val, weight x.1, label x.1⟩)) := by
  have hctx := work_context_represents data source anchorWord currentWord boxWord parityWord
    anchor current z parity ha hlen hanchor hcurrent hbox hparity
  have hcand (a : Walks.Arc C) :
      candidate key (RegisterWorkSource.context data source anchorWord currentWord boxWord parityWord)
        ⟨Walks.source C a, target C a, metadata a.val.1⟩ =
      (moveCandidate C W π radius anchor current z parity a).toList.map (fun x =>
        (source, ⟨encodeBits width (nodeEquiv r d radius x.2).val, weight x.1, label x.1⟩)) := by
    rw [candidate_eq_moveCandidate key hkey C W π anchor current z parity _ hctx a _
      (deltas a.val.1) (hdeltas _) (hdelta _) (hmetaParity _) hcap]
    simp only [RegisterWorkSource.context]
    unfold moveCandidate
    split
    · cases updateBox radius z (W a.val.1) <;> simp [hmetaWeight, hmetaLabel]
    · rfl
  unfold RegisterWorkSource.arcs
  rw [exit_arcs_eq data.arithmetic ha source anchorWord currentWord boxWord parityWord
    anchor current z parity data.weight data.label hanchor hcurrent hbox hparity hcap]
  simp only [SearchConstruction.outgoing, List.map_append, htemplates, List.flatMap_map]
  congr 1
  · by_cases he : current = anchor <;> simp [he, hweight, hlabel]
  · rw [List.filterMap_eq_flatMap_toList, List.map_flatMap]
    exact List.flatMap_congr (fun a _ => hcand a)

end WeightedMIS.ExpandedWords
