module

public import WeightedMIS.ExpandedCoordinate
public import WeightedMIS.CompiledTemplates
public import WeightedMIS.EfficientSearchPointerData

/-! # Shared records used by the finite expanded-graph generator -/

@[expose] public section

namespace WeightedMIS.ExpandedWords

open WeightedMIS.PointerMemory WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer

structure ArcMetadata (vbits cbits : ℕ) where
  deltas : List (SignedWord vbits)
  parity : Bool
  weight : Bits cbits
  label : Ptr

def CostLabelAt {cbits : ℕ} (h : Heap) (p : Ptr) (weight : Bits cbits) (label : Ptr) : Prop :=
  ∃ wp, h[p]? = some (.pair wp label) ∧ BitsAt h wp weight ∧ label < h.length

def MetadataAt {vbits cbits : ℕ} (h : Heap) (p : Ptr) (a : ArcMetadata vbits cbits) : Prop :=
  ∃ deltas parity costLabel, h[p]? = some (.pair deltas parity) ∧
    h[parity]? = some (.bit a.parity costLabel) ∧
    DeltasAt h deltas a.deltas ∧ CostLabelAt h costLabel a.weight a.label

theorem CostLabelAt.allocated {cbits : ℕ} {h : Heap} {p : Ptr} {w : Bits cbits} {l : Ptr}
    (hc : CostLabelAt h p w l) : p < h.length := by
  obtain ⟨_, hp, _⟩ := hc
  exact List.getElem?_eq_some_iff.mp hp |>.1

theorem CostLabelAt.mono {cbits : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr}
    {w : Bits cbits} {l : Ptr} (hc : CostLabelAt h p w l) : CostLabelAt h' p w l := by
  obtain ⟨wp, hp, hw, hl⟩ := hc
  exact ⟨wp, he.lookup hp, hw.mono he, lt_of_lt_of_le hl he.length_le⟩

theorem MetadataAt.allocated {vbits cbits : ℕ} {h : Heap} {p : Ptr} {a : ArcMetadata vbits cbits}
    (hc : MetadataAt h p a) : p < h.length := by
  obtain ⟨_, _, _, hp, _⟩ := hc
  exact List.getElem?_eq_some_iff.mp hp |>.1

theorem MetadataAt.mono {vbits cbits : ℕ} {h h' : Heap} (he : Extends h h') {p : Ptr}
    {a : ArcMetadata vbits cbits} (hc : MetadataAt h p a) : MetadataAt h' p a := by
  obtain ⟨dp, pp, cp, hp, hparity, hd, hcost⟩ := hc
  exact ⟨dp, pp, cp, he.lookup hp, he.lookup hparity, hd.mono he, hcost.mono he⟩

end WeightedMIS.ExpandedWords
