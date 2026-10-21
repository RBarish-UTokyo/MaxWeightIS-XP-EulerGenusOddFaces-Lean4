module

public import WeightedMIS.ExpandedCoordinateSemantics

/-!
# Empty signature dimensions need no stored box base

When there are no signature coordinates, division, updates, and Horner
encoding never inspect the base word. Thus vertex words need not hold the
irrelevant number 4m+1 when the expanded graph has constant-size signatures.
-/

@[expose] public section

namespace WeightedMIS.ExpandedWords

open WeightedMIS.EfficientSearch WeightedMIS.NodeEncoding WeightedMIS.Expanded
open WeightedMIS.RegisterDigits WeightedMIS.RegisterHorner WeightedMIS.SearchConstruction

theorem decodeWords_box_or_empty {width d radius : ℕ} (base value : Bits width)
    (z : Box (Fin d) radius) (hb : d = 0 ∨ base.value = 4 * radius + 1)
    (hv : value.value = (boxEquiv d radius z).val) :
    decodeWords base d value = boxWords width z := by
  rcases hb with rfl | hb
  · simp [decodeWords, boxWords]
  · exact decodeWords_box base value z hb hv

theorem encodeWords_box_or_empty {width d radius : ℕ} (base : Bits width)
    (z : Box (Fin d) radius) (hb : d = 0 ∨ base.value = 4 * radius + 1)
    (hcap : (4 * radius + 1) ^ d ≤ 2 ^ width) :
    (encodeWords base (boxWords width z)).value = (boxEquiv d radius z).val := by
  rcases hb with rfl | hb
  · simp [encodeWords, boxWords, boxEquiv, finFunctionFinEquiv_apply, Bits.value_zero]
  · exact encodeWords_box base z hb hcap

theorem updateWords_box_or_empty {width d radius : ℕ} (base : Bits width)
    (z : Box (Fin d) radius) (deltas : Fin d → SignedWord width) (delta : Fin d → ℤ)
    (hb : d = 0 ∨ base.value = 4 * radius + 1) (hd : ∀ i, (deltas i).value = delta i) :
    updateWords base (boxWords width z) (List.ofFn deltas) =
      (updateBox radius z delta).map (boxWords width) := by
  rcases hb with rfl | hb
  · simp [updateWords, boxWords, updateBox]
  · exact updateWords_box base z deltas delta hb hd

/-- The full positional update remains exact without a representable base
when the actual signature dimension is zero. -/
theorem decode_update_encode_box_or_empty {width d radius : ℕ} (base value : Bits width)
    (z : Box (Fin d) radius) (deltas : Fin d → SignedWord width) (delta : Fin d → ℤ)
    (hb : d = 0 ∨ base.value = 4 * radius + 1) (hv : value.value = (boxEquiv d radius z).val)
    (hd : ∀ i, (deltas i).value = delta i) (hcap : (4 * radius + 1) ^ d ≤ 2 ^ width) :
    ((updateWords base (decodeWords base d value) (List.ofFn deltas)).map
      (fun ws => (encodeWords base ws).value)) =
      (updateBox radius z delta).map (fun z' => (boxEquiv d radius z').val) := by
  rw [decodeWords_box_or_empty base value z hb hv,
    updateWords_box_or_empty base z deltas delta hb hd]
  rw [Option.map_map]
  congr 1
  funext z'
  exact encodeWords_box_or_empty base z' hb hcap

end WeightedMIS.ExpandedWords
