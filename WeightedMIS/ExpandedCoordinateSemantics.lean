module

public import WeightedMIS.ExpandedWordEncoding
public import WeightedMIS.ExpandedCoordinate

/-! # Binary signature updates agree exactly with the expanded graph -/

@[expose] public section

namespace WeightedMIS.ExpandedWords

open WeightedMIS.EfficientSearch WeightedMIS.SparseSearchGraph WeightedMIS.NodeEncoding
open WeightedMIS.Expanded WeightedMIS.RegisterDigits WeightedMIS.RegisterHorner
open WeightedMIS.SearchConstruction

/-- Success of the actual binary update is exactly the signed range check. -/
theorem updateDigit_isSome_iff {width : ℕ} (base digit : Bits width) (delta : SignedWord width)
    (hd : digit.value < base.value) :
    (updateDigit base digit delta).isSome = true ↔
      0 ≤ (digit.value : ℤ) + delta.value ∧ (digit.value : ℤ) + delta.value < base.value := by
  have hs := updateDigit_spec base digit delta hd
  cases hu : updateDigit base digit delta <;>
    by_cases hr : 0 ≤ (digit.value : ℤ) + delta.value ∧ (digit.value : ℤ) + delta.value < base.value <;>
    simp_all

/-- The actual returned binary word is uniquely characterized by integer
addition and the valid half-open coordinate range. -/
theorem updateDigit_eq_some_iff {width : ℕ} (base digit out : Bits width)
    (delta : SignedWord width) (hd : digit.value < base.value) :
    updateDigit base digit delta = some out ↔
      (out.value : ℤ) = (digit.value : ℤ) + delta.value ∧ out.value < base.value := by
  have hs := updateDigit_spec base digit delta hd
  constructor
  · intro he
    have hr := (updateDigit_isSome_iff base digit delta hd).mp (by simp [he])
    rw [he, if_pos hr] at hs
    have hv : (out.value : ℤ) = (digit.value : ℤ) + delta.value := Option.some.inj hs
    exact ⟨hv, by omega⟩
  · rintro ⟨hv, hlt⟩
    have hr : 0 ≤ (digit.value : ℤ) + delta.value ∧
        (digit.value : ℤ) + delta.value < base.value := by omega
    rw [if_pos hr] at hs
    cases he : updateDigit base digit delta with
    | none => simp [he] at hs
    | some w =>
      rw [he] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      congr 1
      apply bits_value_injective
      omega

/-- A list update succeeds exactly when each coordinate update succeeds. -/
theorem updateWords_isSome_ofFn {width d : ℕ} (base : Bits width)
    (digits : Fin d → Bits width) (deltas : Fin d → SignedWord width) :
    (updateWords base (List.ofFn digits) (List.ofFn deltas)).isSome = true ↔
      ∀ i, (updateDigit base (digits i) (deltas i)).isSome = true := by
  induction d with
  | zero => simp [updateWords]
  | succ d ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    rw [Fin.forall_fin_succ]
    rw [← ih (fun i => digits i.succ) (fun i => deltas i.succ)]
    cases h : updateDigit base (digits 0) (deltas 0) <;>
      cases ht : updateWords base (List.ofFn fun i => digits i.succ)
        (List.ofFn fun i => deltas i.succ) <;> simp [updateWords, h, ht]

/-- Coordinatewise actual binary outputs determine the complete emitted list. -/
theorem updateWords_ofFn {width d : ℕ} (base : Bits width)
    (digits out : Fin d → Bits width) (deltas : Fin d → SignedWord width)
    (h : ∀ i, updateDigit base (digits i) (deltas i) = some (out i)) :
    updateWords base (List.ofFn digits) (List.ofFn deltas) = some (List.ofFn out) := by
  induction d with
  | zero => simp [updateWords]
  | succ d ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
    simp only [updateWords, h 0, Option.bind_some]
    rw [ih (fun i => digits i.succ) (fun i => out i.succ)
      (fun i => deltas i.succ) (fun i => h i.succ)]
    rfl

/-- Shifted unsigned digits have the same range predicate as their actual
integer coordinates in the symmetric signature box. -/
theorem coordinate_range_iff {d radius : ℕ} (z : Box (Fin d) radius)
    (delta : Fin d → ℤ) (i : Fin d) :
    (0 ≤ ((z i).val : ℤ) + delta i ∧ ((z i).val : ℤ) + delta i < 4 * radius + 1) ↔
      |coordinate z i + delta i| ≤ 2 * (radius : ℤ) := by
  rw [abs_le]
  simp only [coordinate]
  omega

/-- Binary signed-magnitude updates on the decoded coordinate list agree
exactly with the genuine bounded signature transition. -/
theorem updateWords_box {width d radius : ℕ} (base : Bits width)
    (z : Box (Fin d) radius) (deltas : Fin d → SignedWord width) (delta : Fin d → ℤ)
    (hb : base.value = 4 * radius + 1) (hd : ∀ i, (deltas i).value = delta i) :
    updateWords base (boxWords width z) (List.ofFn deltas) =
      (updateBox radius z delta).map (boxWords width) := by
  have hwidth : 4 * radius + 1 < 2 ^ width := by rw [← hb]; exact Bits.value_lt base
  have digitValue (i : Fin d) : (encodeBits width (z i).val).value = (z i).val :=
    encodeBits_value _ _ ((z i).isLt.trans hwidth)
  cases hu : updateBox radius z delta with
  | some out =>
    have he := (updateBox_eq_some_iff radius z out delta).mp hu
    simp only [Option.map_some]
    apply updateWords_ofFn
    intro i
    apply (updateDigit_eq_some_iff base _ _ _ (by rw [digitValue, hb]; exact (z i).isLt)).mpr
    have outValue := encodeBits_value width (out i).val ((out i).isLt.trans hwidth)
    rw [outValue, digitValue, hd, hb]
    exact ⟨by have hi := he i; dsimp [coordinate] at hi; omega, (out i).isLt⟩
  | none =>
    simp only [Option.map_none]
    have hn : ¬∀ i, |coordinate z i + delta i| ≤ 2 * (radius : ℤ) := by
      intro ha
      simp [updateBox, ha] at hu
    have his : ¬(updateWords base (boxWords width z) (List.ofFn deltas)).isSome = true := by
      intro hs
      have hi := (updateWords_isSome_ofFn base (fun i => encodeBits width (z i).val) deltas).mp hs
      apply hn
      intro i
      have hr := (updateDigit_isSome_iff base _ _ (by rw [digitValue, hb]; exact (z i).isLt)).mp (hi i)
      rw [digitValue, hd, hb] at hr
      exact (coordinate_range_iff z delta i).mp hr
    cases he : updateWords base (boxWords width z) (List.ofFn deltas) with
    | none => rfl
    | some out => simp [he] at his

/-- Canonically encoded actual integer coefficients give the same transition. -/
theorem updateWords_signed_box {width d radius : ℕ} (base : Bits width)
    (z : Box (Fin d) radius) (delta : Fin d → ℤ) (hb : base.value = 4 * radius + 1)
    (hd : ∀ i, (delta i).natAbs < 2 ^ width) :
    updateWords base (boxWords width z) (List.ofFn (fun i => signedWord width (delta i))) =
      (updateBox radius z delta).map (boxWords width) :=
  updateWords_box base z _ delta hb (fun i => signedWord_value _ (hd i))

/-- The complete repeated-division/update/Horner word calculation returns
exactly the actual updated box ID or fails on exactly the same range check. -/
theorem decode_update_encode_box {width d radius : ℕ} (base value : Bits width)
    (z : Box (Fin d) radius) (deltas : Fin d → SignedWord width) (delta : Fin d → ℤ)
    (hb : base.value = 4 * radius + 1) (hv : value.value = (boxEquiv d radius z).val)
    (hd : ∀ i, (deltas i).value = delta i) (hcap : (4 * radius + 1) ^ d ≤ 2 ^ width) :
    ((updateWords base (decodeWords base d value) (List.ofFn deltas)).map
      (fun ws => (encodeWords base ws).value)) =
      (updateBox radius z delta).map (fun z' => (boxEquiv d radius z').val) := by
  rw [decodeWords_box base value z hb hv, updateWords_box base z deltas delta hb hd]
  rw [Option.map_map]
  congr 1
  funext z'
  exact encodeWords_box base z' hb hcap

end WeightedMIS.ExpandedWords
