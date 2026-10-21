module

public import WeightedMIS.ExpandedCoordinate
public import WeightedMIS.RegisterDigits
public import WeightedMIS.RegisterHorner
public import WeightedMIS.SparseSearchGraph

/-! # Exact binary digit encoding of the actual finite signature box -/

@[expose] public section

namespace WeightedMIS.ExpandedWords

open WeightedMIS.EfficientSearch WeightedMIS.SparseSearchGraph WeightedMIS.NodeEncoding
open WeightedMIS.Expanded WeightedMIS.RegisterDigits WeightedMIS.RegisterHorner

/-- Fixed-width binary words are determined by their natural values. -/
theorem bits_value_injective {n : ℕ} : Function.Injective (@Bits.value n) := by
  intro a b h
  induction n with
  | zero => cases a; cases b; rfl
  | succ n ih =>
    cases a with
    | cons x xs =>
      cases b with
      | cons y ys =>
        have hx := Bits.value_lt xs
        have hy := Bits.value_lt ys
        cases x <;> cases y <;> simp only [Bits.value, Bool.false_eq_true, ↓reduceIte, zero_add] at h
        · exact congrArg (Bits.cons false) (ih h)
        · omega
        · omega
        · exact congrArg (Bits.cons true) (ih (by omega))

/-- Explicit fixed-width words for all shifted coordinates, in coordinate order. -/
def boxWords (width : ℕ) {d radius : ℕ} (z : Box (Fin d) radius) : List (Bits width) :=
  List.ofFn (fun i => encodeBits width (z i).val)

@[simp] theorem boxWords_length (width : ℕ) {d radius : ℕ} (z : Box (Fin d) radius) :
    (boxWords width z).length = d := by simp [boxWords]

theorem boxWords_values {width d radius : ℕ} (z : Box (Fin d) radius)
    (hb : 4 * radius + 1 < 2 ^ width) :
    (boxWords width z).map Bits.value = List.ofFn (fun i => (z i).val) := by
  rw [boxWords, List.map_ofFn]
  congr 1
  funext i
  exact encodeBits_value _ _ ((z i).isLt.trans hb)

/-- The natural repeated-division list is the actual positional inverse. -/
theorem naturalDigits_ofFn (base count value : ℕ) (hb : 0 < base) :
    naturalDigits base count value =
      List.ofFn (fun i => ((EncodingCost.decodeDigits base hb count value).value i).val) := by
  induction count generalizing value with
  | zero => simp [naturalDigits]
  | succ count ih =>
    rw [naturalDigits, List.ofFn_succ]
    simp only [EncodingCost.decodeDigits, Fin.cases_zero, Fin.cases_succ]
    rw [ih]

/-- Actual binary division decodes a box ID into exactly its actual shifted
coordinate words; no enumeration of box tuples is used. -/
theorem decodeWords_box {width d radius : ℕ} (base value : Bits width)
    (z : Box (Fin d) radius) (hb : base.value = 4 * radius + 1)
    (hv : value.value = (boxEquiv d radius z).val) :
    decodeWords base d value = boxWords width z := by
  apply (List.map_inj_right (fun _ _ h => bits_value_injective h)).mp
  rw [decodeWords_values, boxWords_values z (by rw [← hb]; exact Bits.value_lt base), hb, hv]
  rw [naturalDigits_ofFn _ _ _ (by omega)]
  have he := EncodingCost.decodeDigits_equiv (4 * radius + 1) d (by omega) (boxEquiv d radius z)
  have he' : (EncodingCost.decodeDigits (4 * radius + 1) (by omega) d
      (boxEquiv d radius z).val).value = z := by
    simpa only [boxEquiv, Equiv.symm_apply_apply] using he
  rw [he']

/-- Word-list Horner evaluation equals the actual signature's positional ID. -/
theorem numeral_boxWords {width d radius : ℕ} (z : Box (Fin d) radius)
    (hb : 4 * radius + 1 < 2 ^ width) :
    numeral (4 * radius + 1) (boxWords width z) = (boxEquiv d radius z).val := by
  have aux : ∀ (d : ℕ) (z : Box (Fin d) radius),
      numeral (4 * radius + 1) (boxWords width z) =
        (EncodingCost.encodeDigits (4 * radius + 1) d z).value := by
    intro d
    induction d with
    | zero => intro z; simp [boxWords, numeral, EncodingCost.encodeDigits]
    | succ d ih =>
      intro z
      rw [boxWords, List.ofFn_succ, numeral]
      rw [encodeBits_value _ _ ((z 0).isLt.trans hb)]
      change (z 0).val + (4 * radius + 1) * numeral (4 * radius + 1)
        (boxWords width (fun i => z i.succ)) = _
      rw [ih]
      rfl
  rw [aux, EncodingCost.encodeDigits_value]
  rfl

/-- Compiled multiplication/addition in Horner form returns the exact box ID
when the shared word width contains the entire box range. -/
theorem encodeWords_box {width d radius : ℕ} (base : Bits width) (z : Box (Fin d) radius)
    (hb : base.value = 4 * radius + 1) (hcap : (4 * radius + 1) ^ d ≤ 2 ^ width) :
    (encodeWords base (boxWords width z)).value = (boxEquiv d radius z).val := by
  have hn := numeral_boxWords z (by rw [← hb]; exact Bits.value_lt base)
  rw [encodeWords_exact base _ (by rw [hb, hn]; exact (boxEquiv d radius z).isLt.trans_le hcap)]
  simpa [hb] using hn

/-- Canonical signed-magnitude words for integral signature coefficients. -/
def signedWord (width : ℕ) (z : ℤ) : SignedWord width :=
  ⟨decide (z < 0), encodeBits width z.natAbs⟩

theorem signedWord_value {width : ℕ} (z : ℤ) (hz : z.natAbs < 2 ^ width) :
    (signedWord width z).value = z := by
  simp only [signedWord, SignedWord.value, encodeBits_value _ _ hz, decide_eq_true_eq]
  split_ifs with h
  · rw [Int.natCast_natAbs, abs_of_neg h]; omega
  · rw [Int.natCast_natAbs, abs_of_nonneg (le_of_not_gt h)]

end WeightedMIS.ExpandedWords
