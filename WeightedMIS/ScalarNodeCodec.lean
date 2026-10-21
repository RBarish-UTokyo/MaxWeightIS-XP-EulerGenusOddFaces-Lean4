module

public import WeightedMIS.NodeEncoding
public import WeightedMIS.SparseSearchGraph
public import WeightedMIS.BinaryGCD

/-!
# Positional scalar coordinates of expanded nodes

The numeric codec uses quotient and remainder by the parity-box block size
and the signed-state count. These formulas agree with the executable product
and sum equivalences used by the expanded-graph numbering.
-/

@[expose] public section

namespace WeightedMIS.ScalarNodeCodec

open Expanded NodeEncoding EfficientSearch

structure Coordinates where
  hub : Bool
  anchor : ℕ
  current : ℕ
  box : ℕ
  parity : ℕ
  deriving DecidableEq

/-- The scalar data carried by a typed expanded node. -/
def coordinates {r d radius : ℕ} : Node (Fin r) (Fin d) radius → Coordinates
  | .hub z parity => ⟨true, 0, 0, (boxEquiv d radius z).val, parity.val⟩
  | .work a v z parity => ⟨false, (stateEquiv r a).val, (stateEquiv r v).val,
      (boxEquiv d radius z).val, parity.val⟩

def encode (S T : ℕ) (node : Coordinates) : ℕ :=
  if node.hub then 2 * node.box + node.parity
  else T * (1 + S * node.anchor + node.current) + 2 * node.box + node.parity

def decode (S T id : ℕ) : Coordinates :=
  if id < T then ⟨true, 0, 0, id % T / 2, id % T % 2⟩
  else ⟨false, (id / T - 1) / S, (id / T - 1) % S, id % T / 2, id % T % 2⟩

theorem nodeEquiv_hub {r d radius : ℕ} (z : Box (Fin d) radius) (parity : ZMod 2) :
    (nodeEquiv r d radius (.hub z parity)).val =
      2 * (boxEquiv d radius z).val + parity.val := by
  simp [nodeEquiv, nodeShape, parityEquiv, finProdFinEquiv, finSumFinEquiv, Equiv.prodCongr_apply ]
  change parity.val + 2 * (boxEquiv d radius z).val = _
  omega

theorem nodeEquiv_work {r d radius : ℕ} (a v : Walks.State (Fin r))
    (z : Box (Fin d) radius) (parity : ZMod 2) :
    (nodeEquiv r d radius (.work a v z parity)).val =
      (2 * (4 * radius + 1) ^ d) *
        (1 + (2 * r + 1) * (stateEquiv r a).val + (stateEquiv r v).val) +
          2 * (boxEquiv d radius z).val + parity.val := by
  change (4 * radius + 1) ^ d * 2 +
    ((parity.val + 2 * (boxEquiv d radius z).val) +
      ((4 * radius + 1) ^ d * 2) * (stateEquiv r v).val +
      ((2 * r + 1) * ((4 * radius + 1) ^ d * 2)) * (stateEquiv r a).val) = _
  ring

theorem encode_coordinates {r d radius : ℕ} (node : Node (Fin r) (Fin d) radius) :
    encode (2 * r + 1) (2 * (4 * radius + 1) ^ d) (coordinates node) =
      (nodeEquiv r d radius node).val := by
  cases node with
  | hub z parity => exact (nodeEquiv_hub z parity).symm
  | work a v z parity => exact (nodeEquiv_work a v z parity).symm

/-- Scalar decoding recovers every field of the actual numbered node. -/
theorem decode_coordinates {r d radius : ℕ} (node : Node (Fin r) (Fin d) radius) :
    decode (2 * r + 1) (2 * (4 * radius + 1) ^ d)
      (nodeEquiv r d radius node).val = coordinates node := by
  have hT : 0 < 2 * (4 * radius + 1) ^ d := by positivity
  cases node with
  | hub z parity =>
      have hp : parity.val < 2 := parity.isLt
      have hz := (boxEquiv d radius z).isLt
      have htail : 2 * (boxEquiv d radius z).val + parity.val <
          2 * (4 * radius + 1) ^ d := by omega
      rw [nodeEquiv_hub]
      simp only [decode, htail, ↓reduceIte, Nat.mod_eq_of_lt htail, coordinates]
      congr 1 <;> omega
  | work a v z parity =>
      have ha := (stateEquiv r a).isLt
      have hv := (stateEquiv r v).isLt
      have hp : parity.val < 2 := parity.isLt
      have hz := (boxEquiv d radius z).isLt
      let T := 2 * (4 * radius + 1) ^ d
      let S := 2 * r + 1
      let k := 1 + S * (stateEquiv r a).val + (stateEquiv r v).val
      let t := 2 * (boxEquiv d radius z).val + parity.val
      have ht : t < T := by dsimp [t, T]; omega
      have hk : 1 ≤ k := by dsimp [k]; omega
      have hge : T ≤ T * k + t := by nlinarith
      have hq : (T * k + t) / T = k := by
        rw [Nat.mul_add_div (by omega : 0 < T), Nat.div_eq_of_lt ht, Nat.add_zero]
      have hr : (T * k + t) % T = t := by simp [Nat.add_mod, Nat.mod_eq_of_lt ht]
      rw [nodeEquiv_work]
      rw [Nat.add_assoc]
      change decode S T (T * k + t) = _
      simp only [decode, Nat.not_lt.mpr hge, ↓reduceIte, hq, hr, coordinates]
      have hkm : k - 1 = S * (stateEquiv r a).val + (stateEquiv r v).val := by
        dsimp [k]; omega
      rw [hkm]
      have haq : (S * (stateEquiv r a).val + (stateEquiv r v).val) / S =
          (stateEquiv r a).val := by
        rw [Nat.mul_add_div (by dsimp [S]; omega), Nat.div_eq_of_lt hv, Nat.add_zero]
      have hvr : (S * (stateEquiv r a).val + (stateEquiv r v).val) % S =
          (stateEquiv r v).val := by
        simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
        exact Nat.mod_eq_of_lt hv
      rw [haq, hvr]
      congr 1 <;> dsimp [t] <;> omega

structure Words (width : ℕ) where
  hub : Bool
  anchor : Bits width
  current : Bits width
  box : Bits width
  parity : Bits width

/-- Read the natural values of the five returned fields. -/
def Words.values {width : ℕ} (node : Words width) : Coordinates :=
  ⟨node.hub, node.anchor.value, node.current.value, node.box.value, node.parity.value⟩

/-- Exact bit-algorithm counterpart of scalar decoding. -/
def decodeWords {width : ℕ} (id S T one two : Bits width) : Words width :=
  let q := (Bits.divide id T).1
  let rem := (Bits.remainder id T).1
  let box := (Bits.divide rem two).1
  let parity := (Bits.remainder rem two).1
  if (Bits.compare id T).1 = .lt then ⟨true, q, q, box, parity⟩
  else
    let k := (Bits.subtract q one).1
    ⟨false, (Bits.divide k S).1, (Bits.remainder k S).1, box, parity⟩

/-- The bounded-word decoder implements ordinary scalar coordinates exactly. -/
theorem decodeWords_values {width : ℕ} (id S T one two : Bits width)
    (hT : 0 < T.value) (h1 : one.value = 1) (h2 : two.value = 2) :
    (decodeWords id S T one two).values = decode S.value T.value id.value := by
  have hcmp := (Bits.compare_correct id T).1
  have hq := (Bits.divide_value id T).1
  have hr := Bits.remainder_value id T
  have hb := (Bits.divide_value (Bits.remainder id T).1 two).1
  have hp := Bits.remainder_value (Bits.remainder id T).1 two
  rw [hr, h2] at hb hp
  by_cases hh : id.value < T.value
  · have hlt := hcmp.mpr hh
    have hq0 : (Bits.divide id T).1.value = 0 := by rw [hq]; exact Nat.div_eq_of_lt hh
    simp only [decodeWords, hlt, ↓reduceIte, Words.values, decode, hh, hq0, hb, hp]
  · have hn := mt hcmp.mp hh
    have hle : one.value ≤ (Bits.divide id T).1.value := by
      rw [h1, hq]
      exact Nat.div_pos (Nat.le_of_not_gt hh) hT
    have hk := (Bits.subtract_value_of_le (Bits.divide id T).1 one hle).2
    rw [hq, h1] at hk
    have ha := (Bits.divide_value (Bits.subtract (Bits.divide id T).1 one).1 S).1
    have hv := Bits.remainder_value (Bits.subtract (Bits.divide id T).1 one).1 S
    rw [hk] at ha hv
    simp only [decodeWords, hn, ↓reduceIte, Words.values, decode, hh, ha, hv, hb, hp]

/-- Reassemble a node ID by the fixed-width arithmetic algorithms. -/
def encodeWords {width : ℕ} (S T one two : Bits width) (node : Words width) : Bits width :=
  let tail := (Bits.add (Bits.multiply two node.box).1 node.parity).1
  if node.hub then tail
  else
    let index := (Bits.add (Bits.add (Bits.multiply S node.anchor).1 node.current).1 one).1
    (Bits.add (Bits.multiply T index).1 tail).1

private theorem multiply_modEq {width : ℕ} (a b : Bits width) :
    Nat.ModEq (2 ^ width) (Bits.multiply a b).1.value (a.value * b.value) := by
  rw [Bits.multiply_value]
  exact Nat.mod_modEq _ _

theorem encodeWords_modEq {width : ℕ} (S T one two : Bits width) (node : Words width)
    (h1 : one.value = 1) (h2 : two.value = 2) :
    Nat.ModEq (2 ^ width) (encodeWords S T one two node).value
      (encode S.value T.value node.values) := by
  have ht := (Bits.add_modEq (Bits.multiply two node.box).1 node.parity).trans
    ((multiply_modEq two node.box).add_right node.parity.value)
  have ha := (Bits.add_modEq (Bits.multiply S node.anchor).1 node.current).trans
    ((multiply_modEq S node.anchor).add_right node.current.value)
  have hi := (Bits.add_modEq (Bits.add (Bits.multiply S node.anchor).1 node.current).1 one).trans
    (ha.add_right one.value)
  have hg := (multiply_modEq T
    (Bits.add (Bits.add (Bits.multiply S node.anchor).1 node.current).1 one).1).trans
      (hi.mul_left T.value)
  cases hh : node.hub with
  | true => simpa only [encodeWords, hh, ↓reduceIte, encode, Words.values, h2] using ht
  | false =>
      have h := (Bits.add_modEq
        (Bits.multiply T (Bits.add (Bits.add (Bits.multiply S node.anchor).1 node.current).1 one).1).1
        (Bits.add (Bits.multiply two node.box).1 node.parity).1).trans (hg.add ht)
      simpa [encodeWords, encode, Words.values, hh, h1, h2,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- No intermediate arithmetic-size premise is required: the complete valid
 ID fits, and modular bit arithmetic preserves the positional polynomial. -/
theorem encodeWords_exact {width : ℕ} (S T one two : Bits width) (node : Words width)
    (h1 : one.value = 1) (h2 : two.value = 2)
    (hfit : encode S.value T.value node.values < 2 ^ width) :
    (encodeWords S T one two node).value = encode S.value T.value node.values := by
  have h := encodeWords_modEq S T one two node h1 h2
  change (encodeWords S T one two node).value % 2 ^ width =
    encode S.value T.value node.values % 2 ^ width at h
  exact (Nat.mod_eq_of_lt (Bits.value_lt _)).symm.trans
    (h.trans (Nat.mod_eq_of_lt hfit))

end WeightedMIS.ScalarNodeCodec
