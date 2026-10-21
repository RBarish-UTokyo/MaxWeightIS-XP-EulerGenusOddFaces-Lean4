module

public import WeightedMIS.RegisterResize
public import WeightedMIS.RegisterSignificant
public import WeightedMIS.ExpandedCandidateSemantics

/-!
# Exact parameter words of the expanded search graph

`word k v` is the word of width `k` holding `v mod 2^k`. Binary addition,
multiplication, subtraction of one and resizing act on these words exactly as
the corresponding natural operations modulo `2^k`, so the parameter
calculation at a generous working width `G` is described without any
intermediate overflow premise. One fit premise `fitBound r d w < 2^G` then
makes every value that is stripped, resized or decremented exact.

At the canonical vertex width the arithmetic words represent the graph
dimensions (`ArithmeticRepresents`), the start and finish keys are
`(4m+1)^d - 1` and `(4m+1)^d`, and the hub state key is zero.
-/

@[expose] public section

namespace WeightedMIS.ExpandedParameters

open WeightedMIS.SparseSearchGraph WeightedMIS.NodeEncoding WeightedMIS.Expanded
open WeightedMIS.EfficientSearch WeightedMIS.ExpandedWords

/-- The word of width `k` holding `v mod 2^k`. -/
def word (k v : ℕ) : Bits k := encodeBits k (v % 2 ^ k)

@[simp] theorem word_value (k v : ℕ) : (word k v).value = v % 2 ^ k :=
  encodeBits_value _ _ (Nat.mod_lt _ (by positivity))

theorem word_value_of_lt {k v : ℕ} (h : v < 2 ^ k) : (word k v).value = v := by
  rw [word_value, Nat.mod_eq_of_lt h]

theorem eq_word {k v : ℕ} {x : Bits k} (h : x.value = v % 2 ^ k) : x = word k v :=
  ScalarNodeCodec.bits_value_injective k (by rw [word_value, h])

theorem word_mod (k v : ℕ) : word k (v % 2 ^ k) = word k v := by
  unfold word
  rw [Nat.mod_mod]

theorem zero_eq_word (k : ℕ) : Bits.zero k = word k 0 := eq_word (by simp)

theorem resizeTo_eq_word {k n : ℕ} (x : Bits n) : Bits.resizeTo k x = word k x.value := rfl

theorem resizeTo_word (k n v : ℕ) : Bits.resizeTo k (word n v) = word k (v % 2 ^ n) := by
  rw [resizeTo_eq_word, word_value]

theorem resizeTo_word_of_lt {k n v : ℕ} (h : v < 2 ^ n) :
    Bits.resizeTo k (word n v) = word k v := by
  rw [resizeTo_word, Nat.mod_eq_of_lt h]

theorem addCarry_word (k a b : ℕ) (c : Bool) :
    (Bits.addCarry (word k a) (word k b) c).1 = word k (a + b + if c then 1 else 0) := by
  apply eq_word
  have hv := Bits.addCarry_value (word k a) (word k b) c
  have hlt := Bits.value_lt (Bits.addCarry (word k a) (word k b) c).1
  simp only [word_value] at hv
  have h1 : ((Bits.addCarry (word k a) (word k b) c).1.value +
      2 ^ k * (if (Bits.addCarry (word k a) (word k b) c).2.1 then 1 else 0)) % 2 ^ k =
        (Bits.addCarry (word k a) (word k b) c).1.value := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rw [hv] at h1
  rw [← h1]
  exact ((Nat.mod_modEq a _).add (Nat.mod_modEq b _)).add_right _

theorem add_word (k a b : ℕ) : (Bits.add (word k a) (word k b)).1 = word k (a + b) := by
  show (Bits.addCarry (word k a) (word k b) false).1 = _
  simpa using addCarry_word k a b false

theorem multiply_word (k a b : ℕ) :
    (Bits.multiply (word k a) (word k b)).1 = word k (a * b) := by
  apply eq_word
  rw [Bits.multiply_value, word_value, word_value, ← Nat.mul_mod]

theorem subtract_word {k a : ℕ} (h1 : 1 ≤ a) (ha : a < 2 ^ k) (hk : 1 < 2 ^ k) :
    (Bits.subtract (word k a) (word k 1)).1 = word k (a - 1) := by
  apply eq_word
  have hv := (Bits.subtract_value_of_le (word k a) (word k 1)
    (by rw [word_value_of_lt hk, word_value_of_lt ha]; exact h1)).2
  rw [hv, word_value_of_lt hk, word_value_of_lt ha, Nat.mod_eq_of_lt (by omega)]

/-- One generous bound on every parameter value. -/
def fitBound {m : ℕ} (r d : ℕ) (w : Fin m → ℕ) : ℕ :=
  (entryBound r m d m + 2) * (weightBound w + 1)

/-- The value whose binary length is the cost width. -/
def costProduct {m : ℕ} (r d : ℕ) (w : Fin m → ℕ) : ℕ :=
  (entryBound r m d m + 2) * weightBound w

theorem costWidth_eq {m : ℕ} (r d : ℕ) (w : Fin m → ℕ) :
    costWidth r d m w = (costProduct r d w).size := rfl

/-- The arithmetic record at the canonical vertex width. -/
def arithmetic (r d radius : ℕ) : ArithmeticWords (vertexWidth r d radius) :=
  ⟨word _ (4 * radius + 1), word _ (2 * r + 1), word _ (2 * (4 * radius + 1) ^ d),
    word _ 1, word _ 2⟩

theorem nodeCount_ge (r d radius : ℕ) :
    4 ≤ nodeCount r d radius ∧ 2 * (4 * radius + 1) ^ d ≤ nodeCount r d radius ∧
      2 * r + 1 ≤ nodeCount r d radius := by
  have hq : 1 ≤ (4 * radius + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hsq : 2 * r + 1 ≤ (2 * r + 1) ^ 2 := by nlinarith
  unfold nodeCount
  refine ⟨?_, Nat.le_mul_of_pos_right _ (by omega), ?_⟩ <;> nlinarith

theorem arithmetic_represents (r d radius : ℕ) :
    ArithmeticRepresents (arithmetic r d radius) r d radius := by
  obtain ⟨hs, hb, h1, h2⟩ := ScalarNodeCodec.parameters_fit r d radius
  refine ⟨?_, word_value_of_lt hs, word_value_of_lt hb, word_value_of_lt h1,
    word_value_of_lt h2⟩
  rcases Nat.eq_zero_or_pos d with hd | hd
  · exact Or.inl hd
  · right
    apply word_value_of_lt
    have hle : 4 * radius + 1 ≤ (4 * radius + 1) ^ d :=
      Nat.le_self_pow (by omega) _
    omega

/-- Twice the box index of the zero box, plus one, is the box count. -/
theorem zeroBox_index (d radius : ℕ) :
    2 * (boxEquiv d radius (zeroBox (Fin d) radius)).val + 1 = (4 * radius + 1) ^ d := by
  have hsum : (boxEquiv d radius (zeroBox (Fin d) radius)).val =
      ∑ i ∈ Finset.range d, 2 * radius * (4 * radius + 1) ^ i := by
    simp only [boxEquiv, finFunctionFinEquiv_apply, zeroBox]
    exact Fin.sum_univ_eq_sum_range (fun i => 2 * radius * (4 * radius + 1) ^ i) d
  have hg := geom_sum_mul_add (4 * radius) d
  rw [hsum, ← Finset.mul_sum, ← hg]
  ring

theorem start_index (r d radius : ℕ) :
    (nodeEquiv r d radius (start radius)).val = (4 * radius + 1) ^ d - 1 := by
  have hz := zeroBox_index d radius
  rw [start, ScalarNodeCodec.nodeEquiv_hub]
  simp only [ZMod.val_zero]
  omega

theorem finish_index (r d radius : ℕ) :
    (nodeEquiv r d radius (finish radius)).val = (4 * radius + 1) ^ d := by
  have hz := zeroBox_index d radius
  have h1 : (1 : ZMod 2).val = 1 := rfl
  rw [finish, ScalarNodeCodec.nodeEquiv_hub, h1]
  omega

theorem nodeKey_eq_word {r d radius : ℕ} (v : Node (Fin r) (Fin d) radius) :
    nodeKey v = word _ (nodeEquiv r d radius v).val := by
  apply eq_word
  rw [nodeKey, vertexKey_value]
  exact (Nat.mod_eq_of_lt ((nodeEquiv r d radius v).isLt.trans (Nat.lt_size_self _))).symm

theorem nodeKey_start (r d radius : ℕ) :
    nodeKey (start radius : Node (Fin r) (Fin d) radius) =
      word _ ((4 * radius + 1) ^ d - 1) := by
  rw [nodeKey_eq_word, start_index]

theorem nodeKey_finish (r d radius : ℕ) :
    nodeKey (finish radius : Node (Fin r) (Fin d) radius) =
      word _ ((4 * radius + 1) ^ d) := by
  rw [nodeKey_eq_word, finish_index]

theorem stateEquiv_none (r : ℕ) : (NodeEncoding.stateEquiv r none).val = 0 := by
  simp [NodeEncoding.stateEquiv]

/-- Any key function satisfying the stored-key specification stores the hub
state as the zero word. -/
theorem hubKey_eq {r n : ℕ} {key : Walks.State (Fin r) → Bits n}
    (hk : ∀ v, (key v).value = (NodeEncoding.stateEquiv r v).val) :
    key none = Bits.zero n :=
  ScalarNodeCodec.bits_value_injective n (by rw [hk, stateEquiv_none, Bits.value_zero])

/-- The limit word is the significant part of the node count. -/
theorem limit_value (r d radius : ℕ) :
    (encodeBits (vertexWidth r d radius) (nodeCount r d radius)).value = nodeCount r d radius :=
  encodeBits_value _ _ (Nat.lt_size_self _)

/-- All consequences of the fit premise used by the parameter procedure. -/
structure Fits {m : ℕ} (G r d : ℕ) (w : Fin m → ℕ) : Prop where
  one : 1 < 2 ^ G
  two : 2 < 2 ^ G
  base : 4 * m + 1 < 2 ^ G
  states : 2 * r + 1 < 2 ^ G
  pow : (4 * m + 1) ^ d < 2 ^ G
  block : 2 * (4 * m + 1) ^ d < 2 ^ G
  nodes : nodeCount r d m < 2 ^ G
  entries : entryBound r m d m + 2 ≤ 2 ^ G
  cost : costProduct r d w < 2 ^ G
  vertexWidth_le : vertexWidth r d m ≤ G
  costWidth_le : costWidth r d m w ≤ G

theorem fits_of_lt {m G r d : ℕ} {w : Fin m → ℕ} (h : fitBound r d w < 2 ^ G) :
    Fits G r d w := by
  obtain ⟨h4, hblock, hstates⟩ := nodeCount_ge r d m
  have hq : 1 ≤ (4 * m + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hN : nodeCount r d m ≤ entryBound r m d m := by
    unfold entryBound
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hE : 4 * m + 1 ≤ entryBound r m d m := by
    unfold entryBound
    nlinarith
  have hF : entryBound r m d m + 2 ≤ fitBound r d w := by
    unfold fitBound
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hC : costProduct r d w ≤ fitBound r d w := by
    unfold costProduct fitBound
    exact Nat.mul_le_mul_left _ (by omega)
  have hnodes : nodeCount r d m < 2 ^ G := by omega
  have hcost : costProduct r d w < 2 ^ G := hC.trans_lt h
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, hnodes, by omega, hcost,
    Nat.size_le.mpr hnodes, Nat.size_le.mpr hcost⟩

end WeightedMIS.ExpandedParameters
