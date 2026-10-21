module

public import WeightedMIS.ScalarNodeCodec

/-! # Exact word-level encoding of the actual expanded-node equivalence -/

@[expose] public section

namespace WeightedMIS.ScalarNodeCodec

open Expanded NodeEncoding EfficientSearch SparseSearchGraph

variable {width r d radius : ℕ}

/-- Every decoder word represents the corresponding field of the actual node. -/
theorem decodeWords_node (node : Node (Fin r) (Fin d) radius)
    (id S T one two : Bits width)
    (hid : id.value = (nodeEquiv r d radius node).val)
    (hs : S.value = 2 * r + 1) (ht : T.value = 2 * (4 * radius + 1) ^ d)
    (h1 : one.value = 1) (h2 : two.value = 2) :
    (decodeWords id S T one two).values = coordinates node := by
  rw [decodeWords_values id S T one two (by rw [ht]; positivity) h1 h2, hid, hs, ht]
  exact decode_coordinates node

/-- Any stored node fields satisfying the exact coordinate specification encode
 to the precise numeric graph ID used by outgoing-list construction. -/
theorem encodeWords_node (node : Node (Fin r) (Fin d) radius)
    (S T one two : Bits width) (words : Words width)
    (hwords : words.values = coordinates node)
    (hs : S.value = 2 * r + 1) (ht : T.value = 2 * (4 * radius + 1) ^ d)
    (h1 : one.value = 1) (h2 : two.value = 2)
    (hwidth : nodeCount r d radius ≤ 2 ^ width) :
    (encodeWords S T one two words).value = (nodeEquiv r d radius node).val := by
  have he : encode S.value T.value words.values = (nodeEquiv r d radius node).val := by
    rw [hwords, hs, ht, encode_coordinates]
  rw [encodeWords_exact S T one two words h1 h2
    (by rw [he]; exact (nodeEquiv r d radius node).isLt.trans_le hwidth), he]

/-- The width already assigned to graph vertices also stores every scalar
 parameter used by decoding and encoding, including the zero-dimensional box. -/
theorem parameters_fit (r d radius : ℕ) :
    2 * r + 1 < 2 ^ vertexWidth r d radius ∧
    2 * (4 * radius + 1) ^ d < 2 ^ vertexWidth r d radius ∧
    1 < 2 ^ vertexWidth r d radius ∧ 2 < 2 ^ vertexWidth r d radius := by
  have hq : 1 ≤ (4 * radius + 1) ^ d := by
    have hp : 0 < (4 * radius + 1) ^ d := by positivity
    omega
  have hs : 1 ≤ 2 * r + 1 := by omega
  have hsq : 1 ≤ (2 * r + 1) ^ 2 := by nlinarith
  have hsle : 2 * r + 1 ≤ 1 + (2 * r + 1) ^ 2 := by nlinarith
  have hT : 1 ≤ 2 * (4 * radius + 1) ^ d := by omega
  have hS : 2 * r + 1 ≤ nodeCount r d radius := by
    calc
      _ ≤ 1 + (2 * r + 1) ^ 2 := hsle
      _ = 1 * (1 + (2 * r + 1) ^ 2) := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ hT
  have hblock : 2 * (4 * radius + 1) ^ d ≤ nodeCount r d radius := by
    exact Nat.le_mul_of_pos_right _ (by omega : 0 < 1 + (2 * r + 1) ^ 2)
  have htwo : 2 ≤ nodeCount r d radius :=
    (by omega : 2 ≤ 2 * (4 * radius + 1) ^ d).trans hblock
  have hn : nodeCount r d radius < 2 ^ vertexWidth r d radius := Nat.lt_size_self _
  exact ⟨hS.trans_lt hn, hblock.trans_lt hn, (by omega), htwo.trans_lt hn⟩

/-- Equal-width binary words are determined by their natural value. -/
theorem bits_value_injective (width : ℕ) : Function.Injective (@Bits.value width) := by
  induction width with
  | zero => intro a b _; cases a; cases b; rfl
  | succ width ih =>
      intro a b heq
      cases a with
      | cons abit atail =>
        cases b with
        | cons bbit btail =>
          have ha := Bits.value_lt atail
          have hb := Bits.value_lt btail
          have hbits : abit = bbit := by
            cases abit <;> cases bbit <;> simp_all [Bits.value] <;> omega
          subst bbit
          have htail : atail.value = btail.value := by
            cases abit <;> simp_all [Bits.value]
          rw [ih htail]

/-- The compiled encoder's word equals the graph's actual vertex key, rather
 than merely having a compatible numeric value. -/
theorem encodeWords_key (node : Node (Fin r) (Fin d) radius)
    (S T one two : Bits (vertexWidth r d radius))
    (words : Words (vertexWidth r d radius))
    (hwords : words.values = coordinates node)
    (hs : S.value = 2 * r + 1) (ht : T.value = 2 * (4 * radius + 1) ^ d)
    (h1 : one.value = 1) (h2 : two.value = 2) :
    encodeWords S T one two words = nodeKey node := by
  apply bits_value_injective
  have he := encodeWords_node node S T one two words hwords hs ht h1 h2
    (Nat.lt_size_self (nodeCount r d radius)).le
  simpa only [nodeKey, vertexKey_value] using he

end WeightedMIS.ScalarNodeCodec
