module

public import WeightedMIS.NetworkWeights

/-!
# Word encoding of the double-cover network

Network nodes of `DoubleCoverNetwork.Node (Fin n)` are words of width `W + 2`:
two tag bits followed by a payload word of width `W`. The source and sink are
`00·0` and `01·0`; the copies of a vertex `v` are `10·v` (left) and `11·v`
(right), where `v` is the vertex word `GraphReachEncoded.word W v`. The value of
a node word is injective whenever `n < 2 ^ W`.

The capacity word of an ordered pair is the canonical encoding of the entry of
`MaxFlowPreprocessing.matrix`. The stored table lists all ordered pairs of
`MaxFlowPreprocessing.networkNodes (List.finRange n)` in `List.product` order;
it is written here as a nested flat map, the shape built by the register code.
Adjacency of two vertex words is decided by scanning the endpoint words of all
edges; the result agrees with `EdgeTransport.Adj` for every decision instance.
-/

@[expose] public section

namespace WeightedMIS.NetworkWords

open WeightedMIS.EfficientSearch WeightedMIS.DoubleCoverNetwork WeightedMIS.MaxFlowPreprocessing
open WeightedMIS.GraphReachEncoded
open scoped BigOperators

variable {n : ℕ}

/-! ## Node words -/

/-- Inner (vertex copy) nodes have leading bit `true`. -/
def tagInner : Node (Fin n) → Bool
  | .inl _ => false
  | .inr _ => true

/-- The terminal flag, or the side of a vertex copy. -/
def tagSide : Node (Fin n) → Bool
  | .inl b => b
  | .inr p => p.1

def payload (W : ℕ) : Node (Fin n) → Bits W
  | .inl _ => Bits.zero W
  | .inr p => word W p.2.val

def nodeWord (W : ℕ) (u : Node (Fin n)) : Bits (W + 2) :=
  .cons (tagInner u) (.cons (tagSide u) (payload W u))

theorem nodeWord_injective {W : ℕ} (hn : n < 2 ^ W) :
    Function.Injective (nodeWord W (n := n)) := by
  intro u v huv
  simp only [nodeWord, Bits.cons.injEq] at huv
  obtain ⟨h1, h2, h3⟩ := huv
  rcases u with b | ⟨b, x⟩ <;> rcases v with c | ⟨c, y⟩ <;>
    simp only [tagInner, tagSide, payload, reduceCtorEq] at h1 h2 h3
  · rw [h2]
  · rw [h2, word_injective hn h3]

theorem nodeWord_value_injective {W : ℕ} (hn : n < 2 ^ W) :
    Function.Injective (fun u : Node (Fin n) => (nodeWord W u).value) :=
  fun _ _ h => nodeWord_injective hn (ResidualListReach.bits_value_inj h)

/-- The node enumeration used by the preprocessing. -/
abbrev nodes (n : ℕ) : List (Node (Fin n)) := networkNodes (List.finRange n)

theorem nodes_eq (n : ℕ) : nodes n = sourceNode :: sinkNode ::
    ((List.finRange n).map (fun v => (Sum.inr (false, v) : Node (Fin n))) ++
      (List.finRange n).map (fun v => (Sum.inr (true, v) : Node (Fin n)))) := by
  simp [nodes, networkNodes]

theorem nodes_complete (n : ℕ) : ∀ u, u ∈ nodes n :=
  networkNodes_complete _ (List.mem_finRange)

theorem nodes_length (n : ℕ) : (nodes n).length = Fintype.card (Node (Fin n)) := by
  rw [nodes_eq]
  simp [Fintype.card_sum, Fintype.card_prod]
  ring

/-- The record of a node: its word and the scaled weight of its vertex. -/
def muOf {B : ℕ} (muw : Fin n → Bits B) (zero : Bits B) : Node (Fin n) → Bits B
  | .inl _ => zero
  | .inr p => muw p.2

/-! ## Capacity words -/

/-- The canonical capacity word of an ordered pair. -/
def capWord (B : ℕ) (adj : Fin n → Fin n → Prop) [DecidableRel adj] (μ : Fin n → ℕ)
    (u v : Node (Fin n)) : Bits B :=
  word B (matrix adj μ u v)

section Caps

variable (B : ℕ) (adj : Fin n → Fin n → Prop) [DecidableRel adj] (μ : Fin n → ℕ)

theorem cap_source_left (y : Fin n) :
    capWord B adj μ (.inl false) (.inr (false, y)) = word B (μ y) := rfl

theorem cap_left_right (x y : Fin n) :
    capWord B adj μ (.inr (false, x)) (.inr (true, y)) =
      if adj x y then word B (1 + ∑ v, μ v) else word B 0 := by
  unfold capWord
  simp only [matrix]
  split <;> rfl

theorem cap_right_sink (x : Fin n) :
    capWord B adj μ (.inr (true, x)) (.inl true) = word B (μ x) := rfl

/-- Every other ordered pair has capacity zero. -/
theorem cap_zero (u v : Node (Fin n))
    (h1 : ¬ (u = .inl false ∧ tagInner v = true ∧ tagSide v = false))
    (h2 : ¬ (tagInner u = true ∧ tagSide u = false ∧ tagInner v = true ∧ tagSide v = true))
    (h3 : ¬ (tagInner u = true ∧ tagSide u = true ∧ v = .inl true)) :
    capWord B adj μ u v = word B 0 := by
  unfold capWord
  congr 1
  rcases u with (_ | _) | ⟨(_ | _), x⟩ <;> rcases v with (_ | _) | ⟨(_ | _), y⟩ <;>
    simp_all [matrix, tagInner, tagSide]

theorem matrix_le (u v : Node (Fin n)) : matrix adj μ u v ≤ 1 + ∑ x, μ x := by
  have hs (y : Fin n) : μ y ≤ ∑ x, μ x :=
    Finset.single_le_sum (f := μ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
  rcases u with (_ | _) | ⟨(_ | _), x⟩ <;> rcases v with (_ | _) | ⟨(_ | _), y⟩ <;>
    simp only [matrix] <;> first | omega | (have := hs x; omega) | (have := hs y; omega) |
      (split <;> omega)

theorem matrix_zero_or (u v : Node (Fin n)) : matrix adj μ u v = 0 ∨ matrix adj μ v u = 0 := by
  rcases u with (_ | _) | ⟨(_ | _), x⟩ <;> rcases v with (_ | _) | ⟨(_ | _), y⟩ <;>
    simp [matrix]

theorem matrix_pair_le (u v : Node (Fin n)) :
    matrix adj μ u v + matrix adj μ v u ≤ 1 + ∑ x, μ x := by
  rcases matrix_zero_or adj μ u v with h | h
  · rw [h, zero_add]; exact matrix_le adj μ v u
  · rw [h, add_zero]; exact matrix_le adj μ u v

theorem capWord_value {B : ℕ} (hbig : 1 + ∑ x, μ x < 2 ^ B) (u v : Node (Fin n)) :
    (capWord B adj μ u v).value = matrix adj μ u v :=
  word_value (lt_of_le_of_lt (matrix_le adj μ u v) hbig)

end Caps

/-! ## Adjacency of vertex words -/

/-- An edge record joins the two queried vertex words, in either orientation. -/
def edgeMatch {W : ℕ} (x y : Bits W) (e : Bits W × Bits W) : Bool :=
  (decide (e.1 = x) && decide (e.2 = y)) || (decide (e.1 = y) && decide (e.2 = x))

theorem adj_words {W m : ℕ} (hn : n < 2 ^ W) (left right : Fin m → Fin n) (x y : Fin n) :
    (edgeWords W left right).any (edgeMatch (word W x.val) (word W y.val)) = true ↔
      EdgeTransport.Adj left right x y := by
  simp only [List.any_eq_true, edgeWords, List.mem_map, List.mem_finRange, true_and,
    EdgeTransport.Adj]
  constructor
  · rintro ⟨_, ⟨e, rfl⟩, he⟩
    refine ⟨e, ?_⟩
    simp only [edgeMatch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      word_eq_iff hn] at he
    exact he
  · rintro ⟨e, he⟩
    refine ⟨_, ⟨e, rfl⟩, ?_⟩
    simp only [edgeMatch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, word_eq_iff hn]
    exact he

/-! ## The stored table -/

theorem product_map_eq {α β : Type*} (l : List α) (g : α × α → β) :
    (l.product l).map g = l.flatMap (fun u => l.flatMap (fun v => [g (u, v)])) := by
  simp only [List.product, List.map_flatMap, List.map_map]
  congr 1
  funext u
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

end WeightedMIS.NetworkWords
