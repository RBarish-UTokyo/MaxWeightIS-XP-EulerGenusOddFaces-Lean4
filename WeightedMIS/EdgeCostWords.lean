module

public import WeightedMIS.RegisterArcLookup
public import WeightedMIS.RegisterPreprocessing
public import WeightedMIS.IntegerEdgeCosts

/-!
# Word-level reference for the integer edge costs

`IntegerEdgeCosts.integerCost` sums over all ordered vertex pairs. For the
edge list `List.finRange m` only the two orientations of the endpoints of an
edge `e` can select `e`, and they do so exactly when no earlier edge joins the
same endpoints (`integerCost_local`). A loop contributes one term.

On an adjacent ordered pair the stored transport entry is the large capacity
minus the residual capacity of the arc from the left copy to the right copy
(`transport_eq_sub`). This uses only feasibility of the computed flow, no
optimality, and holds for every decision instance of the endpoint adjacency.

`costWords` is the word-level computation performed by the register code:
for every edge record, scanned with the reversed list of earlier records, it
returns the zero word when an earlier record joins the same endpoints, and
otherwise `big - residual(10·a, 11·b)` (plus `big - residual(10·b, 11·a)` when
the endpoints differ). `costWords_eq` identifies the result with the canonical
words of `integerCost`.
-/

@[expose] public section

namespace WeightedMIS.EdgeCostWords

open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords WeightedMIS.DoubleCoverNetwork
open WeightedMIS.MaxFlowPreprocessing WeightedMIS.NetworkWords WeightedMIS.NetworkWeights
open WeightedMIS.GraphReachEncoded
open scoped BigOperators

variable {n m : ℕ}

/-! ## The first edge with given endpoints -/

theorem split_lt {as bs : List (Fin m)} {e : Fin m} (hs : List.finRange m = as ++ e :: bs)
    (x : Fin m) : x ∈ as ↔ x < e := by
  have hp := List.pairwise_lt_finRange m
  rw [hs, List.pairwise_append, List.pairwise_cons] at hp
  obtain ⟨-, ⟨hcons, -⟩, hcross⟩ := hp
  constructor
  · intro hx
    exact hcross x hx e List.mem_cons_self
  · intro hx
    have hmem : x ∈ as ++ e :: bs := hs ▸ List.mem_finRange x
    rcases List.mem_append.mp hmem with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h (ne_of_lt hx)
      · exact absurd (hcons x h) (not_lt.mpr hx.le)

/-- The selected edge of a pair is the first edge of `List.finRange m` joining it. -/
theorem selected_finRange_iff (left right : Fin m → Fin n) (u v : Fin n) (e : Fin m) :
    EdgeAllocation.selected left right (List.finRange m) u v = some e ↔
      EdgeAllocation.Matches left right u v e ∧
        ∀ e' < e, ¬ EdgeAllocation.Matches left right u v e' := by
  unfold EdgeAllocation.selected
  rw [List.find?_eq_some_iff_append]
  simp only [decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  constructor
  · rintro ⟨hm, as, bs, hs, hall⟩
    exact ⟨hm, fun e' he' => hall e' ((split_lt hs e').mpr he')⟩
  · rintro ⟨hm, hall⟩
    obtain ⟨as, bs, hs⟩ := List.append_of_mem (List.mem_finRange e)
    exact ⟨hm, as, bs, hs, fun e' he' => hall e' ((split_lt hs e').mp he')⟩

/-- An earlier edge joins the endpoints of `e`. -/
def Earlier (left right : Fin m → Fin n) (e : Fin m) : Prop :=
  ∃ e' < e, EdgeAllocation.Matches left right (left e) (right e) e'

instance (left right : Fin m → Fin n) (e : Fin m) : Decidable (Earlier left right e) :=
  inferInstanceAs (Decidable (∃ e', e' < e ∧ EdgeAllocation.Matches left right (left e) (right e) e'))

theorem matches_swap (left right : Fin m → Fin n) (u v : Fin n) (e : Fin m) :
    EdgeAllocation.Matches left right u v e ↔ EdgeAllocation.Matches left right v u e := by
  unfold EdgeAllocation.Matches
  tauto

theorem selected_iff (left right : Fin m → Fin n) (e : Fin m) (pr : Fin n × Fin n) :
    EdgeAllocation.selected left right (List.finRange m) pr.1 pr.2 = some e ↔
      (pr = (left e, right e) ∨ pr = (right e, left e)) ∧ ¬ Earlier left right e := by
  rw [selected_finRange_iff]
  obtain ⟨u, v⟩ := pr
  simp only [Prod.mk.injEq]
  unfold Earlier
  constructor
  · rintro ⟨hm, hall⟩
    have hp : (u = left e ∧ v = right e) ∨ (u = right e ∧ v = left e) := by
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    refine ⟨hp, ?_⟩
    rintro ⟨e', he', hm'⟩
    apply hall e' he'
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hm'
    · exact (matches_swap left right _ _ e').mp hm'
  · rintro ⟨hp, hn⟩
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Or.inl ⟨rfl, rfl⟩, fun e' he' hm' => hn ⟨e', he', hm'⟩⟩
    · exact ⟨Or.inr ⟨rfl, rfl⟩, fun e' he' hm' =>
        hn ⟨e', he', (matches_swap left right _ _ e').mp hm'⟩⟩

/-! ## Collapsing the pair sum -/

/-- The natural transport entry of an ordered pair. -/
abbrev T (left right : Fin m → Fin n) (weights : Fin n → ℚ) (u v : Fin n) : ℕ :=
  (IntegerEdgeCosts.transport left right (List.finRange n) weights u v).toNat

/-- Only the two orientations of the endpoints contribute, and only for the
first edge joining them. -/
theorem integerCost_local (left right : Fin m → Fin n) (weights : Fin n → ℚ) (e : Fin m) :
    IntegerEdgeCosts.integerCost left right (List.finRange m) (List.finRange n) weights e =
      if Earlier left right e then 0 else
        T left right weights (left e) (right e) +
          if left e = right e then 0 else T left right weights (right e) (left e) := by
  unfold IntegerEdgeCosts.integerCost
  by_cases hE : Earlier left right e
  · rw [ite_eq_left hE]
    apply Finset.sum_eq_zero
    intro pr _
    rw [ite_eq_right]
    rw [selected_iff]
    exact fun h => h.2 hE
  · rw [ite_eq_right hE]
    set a := left e
    set b := right e
    have hpt : ∀ pr : Fin n × Fin n,
        (if EdgeAllocation.selected left right (List.finRange m) pr.1 pr.2 = some e then
          T left right weights pr.1 pr.2 else 0) =
        (if (a, b) = pr then T left right weights pr.1 pr.2 else 0) +
          (if (b, a) = pr then (if a = b then 0 else T left right weights pr.1 pr.2) else 0) := by
      intro pr
      have key := selected_iff left right e pr
      by_cases h1 : pr = (a, b)
      · subst h1
        have hs := key.mpr ⟨Or.inl rfl, hE⟩
        rw [ite_eq_left hs]
        by_cases hab : a = b
        · simp [hab]
        · simp [hab]
      · by_cases h2 : pr = (b, a)
        · subst h2
          have hs := key.mpr ⟨Or.inr rfl, hE⟩
          have hab : a ≠ b := fun h => h1 (by rw [h])
          rw [ite_eq_left hs]
          simp [hab, Ne.symm hab]
        · have hs : ¬ EdgeAllocation.selected left right (List.finRange m) pr.1 pr.2 = some e :=
            fun h => (key.mp h).1.elim h1 h2
          rw [ite_eq_right hs]
          simp [Ne.symm h1, Ne.symm h2]
    rw [Finset.sum_congr rfl (fun pr _ => hpt pr), Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]

/-! ## Transport from residual capacities -/

theorem networkResult_instance (adj : Fin n → Fin n → Prop) (i1 i2 : DecidableRel adj)
    (nodes : List (Fin n)) (w : Fin n → ℚ) :
    @MaxFlowPreprocessing.networkResult _ _ _ adj i1 nodes w =
      @MaxFlowPreprocessing.networkResult _ _ _ adj i2 nodes w := by
  rw [Subsingleton.elim i1 i2]

/-- The stored transport is the integer flow of the preprocessing network,
for the endpoint-adjacency instance used by the compiled preprocessing. -/
theorem transport_eq_flow (left right : Fin m → Fin n) (weights : Fin n → ℚ)
    (hw : ∀ v, 0 ≤ weights v) (u v : Fin n) :
    IntegerEdgeCosts.transport left right (List.finRange n) weights u v =
      (letI := RegisterPreprocessing.endpointAdj left right;
        MaxFlowPreprocessing.networkResult (EdgeTransport.Adj left right) (List.finRange n)
          (NegativeWeights.nonnegative weights)).flow
        (MaxFlowDual.leftNode u) (MaxFlowDual.rightNode v) := by
  have hnn : NegativeWeights.nonnegative weights = weights := by
    funext x
    simp [NegativeWeights.nonnegative, hw x]
  have href := congrArg (fun r => r.flow (MaxFlowDual.leftNode u) (MaxFlowDual.rightNode v))
    (CachedPreprocessing.networkResult_refines (EdgeTransport.Adj left right)
      (List.finRange n) (List.mem_finRange) weights)
  unfold IntegerEdgeCosts.transport
  rw [hnn]
  refine href.trans ?_
  rw [networkResult_instance]

/-- On an adjacent ordered pair the transport is `big` minus the residual
capacity of the arc from the left copy of `u` to the right copy of `v`. -/
theorem transport_eq_sub {W B w : ℕ} (left right : Fin m → Fin n) (weights : Fin n → ℚ)
    (hw : ∀ v, 0 ≤ weights v) (q : Fin n → BinaryRational.Word w)
    {words : ResidualListPhase.Result (W + 2) B}
    (hrep : letI := RegisterPreprocessing.endpointAdj left right;
      ResidualPhaseRefinement.Represents (nodeWord W) (nodes n)
        (matrix (EdgeTransport.Adj left right) (mu q)) sourceNode sinkNode words
        (MaxFlowPreprocessing.networkResult (EdgeTransport.Adj left right) (List.finRange n)
          (NegativeWeights.nonnegative weights))) :
    ∃ caps : Node (Fin n) → Node (Fin n) → Bits B,
      words.table = ((nodes n).product (nodes n)).map
        (ResidualCrossingRefinement.encodeArc (nodeWord W) caps) ∧
      ∀ u v, EdgeTransport.Adj left right u v →
        (caps (MaxFlowDual.leftNode u) (MaxFlowDual.rightNode v)).value ≤ big q ∧
        T left right weights u v =
          big q - (caps (MaxFlowDual.leftNode u) (MaxFlowDual.rightNode v)).value := by
  let _ := RegisterPreprocessing.endpointAdj left right
  obtain ⟨hf, caps, htab, hcap, -⟩ := hrep
  refine ⟨caps, htab, fun u v huv => ?_⟩
  set f := (MaxFlowPreprocessing.networkResult (EdgeTransport.Adj left right) (List.finRange n)
    (NegativeWeights.nonnegative weights)).flow
  have hc : matrix (EdgeTransport.Adj left right) (mu q) (MaxFlowDual.leftNode u)
      (MaxFlowDual.rightNode v) = big q := by
    simp only [matrix, MaxFlowDual.leftNode, MaxFlowDual.rightNode, ite_eq_left huv, big]
  have hcr : matrix (EdgeTransport.Adj left right) (mu q) (MaxFlowDual.rightNode v)
      (MaxFlowDual.leftNode u) = 0 := rfl
  have hval := hcap (MaxFlowDual.leftNode u) (MaxFlowDual.rightNode v)
  have hcast := MaxFlowResidual.matrix_cast _ _ _ f hf (MaxFlowDual.leftNode u)
    (MaxFlowDual.rightNode v)
  have hle := MaxFlowResidual.matrix_le _ _ _ f hf (MaxFlowDual.leftNode u)
    (MaxFlowDual.rightNode v)
  rw [hc, hcr] at hle
  rw [MaxFlowCore.residual, hc] at hcast
  rw [← hval] at hcast hle
  refine ⟨by simpa using hle, ?_⟩
  rw [T, transport_eq_flow left right weights hw u v]
  change (f (MaxFlowDual.leftNode u) (MaxFlowDual.rightNode v)).toNat = _
  omega

/-! ## The word-level computation -/

/-- The word `10·x` of the left copy of a vertex. -/
def leftWord {W : ℕ} (x : Bits W) : Bits (W + 2) := .cons true (.cons false x)

/-- The word `11·x` of the right copy of a vertex. -/
def rightWord {W : ℕ} (x : Bits W) : Bits (W + 2) := .cons true (.cons true x)

theorem leftWord_eq (W : ℕ) (v : Fin n) :
    leftWord (word W v.val) = nodeWord W (MaxFlowDual.leftNode v) := rfl

theorem rightWord_eq (W : ℕ) (v : Fin n) :
    rightWord (word W v.val) = nodeWord W (MaxFlowDual.rightNode v) := rfl

/-- `big` minus the residual capacity of the arc `10·x → 11·y`. -/
def termWord {W B : ℕ} (table : List (Arc (W + 2) B)) (big zero : Bits B) (x y : Bits W) :
    Bits B :=
  (Bits.subtract big (RegisterArcLookup.lookup (leftWord x) (rightWord y) zero table)).1

/-- The cost word of one edge record, given the reversed earlier records. -/
def costWord {W B : ℕ} (table : List (Arc (W + 2) B)) (big zero : Bits B)
    (pre : List (Bits W × Bits W)) (e : Bits W × Bits W) : Bits B :=
  if pre.any (edgeMatch e.1 e.2) then zero
  else if e.1 = e.2 then termWord table big zero e.1 e.2
  else (Bits.addCarry (termWord table big zero e.1 e.2) (termWord table big zero e.2 e.1)
    false).1

/-- The cost words of all records; `pre` holds the earlier records, reversed. -/
def costWords {W B : ℕ} (table : List (Arc (W + 2) B)) (big zero : Bits B) :
    List (Bits W × Bits W) → List (Bits W × Bits W) → List (Bits B)
  | _, [] => []
  | pre, e :: es => costWord table big zero pre e :: costWords table big zero (e :: pre) es

theorem earlier_words {W : ℕ} (hn : n < 2 ^ W) (left right : Fin m → Fin n) (e : Fin m)
    (as : List (Fin m)) (has : ∀ x, x ∈ as ↔ x < e) :
    (as.map fun x => (word W (left x).val, word W (right x).val)).reverse.any
        (edgeMatch (word W (left e).val) (word W (right e).val)) = true ↔
      Earlier left right e := by
  simp only [List.any_reverse, List.any_map, List.any_eq_true, Function.comp_apply]
  unfold Earlier
  constructor
  · rintro ⟨x, hx, hm⟩
    refine ⟨x, (has x).mp hx, ?_⟩
    simp only [edgeMatch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      word_eq_iff hn] at hm
    exact hm
  · rintro ⟨x, hx, hm⟩
    refine ⟨x, (has x).mpr hx, ?_⟩
    simp only [edgeMatch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      word_eq_iff hn]
    exact hm

section Costs

variable {W B w : ℕ} (hn : n < 2 ^ W) (left right : Fin m → Fin n) (weights : Fin n → ℚ)
  (q : Fin n → BinaryRational.Word w) (hB : 2 * big q < 2 ^ B)
  (caps : Node (Fin n) → Node (Fin n) → Bits B)
  (hcaps : ∀ u v, EdgeTransport.Adj left right u v →
    (caps (MaxFlowDual.leftNode u) (MaxFlowDual.rightNode v)).value ≤ big q ∧
    T left right weights u v =
      big q - (caps (MaxFlowDual.leftNode u) (MaxFlowDual.rightNode v)).value)

include hn hB hcaps in
theorem termWord_eq (u v : Fin n) (huv : EdgeTransport.Adj left right u v) :
    termWord (((nodes n).product (nodes n)).map
        (ResidualCrossingRefinement.encodeArc (nodeWord W) caps))
      (word B (big q)) (word B 0) (word W u.val) (word W v.val) =
      word B (T left right weights u v) := by
  unfold termWord
  rw [leftWord_eq, rightWord_eq, RegisterArcLookup.lookup_encoded (nodeWord W)
    (nodeWord_injective hn) caps _ _ _ _
    (show (MaxFlowDual.leftNode u, MaxFlowDual.rightNode v) ∈ (nodes n).product (nodes n) from
      List.mem_product.mpr ⟨nodes_complete n _, nodes_complete n _⟩)]
  obtain ⟨hle, hT⟩ := hcaps u v huv
  have hbig : (word B (big q)).value = big q := word_value (by omega)
  apply eq_word_of_value
  rw [(Bits.subtract_value_of_le _ _ (by rw [hbig]; exact hle)).2, hbig, hT]

include hcaps in
theorem T_le (u v : Fin n) (huv : EdgeTransport.Adj left right u v) :
    T left right weights u v ≤ big q := by
  rw [(hcaps u v huv).2]
  exact Nat.sub_le _ _

include hn hB hcaps in
/-- One edge: the word computed from its earlier records is its integer cost. -/
theorem costWord_eq (e : Fin m) (pre : List (Bits W × Bits W))
    (hpre : pre.any (edgeMatch (word W (left e).val) (word W (right e).val)) = true ↔
      Earlier left right e) :
    costWord (((nodes n).product (nodes n)).map
        (ResidualCrossingRefinement.encodeArc (nodeWord W) caps))
      (word B (big q)) (word B 0) pre (word W (left e).val, word W (right e).val) =
      word B (IntegerEdgeCosts.integerCost left right (List.finRange m) (List.finRange n)
        weights e) := by
  rw [integerCost_local]
  unfold costWord
  by_cases hE : Earlier left right e
  · rw [ite_eq_left (hpre.mpr hE), ite_eq_left hE]
  · rw [ite_eq_right (fun h => hE (hpre.mp h)), ite_eq_right hE]
    have hadj : EdgeTransport.Adj left right (left e) (right e) := ⟨e, Or.inl ⟨rfl, rfl⟩⟩
    have hadj' : EdgeTransport.Adj left right (right e) (left e) := ⟨e, Or.inr ⟨rfl, rfl⟩⟩
    simp only
    rw [termWord_eq hn left right weights q hB caps hcaps _ _ hadj]
    by_cases hab : left e = right e
    · rw [ite_eq_left ((word_eq_iff hn _ _).mpr hab), ite_eq_left hab, Nat.add_zero]
    · rw [ite_eq_right (fun h => hab ((word_eq_iff hn _ _).mp h)), ite_eq_right hab,
        termWord_eq hn left right weights q hB caps hcaps _ _ hadj']
      have h1 := T_le left right weights q caps hcaps _ _ hadj
      have h2 := T_le left right weights q caps hcaps _ _ hadj'
      have v1 : (word B (T left right weights (left e) (right e))).value =
          T left right weights (left e) (right e) := word_value (by omega)
      have v2 : (word B (T left right weights (right e) (left e))).value =
          T left right weights (right e) (left e) := word_value (by omega)
      apply eq_word_of_value
      have hadd := Bits.add_value_of_lt (word B (T left right weights (left e) (right e)))
        (word B (T left right weights (right e) (left e))) (by rw [v1, v2]; omega)
      unfold Bits.add at hadd
      rw [hadd.2, v1, v2]

include hn hB hcaps in
theorem costWords_suffix (as bs : List (Fin m)) (hs : List.finRange m = as ++ bs) :
    costWords (((nodes n).product (nodes n)).map
        (ResidualCrossingRefinement.encodeArc (nodeWord W) caps))
      (word B (big q)) (word B 0)
      (as.map fun x => (word W (left x).val, word W (right x).val)).reverse
      (bs.map fun x => (word W (left x).val, word W (right x).val)) =
      bs.map fun e => word B (IntegerEdgeCosts.integerCost left right (List.finRange m)
        (List.finRange n) weights e) := by
  induction bs generalizing as with
  | nil => rfl
  | cons e bs ih =>
    simp only [List.map_cons, costWords]
    rw [costWord_eq hn left right weights q hB caps hcaps e _
      (earlier_words hn left right e as (split_lt hs))]
    congr 1
    have := ih (as ++ [e]) (by rw [hs]; simp)
    simpa using this

include hn hB hcaps in
/-- All edges: the computed words are the canonical words of the integer costs. -/
theorem costWords_eq :
    costWords (((nodes n).product (nodes n)).map
        (ResidualCrossingRefinement.encodeArc (nodeWord W) caps))
      (word B (big q)) (word B 0) [] (edgeWords W left right) =
      (List.finRange m).map fun e => word B (IntegerEdgeCosts.integerCost left right
        (List.finRange m) (List.finRange n) weights e) :=
  costWords_suffix hn left right weights q hB caps hcaps [] (List.finRange m) rfl

end Costs

/-- Every integer edge cost fits below `2 * big`. -/
theorem integerCost_le {w : ℕ} (left right : Fin m → Fin n) (weights : Fin n → ℚ)
    (q : Fin n → BinaryRational.Word w) (e : Fin m)
    (hT : ∀ u v, EdgeTransport.Adj left right u v → T left right weights u v ≤ big q) :
    IntegerEdgeCosts.integerCost left right (List.finRange m) (List.finRange n) weights e ≤
      2 * big q := by
  rw [integerCost_local]
  have hadj : EdgeTransport.Adj left right (left e) (right e) := ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  have hadj' : EdgeTransport.Adj left right (right e) (left e) := ⟨e, Or.inr ⟨rfl, rfl⟩⟩
  have h1 := hT _ _ hadj
  have h2 := hT _ _ hadj'
  split_ifs <;> omega

end WeightedMIS.EdgeCostWords
