module

public import WeightedMIS.EdgeAllocation
public import WeightedMIS.MaxFlowSize

/-!
# Uniform-denominator integer edge costs

The stored maximum-flow matrix already provides integral transport. Allocating
its entries directly yields natural edge costs with a single denominator 2D.
Their total is the sum of scaled vertex weights, giving explicit bit bounds.
-/

@[expose] public section

namespace WeightedMIS.IntegerEdgeCosts

open scoped BigOperators
open MaxFlowPreprocessing

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The actual stored integral transport entry. -/
def transport (left right : E → V) (nodes : List V) (w : V → ℚ) (u v : V) : ℤ :=
  MaxFlowCached.get
    (CachedPreprocessing.networkResult (EdgeTransport.Adj left right) nodes w).table
    (MaxFlowDual.leftNode u) (MaxFlowDual.rightNode v)

/-- Allocate the integral transport mass before division by the uniform denominator. -/
def integerCost (left right : E → V) (edges : List E) (nodes : List V)
    (w : V → ℚ) (e : E) : ℕ :=
  ∑ p : V × V, if EdgeAllocation.selected left right edges p.1 p.2 = some e then
    (transport left right nodes w p.1 p.2).toNat else 0

theorem transport_nonnegative (left right : E → V) (nodes : List V)
    (complete : ∀ v, v ∈ nodes) (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2))
    (u v : V) : 0 ≤ transport left right nodes w u v := by
  have ht := (CachedPreprocessing.rationalTransport_correct (EdgeTransport.Adj left right)
    (EdgeTransport.adj_symmetric left right) nodes complete w hw ho).1 u v
  have hd : (0 : ℚ) < denominator w := by exact_mod_cast denominator_positive w
  change 0 ≤ (transport left right nodes w u v : ℚ) / (denominator w : ℚ) at ht
  have hh := mul_nonneg ht hd.le
  rw [div_mul_cancel₀ _ (ne_of_gt hd)] at hh
  exact_mod_cast hh

/-- The rational edge cost is represented by an actual natural numerator and
one shared positive denominator. -/
theorem integerCost_exact (left right : E → V) (edges : List E) (nodes : List V)
    (complete : ∀ v, v ∈ nodes) (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2)) (e : E) :
    EdgeAllocation.computedCost left right edges nodes w e =
      (integerCost left right edges nodes w e : ℚ) / (2 * (denominator w : ℚ)) := by
  have hcast (u v : V) : ((transport left right nodes w u v).toNat : ℚ) =
      (transport left right nodes w u v : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (transport_nonnegative left right nodes complete w hw ho u v)
  simp only [EdgeAllocation.computedCost, EdgeAllocation.cost, integerCost, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_zero, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : EdgeAllocation.selected left right edges p.1 p.2 = some e
  · simp only [ite_eq_left hp, hcast, CachedPreprocessing.rationalTransport]
    change ((transport left right nodes w p.1 p.2 : ℚ) / denominator w) / 2 = _
    ring
  · simp [hp]

/-- The sum of natural edge numerators is exactly the scaled total vertex weight. -/
theorem integerCost_total (left right : E → V) (edges : List E)
    (edge_complete : ∀ e, e ∈ edges) (nodes : List V) (node_complete : ∀ v, v ∈ nodes)
    (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2)) :
    (∑ e, integerCost left right edges nodes w e) = ∑ v, scaledWeight w v := by
  have ht := EdgeAllocation.computedCost_total left right edges edge_complete nodes node_complete w hw ho
  simp_rw [integerCost_exact left right edges nodes node_complete w hw ho] at ht
  rw [← Finset.sum_div, ← Nat.cast_sum] at ht
  have hd : (0 : ℚ) < denominator w := by exact_mod_cast denominator_positive w
  have hs : ((∑ v, scaledWeight w v : ℕ) : ℚ) = (denominator w : ℚ) * ∑ v, w v := by
    simp only [Nat.cast_sum, scaledWeight_exact w hw, Finset.mul_sum]
  have he : ((∑ e, integerCost left right edges nodes w e : ℕ) : ℚ) =
      ((∑ v, scaledWeight w v : ℕ) : ℚ) := by
    rw [hs]
    field_simp at ht
    linarith
  exact_mod_cast he

/-- Every natural edge numerator has polynomial binary length. -/
theorem integerCost_le_pow (left right : E → V) (edges : List E)
    (edge_complete : ∀ e, e ∈ edges) (nodes : List V) (node_complete : ∀ v, v ∈ nodes)
    (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2))
    (B : ℕ) (hden : ∀ v, (w v).den ≤ 2 ^ B) (hnum : ∀ v, (w v).num.natAbs ≤ 2 ^ B)
    (e : E) : integerCost left right edges nodes w e ≤
      2 ^ (Fintype.card V + B * (Fintype.card V + 1)) := by
  calc
    _ ≤ ∑ e, integerCost left right edges nodes w e :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    _ = ∑ v, scaledWeight w v :=
      integerCost_total left right edges edge_complete nodes node_complete w hw ho
    _ ≤ ∑ _v : V, 2 ^ (B * (Fintype.card V + 1)) :=
      Finset.sum_le_sum fun v _ => MaxFlowSize.scaledWeight_le_pow w B hden hnum v
    _ = Fintype.card V * 2 ^ (B * (Fintype.card V + 1)) := by simp
    _ ≤ 2 ^ Fintype.card V * 2 ^ (B * (Fintype.card V + 1)) :=
      Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ = _ := by rw [pow_add]

/-- The shared denominator has polynomial binary length. -/
theorem uniform_denominator_le_pow (w : V → ℚ) (B : ℕ)
    (hden : ∀ v, (w v).den ≤ 2 ^ B) :
    2 * denominator w ≤ 2 ^ (B * Fintype.card V + 1) := by
  rw [pow_succ]
  nlinarith [MaxFlowSize.denominator_le_pow w B hden]

end WeightedMIS.IntegerEdgeCosts
