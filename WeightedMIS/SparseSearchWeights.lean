module

public import WeightedMIS.SparseSearchPath
public import WeightedMIS.EncodingCost

/-!
# Uniform-denominator costs and word lengths for sparse search

The search compares integral cost numerators. Dividing by the same positive
denominator preserves every path comparison and recovers the rational edge
costs computed by the flow preprocessing.
-/

@[expose] public section

namespace WeightedMIS.SparseSearchGraph

open Expanded NodeEncoding EfficientSearch

variable {r m d : ℕ}

theorem path_cost_scaled {C : Fin m → Walks.Column (Fin r)}
    {W : Fin m → Fin d → ℤ} {π : Fin m → ZMod 2} {radius : ℕ}
    {s t : Node (Fin r) (Fin d) radius} (p : Path C W π radius s t)
    (w : Fin m → ℕ) (D : ℚ) :
    p.cost (fun e => (w e : ℚ) / D) = (((p.labels.map w).sum : ℕ) : ℚ) / D := by
  unfold Path.cost
  induction p.labels with
  | nil => simp
  | cons e es ih => simp [ih, add_div]

/-- The recovered path minimizes rational costs with a shared denominator. -/
theorem solve_scaled_minimum (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ)
    (D : ℚ) (hD : 0 < D)
    (s t : Node (Fin r) (Fin d) radius) (reachable : Nonempty (Path C W π radius s t)) :
    ∃ distance trace, ∃ p : Path C W π radius s t,
      (recover (solve (graph C W π radius w) (nodeKey s)) (nodeKey t)).1 =
        some (distance, trace) ∧
      p.labels = traceLabels trace ∧
      p.cost (fun e => (w e : ℚ) / D) = (distance.value : ℚ) / D ∧
      ∀ q : Path C W π radius s t,
        p.cost (fun e => (w e : ℚ) / D) ≤ q.cost (fun e => (w e : ℚ) / D) := by
  obtain ⟨distance, trace, p, hout, hp, hcost, hmin, _hwork⟩ :=
    solve_expanded_minimum C W π radius w s t reachable
  refine ⟨distance, trace, p, hout, hp, ?_, ?_⟩
  · rw [path_cost_scaled, hcost]
  · intro q
    rw [path_cost_scaled, path_cost_scaled]
    apply div_le_div_of_nonneg_right _ hD.le
    exact_mod_cast hmin q

/-- The exact natural edge costs produced by the integral transport routine
give the minimum path for its original rational edge costs. -/
theorem solve_computedCost_minimum {n : ℕ}
    (left right : Fin m → Fin n) (edges : List (Fin m)) (nodes : List (Fin n))
    (complete : ∀ v, v ∈ nodes) (weights : Fin n → ℚ) (hw : ∀ v, 0 ≤ weights v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2))
    (C : Fin m → Walks.Column (Fin r)) (W : Fin m → Fin d → ℤ)
    (π : Fin m → ZMod 2) (radius : ℕ)
    (s t : Node (Fin r) (Fin d) radius) (reachable : Nonempty (Path C W π radius s t)) :
    ∃ distance trace, ∃ p : Path C W π radius s t,
      (recover (solve (graph C W π radius
        (IntegerEdgeCosts.integerCost left right edges nodes weights)) (nodeKey s)) (nodeKey t)).1 =
        some (distance, trace) ∧
      p.labels = traceLabels trace ∧
      p.cost (EdgeAllocation.computedCost left right edges nodes weights) =
        (distance.value : ℚ) / (2 * (MaxFlowPreprocessing.denominator weights : ℚ)) ∧
      ∀ q : Path C W π radius s t,
        p.cost (EdgeAllocation.computedCost left right edges nodes weights) ≤
          q.cost (EdgeAllocation.computedCost left right edges nodes weights) := by
  have hD : (0 : ℚ) < 2 * (MaxFlowPreprocessing.denominator weights : ℚ) := by
    have hd : (0 : ℚ) < MaxFlowPreprocessing.denominator weights := by
      exact_mod_cast MaxFlowPreprocessing.denominator_positive weights
    positivity
  have hcost : EdgeAllocation.computedCost left right edges nodes weights =
      fun e => (IntegerEdgeCosts.integerCost left right edges nodes weights e : ℚ) /
        (2 * (MaxFlowPreprocessing.denominator weights : ℚ)) := by
    funext e
    exact IntegerEdgeCosts.integerCost_exact left right edges nodes complete weights hw ho e
  rw [hcost]
  exact solve_scaled_minimum C W π radius _ _ hD s t reachable

theorem size_add_one_le (a : ℕ) : (a + 1).size ≤ a.size + 1 := by
  apply Nat.size_le.mpr
  have h := Nat.lt_size_self a
  have hp : 0 < 2 ^ a.size := by positivity
  rw [pow_succ]
  omega

theorem size_add_two_le (a : ℕ) : (a + 2).size ≤ a.size + 2 := by
  apply Nat.size_le.mpr
  have h := Nat.lt_size_self a
  have hp : 0 < 2 ^ a.size := by positivity
  rw [pow_succ, pow_succ]
  omega

/-- Vertex words grow linearly with the signature dimension and logarithmically
with the radius and number of local rows. -/
theorem vertexWidth_le (r d radius : ℕ) :
    vertexWidth r d radius ≤ d * (4 * radius + 1).size + 2 * (2 * r + 1).size + 5 := by
  have h₁ := EncodingCost.size_mul_le (2 * (4 * radius + 1) ^ d) (1 + (2 * r + 1) ^ 2)
  have h₂ := EncodingCost.size_mul_le 2 ((4 * radius + 1) ^ d)
  have hp := EncodingCost.size_pow_le (4 * radius + 1) d
  have hq := EncodingCost.size_pow_le (2 * r + 1) 2
  have ha := size_add_one_le ((2 * r + 1) ^ 2)
  have htwo : (2 : ℕ).size = 2 := by decide
  rw [htwo] at h₂
  simp only [vertexWidth, nodeCount]
  rw [Nat.add_comm ((2 * r + 1) ^ 2) 1] at ha
  omega

/-- Distance words have the input cost width plus the logarithmic graph size. -/
theorem costWidth_le (r d radius : ℕ) (w : Fin m → ℕ) (B : ℕ)
    (hw : weightBound w ≤ 2 ^ B) :
    costWidth r d radius w ≤ vertexWidth r d radius + (2 * r + 2 * m + 2).size + B + 3 := by
  have h₁ := EncodingCost.size_mul_le (entryBound r m d radius + 2) (weightBound w)
  have h₂ := size_add_two_le (entryBound r m d radius)
  have h₃ := EncodingCost.size_mul_le (nodeCount r d radius) (2 * r + 2 * m + 2)
  have hws : (weightBound w).size ≤ B + 1 := by
    apply Nat.size_le.mpr
    have hp : 0 < 2 ^ B := by positivity
    rw [pow_succ]
    omega
  change ((entryBound r m d radius + 2) * weightBound w).size ≤ _
  change (entryBound r m d radius).size ≤ vertexWidth r d radius + _ at h₃
  omega

/-- The sum of actual edge-cost numerators has polynomial binary length in
 the original rational weights. -/
theorem integerCost_weightBound {n : ℕ}
    (left right : Fin m → Fin n) (edges : List (Fin m))
    (edge_complete : ∀ e, e ∈ edges) (nodes : List (Fin n))
    (node_complete : ∀ v, v ∈ nodes) (weights : Fin n → ℚ)
    (hw : ∀ v, 0 ≤ weights v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2))
    (B : ℕ) (hden : ∀ v, (weights v).den ≤ 2 ^ B)
    (hnum : ∀ v, (weights v).num.natAbs ≤ 2 ^ B) :
    weightBound (IntegerEdgeCosts.integerCost left right edges nodes weights) ≤
      2 ^ (n + B * (n + 1)) := by
  unfold weightBound
  rw [IntegerEdgeCosts.integerCost_total left right edges edge_complete nodes node_complete
    weights hw ho]
  calc
    _ ≤ ∑ _v : Fin n, 2 ^ (B * (n + 1)) := by
      apply Finset.sum_le_sum
      intro v _
      simpa using MaxFlowSize.scaledWeight_le_pow weights B hden hnum v
    _ = n * 2 ^ (B * (n + 1)) := by simp
    _ ≤ 2 ^ n * 2 ^ (B * (n + 1)) :=
      Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ = _ := by rw [pow_add]

/-- The actual search word width is bounded by dimensions, box radius, and
 the input rational bit bound. -/
theorem computedCost_width_le {n : ℕ}
    (left right : Fin m → Fin n) (edges : List (Fin m))
    (edge_complete : ∀ e, e ∈ edges) (nodes : List (Fin n))
    (node_complete : ∀ v, v ∈ nodes) (weights : Fin n → ℚ)
    (hw : ∀ v, 0 ≤ weights v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2))
    (B : ℕ) (hden : ∀ v, (weights v).den ≤ 2 ^ B)
    (hnum : ∀ v, (weights v).num.natAbs ≤ 2 ^ B) (r d radius : ℕ) :
    costWidth r d radius (IntegerEdgeCosts.integerCost left right edges nodes weights) ≤
      d * (4 * radius + 1).size + 2 * (2 * r + 1).size +
        (2 * r + 2 * m + 2).size + n + B * (n + 1) + 8 := by
  have h := costWidth_le r d radius _ _
    (integerCost_weightBound left right edges edge_complete nodes node_complete weights hw ho
      B hden hnum)
  have hv := vertexWidth_le r d radius
  omega

end WeightedMIS.SparseSearchGraph
