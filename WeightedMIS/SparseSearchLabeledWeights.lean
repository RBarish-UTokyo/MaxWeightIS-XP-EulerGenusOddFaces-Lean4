module

public import WeightedMIS.SparseSearchLabeledPath

/-!
# Original rational costs for encoded search labels

The decoded result of sparse search minimizes the rational costs actually
computed by the integral transport preprocessing.
-/

@[expose] public section

namespace WeightedMIS.SparseSearchGraph.Labeled

open Expanded NodeEncoding EfficientSearch

variable {Label : Type*} {r m d : ℕ}
variable (η : Option (Fin m) → Label) (δ : Label → Option (Fin m))
variable (hδ : ∀ label, δ (η label) = label)

include hδ in
/-- The recovered path minimizes rational costs with a shared denominator. -/
theorem solve_scaled_minimum (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ)
    (D : ℚ) (hD : 0 < D)
    (s t : Node (Fin r) (Fin d) radius) (reachable : Nonempty (Path C W π radius s t)) :
    ∃ distance trace, ∃ p : Path C W π radius s t,
      (recover (solve (graph η C W π radius w) (nodeKey s)) (nodeKey t)).1 =
        some (distance, trace) ∧
      p.labels = traceLabels δ trace ∧
      p.cost (fun e => (w e : ℚ) / D) = (distance.value : ℚ) / D ∧
      ∀ q : Path C W π radius s t,
        p.cost (fun e => (w e : ℚ) / D) ≤ q.cost (fun e => (w e : ℚ) / D) := by
  obtain ⟨distance, trace, p, hout, hp, hcost, hmin, _hwork⟩ :=
    solve_expanded_minimum η δ hδ C W π radius w s t reachable
  refine ⟨distance, trace, p, hout, hp, ?_, ?_⟩
  · rw [path_cost_scaled, hcost]
  · intro q
    rw [path_cost_scaled, path_cost_scaled]
    apply div_le_div_of_nonneg_right _ hD.le
    exact_mod_cast hmin q

include hδ in
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
      (recover (solve (graph η C W π radius
        (IntegerEdgeCosts.integerCost left right edges nodes weights)) (nodeKey s)) (nodeKey t)).1 =
        some (distance, trace) ∧
      p.labels = traceLabels δ trace ∧
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
  exact solve_scaled_minimum η δ hδ C W π radius _ _ hD s t reachable


end WeightedMIS.SparseSearchGraph.Labeled
