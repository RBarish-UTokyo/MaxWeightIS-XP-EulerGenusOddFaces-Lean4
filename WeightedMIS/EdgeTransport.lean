module

public import WeightedMIS.RationalDual

/-!
# Extracting nonnegative rational edge costs

A transportation matrix supported on the undirected adjacency relation is
allocated to the original edge labels. Each ordered pair contributes half its
flow; hence incidence sums are the average of its two marginals. Parallel edges
and loops are retained by the endpoint representation.
-/

@[expose] public section

namespace WeightedMIS.EdgeTransport

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- Undirected adjacency defined by the actual edge endpoints. -/
def Adj (left right : E → V) (u v : V) : Prop :=
  ∃ e, (left e = u ∧ right e = v) ∨ (left e = v ∧ right e = u)

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem adj_symmetric (left right : E → V) : Symmetric (Adj left right) := by
  rintro u v ⟨e, h | h⟩
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩

/-- Summing allocated masses over a property of their target labels. -/
theorem allocate_fiber {P : Type*} [Fintype P] [DecidableEq E]
    (pick : P → E) (mass : P → ℚ) (test : E → Prop) [DecidablePred test] :
    (∑ e, if test e then (∑ p, if pick p = e then mass p else 0) else 0) =
      ∑ p, if test (pick p) then mass p else 0 := by
  calc
    _ = ∑ e, ∑ p, if pick p = e then (if test e then mass p else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : test e <;> simp [he]
    _ = ∑ p, ∑ e, if pick p = e then (if test e then mass p else 0) else 0 :=
      Finset.sum_comm
    _ = _ := by simp

/-- Two equal marginals yield exactly the prescribed incidence weights. -/
theorem flow_to_edge_costs (left right : E → V) (w : V → ℚ)
    (flow : V → V → ℚ) (hflow : ∀ u v, 0 ≤ flow u v)
    (hsupport : ∀ u v, ¬ Adj left right u v → flow u v = 0)
    (hrow : ∀ u, ∑ v, flow u v = w u)
    (hcol : ∀ v, ∑ u, flow u v = w v) :
    ∃ cost : E → ℚ, (∀ e, 0 ≤ cost e) ∧
      ∀ v, Slack.vertexWeight left right cost v = w v := by
  classical
  let P := {p : V × V // Adj left right p.1 p.2}
  let pick : P → E := fun p => Classical.choose p.property
  have hpick (p : P) :
      (left (pick p) = p.val.1 ∧ right (pick p) = p.val.2) ∨
      (left (pick p) = p.val.2 ∧ right (pick p) = p.val.1) :=
    Classical.choose_spec p.property
  let cost : E → ℚ := fun e => ∑ p : P,
    if pick p = e then flow p.val.1 p.val.2 / 2 else 0
  refine ⟨cost, ?_, ?_⟩
  · intro e
    apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact div_nonneg (hflow _ _) (by norm_num)
    · rfl
  · intro v
    let g : V × V → ℚ := fun p =>
      (if p.1 = v then flow p.1 p.2 / 2 else 0) +
      (if p.2 = v then flow p.1 p.2 / 2 else 0)
    have hallocated : Slack.vertexWeight left right cost v = ∑ p : P, g p.val := by
      unfold Slack.vertexWeight
      change (∑ e, if left e = v then (∑ p : P,
        if pick p = e then flow p.val.1 p.val.2 / 2 else 0) else 0) +
        (∑ e, if right e = v then (∑ p : P,
        if pick p = e then flow p.val.1 p.val.2 / 2 else 0) else 0) = _
      rw [allocate_fiber, allocate_fiber, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      rcases hpick p with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · simp [g, hl, hr]
      · simp [g, hl, hr, add_comm]
    have hsub : (∑ p : P, g p.val) = ∑ p : V × V, g p := by
      rw [← Finset.sum_subtype
        (Finset.univ.filter fun p : V × V => Adj left right p.1 p.2)
        (by intro p; simp) g, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : Adj left right p.1 p.2
      · simp [hp]
      · simp [hp, g, hsupport _ _ hp]
    rw [hallocated, hsub, Fintype.sum_prod_type]
    simp_rw [g, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_div, ← Finset.sum_div, hrow, hcol]
    ring

/-- Full rational dual extraction for the all-half optimum on the given finite
multigraph. The edge costs are proved to exist from optimality alone. -/
theorem edge_costs_of_half_optimal (left right : E → V) (w : V → ℚ)
    (ho : Persistence.Optimal (Adj left right) w (fun _ => 1 / 2)) :
    ∃ cost : E → ℚ, (∀ e, 0 ≤ cost e) ∧
      ∀ v, Slack.vertexWeight left right cost v = w v := by
  classical
  obtain ⟨flow, hn, hs, hr, hc⟩ := RationalDual.exists_rational_transport
    (Adj left right) (adj_symmetric left right) w ho
  exact flow_to_edge_costs left right w flow hn hs hr hc

end WeightedMIS.EdgeTransport
