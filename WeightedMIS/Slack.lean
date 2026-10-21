module

public import Mathlib

/-!
# Integer edge slacks and threshold recovery

This file formalizes Lemma 5 of *Maximum-weight independent set in
embedded graphs parameterized by Euler genus and number of odd faces*.  A
finite multigraph is given
by its two endpoint maps.  Parallel edges are retained.  No connectivity or
embedding assumption is needed for this lemma.

The final theorem proves attainment of both optima and equality of their
values.  In particular the minimization permits arbitrary nonnegative integer
slacks; the minimizing witness supplied here has binary slack.
-/

public section

namespace WeightedMIS.Slack

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- An independent vertex set, using the two endpoint maps of a multigraph. -/
@[expose] def Independent (left right : E → V) (I : Finset V) : Prop :=
  ∀ e, ¬ (left e ∈ I ∧ right e ∈ I)

/-- Integer vectors satisfying the edge inequalities; no vertex bounds occur. -/
@[expose] def Feasible (left right : E → V) (x : V → ℤ) : Prop :=
  ∀ e, x (left e) + x (right e) ≤ 1

/-- The integer characteristic function of a finite vertex set. -/
@[expose] def indicator (I : Finset V) (v : V) : ℤ :=
  if v ∈ I then 1 else 0

/-- Threshold recovery selects the vertices whose integer coordinate is positive. -/
@[expose] def threshold (x : V → ℤ) : Finset V :=
  Finset.univ.filter fun v => 1 ≤ x v

/-- The edge slack `1 - x_u - x_v`. -/
@[expose] def slack (left right : E → V) (x : V → ℤ) (e : E) : ℤ :=
  1 - x (left e) - x (right e)

/-- The sum of the rational edge costs. -/
@[expose] def totalCost (cost : E → ℚ) : ℚ := ∑ e, cost e

/-- The objective of an integer edge-slack vector. -/
@[expose] def slackCost (left right : E → V) (cost : E → ℚ)
    (x : V → ℤ) : ℚ := ∑ e, cost e * (slack left right x e : ℚ)

/-- The nonnegative vertex weights induced by edge costs, counting endpoints. -/
@[expose] def vertexWeight (left right : E → V) (cost : E → ℚ) (v : V) : ℚ :=
  (∑ e, if left e = v then cost e else 0) +
  (∑ e, if right e = v then cost e else 0)

/-- Weight of a vertex set under the incidence-induced vertex weights. -/
@[expose] def setWeight (left right : E → V) (cost : E → ℚ) (I : Finset V) : ℚ :=
  ∑ v ∈ I, vertexWeight left right cost v

/-- The edge-incidence expression for the objective of an integer vertex vector. -/
@[expose] def edgeObjective (left right : E → V) (cost : E → ℚ)
    (x : V → ℤ) : ℚ :=
  ∑ e, cost e * ((x (left e) : ℚ) + (x (right e) : ℚ))

omit [DecidableEq V] in
theorem threshold_mem (x : V → ℤ) (v : V) :
    v ∈ threshold x ↔ 1 ≤ x v := by
  simp [threshold]

omit [Fintype V] in
theorem indicator_binary (I : Finset V) (v : V) :
    indicator I v = 0 ∨ indicator I v = 1 := by
  unfold indicator
  split_ifs <;> simp

omit [Fintype V] [Fintype E] in
theorem independent_indicator_feasible (left right : E → V) (I : Finset V)
    (hI : Independent left right I) : Feasible left right (indicator I) := by
  intro e
  have h := hI e
  unfold indicator
  split_ifs <;> simp_all

omit [Fintype V] [Fintype E] in
theorem independent_binary_slack (left right : E → V) (I : Finset V)
    (hI : Independent left right I) (e : E) :
    slack left right (indicator I) e = 0 ∨
      slack left right (indicator I) e = 1 := by
  have h := hI e
  unfold slack indicator
  split_ifs <;> simp_all

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem feasible_iff_slack_nonnegative (left right : E → V) (x : V → ℤ) :
    Feasible left right x ↔ ∀ e, 0 ≤ slack left right x e := by
  unfold Feasible slack
  constructor <;> intro h e <;> have := h e <;> omega

omit [Fintype E] [DecidableEq V] in
theorem threshold_independent (left right : E → V) (x : V → ℤ)
    (hx : Feasible left right x) : Independent left right (threshold x) := by
  intro e he
  have hl := (threshold_mem x (left e)).mp he.1
  have hr := (threshold_mem x (right e)).mp he.2
  have hedge := hx e
  omega

omit [Fintype E] in
/-- Threshold rounding improves the sum at the endpoints of each edge. -/
theorem threshold_edge_domination (left right : E → V) (x : V → ℤ)
    (hx : Feasible left right x) (e : E) :
    x (left e) + x (right e) ≤
      indicator (threshold x) (left e) + indicator (threshold x) (right e) := by
  have hedge := hx e
  simp only [indicator, threshold_mem]
  split_ifs <;> omega

omit [Fintype V] [DecidableEq V] in
theorem slack_cost_identity (left right : E → V) (cost : E → ℚ) (x : V → ℤ) :
    slackCost left right cost x = totalCost cost - edgeObjective left right cost x := by
  unfold slackCost totalCost edgeObjective slack
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

omit [Fintype V] in
theorem set_weight_incidence (left right : E → V) (cost : E → ℚ) (I : Finset V) :
    setWeight left right cost I = edgeObjective left right cost (indicator I) := by
  classical
  unfold setWeight vertexWeight edgeObjective
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (s := I)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp [indicator, mul_add, mul_ite]

omit [Fintype V] in
theorem vertex_weight_nonnegative (left right : E → V) (cost : E → ℚ)
    (hcost : ∀ e, 0 ≤ cost e) (v : V) : 0 ≤ vertexWeight left right cost v := by
  unfold vertexWeight
  apply add_nonneg <;> apply Finset.sum_nonneg <;> intro e _ <;>
    split_ifs <;> simp_all

/-- Feasible integer vectors can be rounded to independent sets without
decreasing the incidence-induced vertex objective. -/
theorem threshold_weight_domination (left right : E → V) (cost : E → ℚ)
    (hcost : ∀ e, 0 ≤ cost e) (x : V → ℤ) (hx : Feasible left right x) :
    totalCost cost - slackCost left right cost x ≤
      setWeight left right cost (threshold x) := by
  rw [slack_cost_identity, set_weight_incidence]
  simp only [sub_sub_cancel]
  unfold edgeObjective
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (hcost e)
  exact_mod_cast threshold_edge_domination left right x hx e

omit [Fintype V] in
theorem independent_cost_identity (left right : E → V) (cost : E → ℚ)
    (I : Finset V) :
    slackCost left right cost (indicator I) = totalCost cost - setWeight left right cost I := by
  rw [slack_cost_identity, set_weight_incidence]

/-- Every finite graph with rational vertex weights induced by edge costs has
an independent set of maximum weight. Nonnegativity is not needed here. -/
theorem exists_maximum_independent (left right : E → V) (cost : E → ℚ) :
    ∃ I : Finset V, Independent left right I ∧
      ∀ J : Finset V, Independent left right J →
        setWeight left right cost J ≤ setWeight left right cost I := by
  classical
  let candidates := Finset.univ.filter (Independent left right)
  have hempty : (∅ : Finset V) ∈ candidates := by
    simp [candidates, Independent]
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image candidates
    (setWeight left right cost) ⟨∅, hempty⟩
  refine ⟨I, (Finset.mem_filter.mp hI).2, ?_⟩
  intro J hJ
  exact hmax J (by simp [candidates, hJ])

/-- Lemma 5, including attainment and binary optimal slack.

For nonnegative rational edge costs, there is an independent set whose
characteristic vector minimizes slack cost over *all* feasible integer
vertex vectors. Its slack is binary, and its weight is the total edge cost
minus that minimum. Thus unbounded feasible slacks are harmless.
-/
theorem integer_slack_optimum (left right : E → V) (cost : E → ℚ)
    (hcost : ∀ e, 0 ≤ cost e) :
    ∃ I : Finset V,
      Independent left right I ∧
      Feasible left right (indicator I) ∧
      (∀ e, slack left right (indicator I) e = 0 ∨
        slack left right (indicator I) e = 1) ∧
      (∀ J : Finset V, Independent left right J →
        setWeight left right cost J ≤ setWeight left right cost I) ∧
      (∀ x : V → ℤ, Feasible left right x →
        slackCost left right cost (indicator I) ≤ slackCost left right cost x) ∧
      setWeight left right cost I =
        totalCost cost - slackCost left right cost (indicator I) := by
  obtain ⟨I, hI, hmax⟩ := exists_maximum_independent left right cost
  refine ⟨I, hI, independent_indicator_feasible left right I hI,
    independent_binary_slack left right I hI, hmax, ?_, ?_⟩
  · intro x hx
    have hround := threshold_weight_domination left right cost hcost x hx
    have hbound := hmax (threshold x) (threshold_independent left right x hx)
    rw [independent_cost_identity]
    linarith
  · rw [independent_cost_identity]
    ring

/-- Recovery from an arbitrary minimizing integer vector, whose slack need
not be binary. This is the rounding step used after shortest-path optimization. -/
theorem minimizing_slack_recovers_optimum (left right : E → V) (cost : E → ℚ)
    (hcost : ∀ e, 0 ≤ cost e) (x : V → ℤ) (hx : Feasible left right x)
    (hmin : ∀ z : V → ℤ, Feasible left right z →
      slackCost left right cost x ≤ slackCost left right cost z) :
    Independent left right (threshold x) ∧
      ∀ J : Finset V, Independent left right J →
        setWeight left right cost J ≤ setWeight left right cost (threshold x) := by
  refine ⟨threshold_independent left right x hx, ?_⟩
  intro J hJ
  have hm := hmin (indicator J) (independent_indicator_feasible left right J hJ)
  have hr := threshold_weight_domination left right cost hcost x hx
  rw [independent_cost_identity] at hm
  linarith

end WeightedMIS.Slack
