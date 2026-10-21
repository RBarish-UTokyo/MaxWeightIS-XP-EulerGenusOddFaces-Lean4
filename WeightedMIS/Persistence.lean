module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.Linarith

/-!
# Weighted persistence for the fractional independent-set relaxation

This file formalizes the exchange argument in Lemma 4 of the manuscript.
Half-integrality and optimality are explicit hypotheses; this file does not prove
that a rational LP solver produces such a point.
-/

@[expose] public section

namespace WeightedMIS.Persistence

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An independent set for the specified adjacency relation. -/
def Independent (adj : V → V → Prop) (I : Finset V) : Prop :=
  ∀ u v, adj u v → u ∈ I → v ∈ I → False

/-- The ordinary fractional independent-set constraints, including vertex bounds. -/
def Feasible (adj : V → V → Prop) (z : V → ℚ) : Prop :=
  (∀ v, 0 ≤ z v ∧ z v ≤ 1) ∧ ∀ u v, adj u v → z u + z v ≤ 1

/-- Half-integrality is an explicit premise of the persistence argument. -/
def HalfIntegral (z : V → ℚ) : Prop :=
  ∀ v, z v = 0 ∨ z v = 1 / 2 ∨ z v = 1

/-- The rational indicator vector of a finite set. -/
def indicator (I : Finset V) (v : V) : ℚ := if v ∈ I then 1 else 0

/-- Linear objective of a rational vertex vector. -/
def objective (w x : V → ℚ) : ℚ := ∑ v, w v * x v

/-- Weight of a finite vertex set. -/
def weight (w : V → ℚ) (I : Finset V) : ℚ := objective w (indicator I)

/-- Optimality among all rational feasible points of the relaxation. -/
def Optimal (adj : V → V → Prop) (w z : V → ℚ) : Prop :=
  Feasible adj z ∧ ∀ x, Feasible adj x → objective w x ≤ objective w z

/-- Retain all vertices with LP value one, and retain the old independent set
only on vertices with LP value one half. -/
def replacement (z : V → ℚ) (I : Finset V) : Finset V :=
  Finset.univ.filter fun v => z v = 1 ∨ (z v = 1 / 2 ∧ v ∈ I)

@[simp] theorem mem_replacement (z : V → ℚ) (I : Finset V) (v : V) :
    v ∈ replacement z I ↔ z v = 1 ∨ (z v = 1 / 2 ∧ v ∈ I) := by
  simp [replacement]

/-- The exchange candidate is the half-step in the direction used in the
manuscript's weighted persistence argument. -/
def perturb (z : V → ℚ) (I : Finset V) (v : V) : ℚ :=
  z v + (indicator I v - indicator (replacement z I) v) / 2

/-- Feasibility alone excludes edges inside the value-one set and from the
value-one set to the value-one-half set. -/
theorem replacement_independent (adj : V → V → Prop) (z : V → ℚ)
    (I : Finset V) (hz : Feasible adj z) (hI : Independent adj I) :
    Independent adj (replacement z I) := by
  intro u v huv hu hv
  have he := hz.2 u v huv
  rw [mem_replacement] at hu hv
  rcases hu with hu | ⟨hu, hIu⟩ <;> rcases hv with hv | ⟨hv, hIv⟩
  · linarith
  · linarith
  · linarith
  · exact hI u v huv hIu hIv

/-- Both vertex bounds and every edge inequality hold for the exchange point. -/
theorem perturb_feasible (adj : V → V → Prop) (z : V → ℚ) (I : Finset V)
    (hz : Feasible adj z) (hh : HalfIntegral z) (hI : Independent adj I) :
    Feasible adj (perturb z I) := by
  constructor
  · intro v
    rcases hh v with hv | hv | hv <;> by_cases hIv : v ∈ I <;>
      simp [perturb, indicator, hv, hIv] <;> norm_num
  · intro u v huv
    have he := hz.2 u v huv
    have hi := hI u v huv
    rcases hh u with hu | hu | hu <;>
      rcases hh v with hv | hv | hv <;>
      by_cases hIu : u ∈ I <;> by_cases hIv : v ∈ I <;>
      simp_all [perturb, indicator] <;> norm_num at *

/-- The objective change is precisely half the difference of the two set weights. -/
theorem perturb_objective (w z : V → ℚ) (I : Finset V) :
    objective w (perturb z I) =
      objective w z + (weight w I - weight w (replacement z I)) / 2 := by
  unfold weight objective perturb
  simp_rw [mul_add, ← mul_div_assoc, mul_sub]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib]

/-- Weighted persistence in its exchange form: every independent set can be
replaced by one containing all value-one vertices and no value-zero vertices,
without decreasing its weight. No nonnegativity assumption on weights is needed. -/
theorem weighted_persistence (adj : V → V → Prop) (w z : V → ℚ)
    (I : Finset V) (hz : Optimal adj w z) (hh : HalfIntegral z)
    (hI : Independent adj I) :
    Independent adj (replacement z I) ∧ weight w I ≤ weight w (replacement z I) := by
  refine ⟨replacement_independent adj z I hz.1 hI, ?_⟩
  have hp := hz.2 (perturb z I) (perturb_feasible adj z I hz.1 hh hI)
  rw [perturb_objective] at hp
  linarith

/-- Feasibility on precisely the induced subgraph of half-valued vertices.
Values of `x` away from that induced subgraph have no significance. -/
def ResidualFeasible (adj : V → V → Prop) (z x : V → ℚ) : Prop :=
  (∀ v, z v = 1 / 2 → 0 ≤ x v ∧ x v ≤ 1) ∧
  ∀ u v, adj u v → z u = 1 / 2 → z v = 1 / 2 → x u + x v ≤ 1

/-- Extend a residual vector by fixing the integral coordinates of the LP point. -/
def extend (z x : V → ℚ) (v : V) : ℚ :=
  if z v = 1 / 2 then x v else z v

/-- The residual objective sums over half-valued vertices only. -/
def residualObjective (w z x : V → ℚ) : ℚ :=
  ∑ v, if z v = 1 / 2 then w v * x v else 0

/-- A feasible vector on the half-valued induced subgraph extends feasibly to the
original graph by fixing zeros and ones. -/
theorem extend_feasible (adj : V → V → Prop) (z x : V → ℚ)
    (hz : Feasible adj z) (hh : HalfIntegral z)
    (hx : ResidualFeasible adj z x) : Feasible adj (extend z x) := by
  constructor
  · intro v
    by_cases hv : z v = 1 / 2
    · simpa [extend, hv] using hx.1 v hv
    · simpa only [extend, ite_eq_right hv] using hz.1 v
  · intro u v huv
    have he := hz.2 u v huv
    rcases hh u with hu | hu | hu <;> rcases hh v with hv | hv | hv
    · simp [extend, hu, hv]
    · have hb := (hx.1 v hv).2
      simpa [extend, hu, hv] using hb
    · simp [extend, hu, hv]
    · have hb := (hx.1 u hu).2
      simpa [extend, hu, hv] using hb
    · simpa [extend, hu, hv] using hx.2 u v huv hu hv
    · linarith
    · simp [extend, hu, hv]
    · linarith
    · linarith

/-- Extension changes the full objective by exactly the residual objective change. -/
theorem extend_objective (w z x : V → ℚ) :
    objective w (extend z x) = objective w z +
      (residualObjective w z x - residualObjective w z (fun _ => 1 / 2)) := by
  unfold objective residualObjective
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : z v = 1 / 2
  · simp [extend, hv]
  · simp only [extend, ite_eq_right hv, sub_self, add_zero]

/-- The all-half vector is feasible and optimal for the residual relaxation. -/
theorem residual_half_optimal (adj : V → V → Prop) (w z : V → ℚ)
    (hz : Optimal adj w z) (hh : HalfIntegral z) :
    ResidualFeasible adj z (fun _ => 1 / 2) ∧
      ∀ x, ResidualFeasible adj z x →
        residualObjective w z x ≤ residualObjective w z (fun _ => 1 / 2) := by
  constructor
  · constructor
    · intro v _; norm_num
    · intro u v _ _ _; norm_num
  · intro x hx
    have he := hz.2 (extend z x) (extend_feasible adj z x hz.1 hh hx)
    rw [extend_objective] at he
    linarith

/-- The vertices fixed to one by the LP optimum. -/
def fixedSet (z : V → ℚ) : Finset V := Finset.univ.filter fun v => z v = 1

/-- Restrict an independent set to the half-valued vertices. -/
def residualSet (z : V → ℚ) (I : Finset V) : Finset V :=
  I.filter fun v => z v = 1 / 2

/-- The two pieces of a persistent set have disjoint weights. -/
theorem replacement_weight (w z : V → ℚ) (I : Finset V) :
    weight w (replacement z I) = weight w (fixedSet z) + weight w (residualSet z I) := by
  unfold weight objective
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h1 : z v = 1 <;> by_cases hh : z v = 1 / 2 <;> by_cases hi : v ∈ I <;>
    simp_all [indicator, fixedSet, residualSet]

theorem residualSet_independent (adj : V → V → Prop) (z : V → ℚ)
    (I : Finset V) (hI : Independent adj I) : Independent adj (residualSet z I) := by
  intro u v huv hu hv
  exact hI u v huv (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hv).1

theorem residualSet_supported (z : V → ℚ) (I : Finset V) :
    ∀ v ∈ residualSet z I, z v = 1 / 2 := by
  intro v hv
  exact (Finset.mem_filter.mp hv).2

theorem residualSet_eq_self (z : V → ℚ) (J : Finset V)
    (hJ : ∀ v ∈ J, z v = 1 / 2) : residualSet z J = J := by
  apply Finset.filter_eq_self.mpr
  exact hJ

set_option maxHeartbeats 400000 in
/-- The optimization form of weighted persistence: a maximum independent set
on the half-valued induced subgraph extends to a maximum independent set of the
original graph, with optimum weight equal to the fixed-one weight plus the
residual optimum. Existence of an LP half-integral optimum remains explicit. -/
theorem residual_maximum_extends (adj : V → V → Prop) (w z : V → ℚ)
    (hz : Optimal adj w z) (hh : HalfIntegral z) (J : Finset V)
    (hJ : Independent adj J) (hs : ∀ v ∈ J, z v = 1 / 2)
    (hm : ∀ K, Independent adj K → (∀ v ∈ K, z v = 1 / 2) → weight w K ≤ weight w J) :
    Independent adj (replacement z J) ∧
      weight w (replacement z J) = weight w (fixedSet z) + weight w J ∧
      ∀ I, Independent adj I → weight w I ≤ weight w (replacement z J) := by
  refine ⟨replacement_independent adj z J hz.1 hJ, ?_, ?_⟩
  · rw [replacement_weight, residualSet_eq_self z J hs]
  · intro I hI
    have hi : Independent adj (residualSet z I) := residualSet_independent adj z I hI
    have hsI : ∀ v ∈ residualSet z I, z v = 1 / 2 := residualSet_supported z I
    have hb : weight w (residualSet z I) ≤ weight w J := hm (residualSet z I) hi hsI
    have hp : weight w I ≤ weight w (replacement z I) :=
      (weighted_persistence adj w z I hz hh hI).2
    rw [replacement_weight] at hp
    rw [replacement_weight, residualSet_eq_self z J hs]
    linarith only [hb, hp]

end WeightedMIS.Persistence
