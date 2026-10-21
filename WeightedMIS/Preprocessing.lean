module

public import WeightedMIS.HalfIntegral
public import WeightedMIS.Persistence
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Half-integral weighted preprocessing

This module combines the proved half-integrality theorem with weighted
persistence. Its input is an actual optimal extreme point of the rational
fractional independent-set polytope. Existence of that point is established
in `LPExistence`; its polynomial-time construction remains unproved.
-/

public section

namespace WeightedMIS.Preprocessing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A rational extreme point satisfies the half-integrality predicate used by
weighted persistence. -/
theorem extreme_half_integral (adj : V → V → Prop) (z : V → ℚ)
    (he : z ∈ (HalfIntegral.polytope adj).extremePoints ℚ) :
    Persistence.HalfIntegral z :=
  HalfIntegral.extreme_point_half_integral adj z he

/-- Every independent set can be replaced without weight loss at an actual
optimal extreme point of the fractional independent-set relaxation. -/
theorem extreme_weighted_persistence (adj : V → V → Prop) (w z : V → ℚ)
    (I : Finset V) (ho : Persistence.Optimal adj w z)
    (he : z ∈ (HalfIntegral.polytope adj).extremePoints ℚ)
    (hI : Persistence.Independent adj I) :
    Persistence.Independent adj (Persistence.replacement z I) ∧
      Persistence.weight w I ≤ Persistence.weight w (Persistence.replacement z I) :=
  Persistence.weighted_persistence adj w z I ho (extreme_half_integral adj z he) hI

/-- The residual all-half vector is optimal after preprocessing at an actual
optimal extreme point. -/
theorem extreme_residual_half_optimal (adj : V → V → Prop) (w z : V → ℚ)
    (ho : Persistence.Optimal adj w z)
    (he : z ∈ (HalfIntegral.polytope adj).extremePoints ℚ) :
    Persistence.ResidualFeasible adj z (fun _ => 1 / 2) ∧
      ∀ x, Persistence.ResidualFeasible adj z x →
        Persistence.residualObjective w z x ≤
          Persistence.residualObjective w z (fun _ => 1 / 2) :=
  Persistence.residual_half_optimal adj w z ho (extreme_half_integral adj z he)

/-- A residual maximum extends to an original maximum, with exactly the fixed
one-vertex weight added. This combines Lemmas 3 and 4 without an independent
half-integrality assumption. -/
theorem extreme_residual_maximum_extends (adj : V → V → Prop) (w z : V → ℚ)
    (ho : Persistence.Optimal adj w z)
    (he : z ∈ (HalfIntegral.polytope adj).extremePoints ℚ) (J : Finset V)
    (hJ : Persistence.Independent adj J) (hs : ∀ v ∈ J, z v = 1 / 2)
    (hm : ∀ K, Persistence.Independent adj K → (∀ v ∈ K, z v = 1 / 2) →
      Persistence.weight w K ≤ Persistence.weight w J) :
    Persistence.Independent adj (Persistence.replacement z J) ∧
      Persistence.weight w (Persistence.replacement z J) =
        Persistence.weight w (Persistence.fixedSet z) + Persistence.weight w J ∧
      ∀ I, Persistence.Independent adj I →
        Persistence.weight w I ≤ Persistence.weight w (Persistence.replacement z J) :=
  Persistence.residual_maximum_extends adj w z ho (extreme_half_integral adj z he) J hJ hs hm

end WeightedMIS.Preprocessing
