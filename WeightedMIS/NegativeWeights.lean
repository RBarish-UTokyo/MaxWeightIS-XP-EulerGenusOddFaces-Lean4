module

public import WeightedMIS.Persistence
public import Mathlib.Tactic

/-!
# Removing negative weights

Replacing negative vertex weights by zero and then deleting the originally
negative vertices from an optimum set preserves the maximum weight. This is
the preprocessing operation at the start of Section 3.
-/

@[expose] public section

namespace WeightedMIS.NegativeWeights

open Persistence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Truncate each negative weight to zero. -/
def nonnegative (w : V → ℚ) (v : V) : ℚ := max (w v) 0

/-- Remove exactly the selected vertices whose original weight is negative. -/
def prune (w : V → ℚ) (I : Finset V) : Finset V := I.filter fun v => 0 ≤ w v

omit [Fintype V] [DecidableEq V] in
theorem nonnegative_nonnegative (w : V → ℚ) (v : V) : 0 ≤ nonnegative w v :=
  le_max_right _ _

omit [Fintype V] [DecidableEq V] in
/-- Removing vertices cannot violate independence. -/
theorem prune_independent (adj : V → V → Prop) (w : V → ℚ)
    (I : Finset V) (hI : Independent adj I) : Independent adj (prune w I) := by
  intro u v huv hu hv
  exact hI u v huv (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hv).1

/-- The retained original weight equals the entire set's truncated weight. -/
theorem prune_weight (w : V → ℚ) (I : Finset V) :
    weight w (prune w I) = weight (nonnegative w) I := by
  unfold weight objective
  apply Finset.sum_congr rfl
  intro v _
  by_cases hi : v ∈ I <;> by_cases hw : 0 ≤ w v
  · simp [indicator, prune, hi, hw, nonnegative]
  · have hle : w v ≤ 0 := le_of_lt (lt_of_not_ge hw)
    simp [indicator, prune, hi, hw, nonnegative, max_eq_right hle]
  · simp [indicator, prune, hi]
  · simp [indicator, prune, hi]

/-- Truncation cannot decrease any fixed independent-set objective. -/
theorem weight_le_truncated (w : V → ℚ) (I : Finset V) :
    weight w I ≤ weight (nonnegative w) I := by
  unfold weight objective
  apply Finset.sum_le_sum
  intro v _
  by_cases hi : v ∈ I
  · simp only [indicator, ite_eq_left hi, mul_one]
    exact le_max_left _ _
  · simp [indicator, hi]

/-- An optimum for truncated weights yields an optimum for the original
weights by the concrete pruning operation. -/
theorem optimum_of_truncated (adj : V → V → Prop) (w : V → ℚ)
    (I : Finset V) (hI : Independent adj I)
    (hmax : ∀ J, Independent adj J → weight (nonnegative w) J ≤ weight (nonnegative w) I) :
    Independent adj (prune w I) ∧
      ∀ J, Independent adj J → weight w J ≤ weight w (prune w I) := by
  refine ⟨prune_independent adj w I hI, ?_⟩
  intro J hJ
  rw [prune_weight]
  exact (weight_le_truncated w J).trans (hmax J hJ)

end WeightedMIS.NegativeWeights
