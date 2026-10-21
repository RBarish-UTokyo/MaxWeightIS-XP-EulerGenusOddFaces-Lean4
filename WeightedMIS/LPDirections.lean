module

public import WeightedMIS.Persistence
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The exact directional condition at an all-half LP optimum

The all-half point lies strictly inside every vertex bound. Its optimality is
therefore equivalent to nonpositivity of the objective on all directions
satisfying the homogeneous edge inequalities. This is the local geometric
step preceding dual-cone or LP-duality arguments; it does not assert the
existence or polynomial-time computation of dual edge costs.
-/

@[expose] public section

namespace WeightedMIS.LPDirections

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The homogeneous edge inequalities defining feasible directions at all-half. -/
def Direction (adj : V → V → Prop) (d : V → ℚ) : Prop :=
  ∀ u v, adj u v → d u + d v ≤ 0

/-- At an all-half optimum, every homogeneous edge-feasible direction has
nonpositive objective. A bounded positive scaling realizes the direction as
an ordinary feasible point, so no differentiability or separation axiom is used. -/
theorem nonpositive_direction (adj : V → V → Prop) (w : V → ℚ)
    (ho : Persistence.Optimal adj w (fun _ => 1 / 2)) (d : V → ℚ)
    (hd : Direction adj d) : Persistence.objective w d ≤ 0 := by
  let B : ℚ := 1 + ∑ v, |d v|
  have hB : 0 < B := by
    have hsum : 0 ≤ ∑ v, |d v| := Finset.sum_nonneg fun v _ => abs_nonneg (d v)
    dsimp [B]
    linarith
  have hden : 0 < 2 * B := mul_pos (by norm_num) hB
  have hb (v : V) : |d v| ≤ B := by
    have hsingle : |d v| ≤ ∑ u, |d u| :=
      Finset.single_le_sum (fun u _ => abs_nonneg (d u)) (Finset.mem_univ v)
    dsimp [B]
    linarith
  let x : V → ℚ := fun v => 1 / 2 + d v / (2 * B)
  have hx : Persistence.Feasible adj x := by
    constructor
    · intro v
      have hu : d v / (2 * B) ≤ 1 / 2 := (div_le_iff₀ hden).2 (by
        have ha := le_abs_self (d v)
        have ha' := hb v
        nlinarith)
      have hl : -(1 / 2) ≤ d v / (2 * B) := (le_div_iff₀ hden).2 (by
        have ha := neg_abs_le (d v)
        have ha' := hb v
        nlinarith)
      dsimp [x]
      constructor <;> linarith
    · intro u v huv
      have he : (d u + d v) / (2 * B) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (hd u v huv) hden.le
      have heq : x u + x v = 1 + (d u + d v) / (2 * B) := by dsimp [x]; ring
      rw [heq]
      linarith
  have hobj : Persistence.objective w x =
      Persistence.objective w (fun _ => 1 / 2) + Persistence.objective w d / (2 * B) := by
    unfold Persistence.objective
    dsimp [x]
    simp_rw [mul_add, ← mul_div_assoc]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_div]
  have hm := ho.2 x hx
  rw [hobj] at hm
  have hq : Persistence.objective w d / (2 * B) ≤ 0 := by linarith
  have hn := (div_le_iff₀ hden).1 hq
  simpa using hn

/-- The directional inequality is also sufficient for all-half optimality. -/
theorem half_optimal_of_nonpositive_directions (adj : V → V → Prop) (w : V → ℚ)
    (hd : ∀ d, Direction adj d → Persistence.objective w d ≤ 0) :
    Persistence.Optimal adj w (fun _ => 1 / 2) := by
  constructor
  · constructor
    · intro v; norm_num
    · intro u v _; norm_num
  · intro x hx
    let d : V → ℚ := fun v => x v - 1 / 2
    have hdir : Direction adj d := by
      intro u v huv
      have he := hx.2 u v huv
      dsimp [d]
      linarith
    have hm := hd d hdir
    have heq : Persistence.objective w d =
        Persistence.objective w x - Persistence.objective w (fun _ => 1 / 2) := by
      unfold Persistence.objective
      dsimp [d]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
    rw [heq] at hm
    linarith

/-- Exact algebraic characterization of optimality at the all-half point. -/
theorem half_optimal_iff (adj : V → V → Prop) (w : V → ℚ) :
    Persistence.Optimal adj w (fun _ => 1 / 2) ↔
      ∀ d, Direction adj d → Persistence.objective w d ≤ 0 :=
  ⟨fun ho d hd => nonpositive_direction adj w ho d hd,
    half_optimal_of_nonpositive_directions adj w⟩

end WeightedMIS.LPDirections
