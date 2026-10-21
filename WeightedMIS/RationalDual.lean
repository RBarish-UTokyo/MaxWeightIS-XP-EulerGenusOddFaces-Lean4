module

public import WeightedMIS.LPDirections
public import WeightedMIS.Slack
public import WeightedMIS.WeightedHall
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic

/-!
# Nonnegative rational edge costs at an all-half optimum

The proof uses weighted Hall inequalities, denominator clearing, and finite
matching. Every argument takes place over the rationals and finite sets.
-/

@[expose] public section

namespace WeightedMIS.RationalDual

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The outgoing neighborhood of a finite set. -/
def neighbors (adj : V → V → Prop) [DecidableRel adj] (S : Finset V) : Finset V :=
  Finset.univ.filter fun v => ∃ u ∈ S, adj u v

@[simp] theorem mem_neighbors (adj : V → V → Prop) [DecidableRel adj]
    (S : Finset V) (v : V) : v ∈ neighbors adj S ↔ ∃ u ∈ S, adj u v := by
  simp [neighbors]

/-- The indicator objective equals the usual sum of weights in a set. -/
theorem weight_eq_sum (w : V → ℚ) (S : Finset V) :
    Persistence.weight w S = ∑ v ∈ S, w v := by
  simp [Persistence.weight, Persistence.objective, Persistence.indicator,
    mul_ite, Finset.sum_ite_mem]

/-- Optimality at all-half implies nonnegative vertex weights. -/
theorem weights_nonnegative (adj : V → V → Prop) (w : V → ℚ)
    (ho : Persistence.Optimal adj w (fun _ => 1 / 2)) : ∀ v, 0 ≤ w v := by
  intro v
  let d : V → ℚ := fun u => if u = v then -1 else 0
  have hd : LPDirections.Direction adj d := by
    intro a b _
    by_cases ha : a = v <;> by_cases hb : b = v <;> simp [d, ha, hb]
  have hm := LPDirections.nonpositive_direction adj w ho d hd
  have he : Persistence.objective w d = -w v := by
    simp [Persistence.objective, d, mul_ite]
  rw [he] at hm
  linarith

/-- A symmetric graph at an all-half optimum satisfies every weighted Hall
inequality. The direction is the indicator of the set minus that of its
neighborhood. -/
theorem weighted_hall (adj : V → V → Prop) [DecidableRel adj]
    (hsym : Symmetric adj) (w : V → ℚ)
    (ho : Persistence.Optimal adj w (fun _ => 1 / 2)) (S : Finset V) :
    ∑ u ∈ S, w u ≤ ∑ v ∈ neighbors adj S, w v := by
  let d : V → ℚ := fun v => Persistence.indicator S v -
    Persistence.indicator (neighbors adj S) v
  have hd : LPDirections.Direction adj d := by
    intro u v huv
    have hforward : u ∈ S → v ∈ neighbors adj S := fun hu =>
      (mem_neighbors adj S v).2 ⟨u, hu, huv⟩
    have hback : v ∈ S → u ∈ neighbors adj S := fun hv =>
      (mem_neighbors adj S u).2 ⟨v, hv, hsym huv⟩
    have hf : Persistence.indicator S u ≤ Persistence.indicator (neighbors adj S) v := by
      by_cases hu : u ∈ S
      · have hv := hforward hu
        simp only [Persistence.indicator, ite_eq_left hu, ite_eq_left hv, le_refl]
      · simp only [Persistence.indicator, ite_eq_right hu]
        split_ifs <;> norm_num
    have hb : Persistence.indicator S v ≤ Persistence.indicator (neighbors adj S) u := by
      by_cases hv : v ∈ S
      · have hu := hback hv
        simp only [Persistence.indicator, ite_eq_left hv, ite_eq_left hu, le_refl]
      · simp only [Persistence.indicator, ite_eq_right hv]
        split_ifs <;> norm_num
    dsimp [d]
    linarith only [hf, hb]
  have hm := LPDirections.nonpositive_direction adj w ho d hd
  have he : Persistence.objective w d = Persistence.weight w S -
      Persistence.weight w (neighbors adj S) := by
    unfold Persistence.weight Persistence.objective
    dsimp [d]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [he, weight_eq_sum, weight_eq_sum] at hm
  linarith

/-- A single positive natural denominator clears every nonnegative rational
weight simultaneously. -/
theorem clear_denominators (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) :
    ∃ D : ℕ, 0 < D ∧ ∃ μ : V → ℕ, ∀ v, (μ v : ℚ) = (D : ℚ) * w v := by
  classical
  let D : ℕ := ∏ v, (w v).den
  have hD : 0 < D := Finset.prod_pos fun v _ => (w v).den_pos
  have hdvd (v : V) : (w v).den ∣ D :=
    Finset.dvd_prod_of_mem (fun u => (w u).den) (Finset.mem_univ v)
  choose k hk using hdvd
  let μ : V → ℕ := fun v => (w v).num.natAbs * k v
  refine ⟨D, hD, μ, ?_⟩
  intro v
  have hn : ((w v).num.natAbs : ℚ) = ((w v).num : ℚ) := by
    calc
      ((w v).num.natAbs : ℚ) = (((w v).num.natAbs : ℤ) : ℚ) := by simp
      _ = ((w v).num : ℚ) := congrArg (fun z : ℤ => (z : ℚ))
        (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr (hw v)))
  have hd : (D : ℚ) = ((w v).den : ℚ) * (k v : ℚ) := by exact_mod_cast hk v
  have hden : ((w v).den : ℚ) ≠ 0 := by exact_mod_cast (w v).den_ne_zero
  have hmul : ((w v).num : ℚ) = w v * ((w v).den : ℚ) :=
    (div_eq_iff hden).mp (Rat.num_div_den (w v))
  dsimp [μ]
  rw [Nat.cast_mul, hn, hmul, hd]
  ring

/-- Clearing denominators transports weighted Hall inequalities to natural
weights, with no rounding or approximation. -/
theorem scaled_weighted_hall (adj : V → V → Prop) [DecidableRel adj]
    (w : V → ℚ) (D : ℕ) (hD : 0 < D) (μ : V → ℕ)
    (hμ : ∀ v, (μ v : ℚ) = (D : ℚ) * w v)
    (hh : ∀ S : Finset V, ∑ u ∈ S, w u ≤ ∑ v ∈ neighbors adj S, w v) :
    ∀ S : Finset V, ∑ u ∈ S, μ u ≤ ∑ v ∈ neighbors adj S, μ v := by
  intro S
  have he (T : Finset V) : ((∑ v ∈ T, μ v : ℕ) : ℚ) =
      (D : ℚ) * ∑ v ∈ T, w v := by
    simp only [Nat.cast_sum, hμ, Finset.mul_sum]
  have hm : ((∑ u ∈ S, μ u : ℕ) : ℚ) ≤
      ((∑ v ∈ neighbors adj S, μ v : ℕ) : ℚ) := by
    rw [he, he]
    exact mul_le_mul_of_nonneg_left (hh S) (by exact_mod_cast hD.le)
  exact_mod_cast hm

/-- An all-half optimum supplies a nonnegative rational transportation matrix
supported on adjacency, with both marginals equal to the vertex weights. -/
theorem exists_rational_transport (adj : V → V → Prop) [DecidableRel adj]
    (hsym : Symmetric adj) (w : V → ℚ)
    (ho : Persistence.Optimal adj w (fun _ => 1 / 2)) :
    ∃ flow : V → V → ℚ,
      (∀ u v, 0 ≤ flow u v) ∧
      (∀ u v, ¬ adj u v → flow u v = 0) ∧
      (∀ u, ∑ v, flow u v = w u) ∧ (∀ v, ∑ u, flow u v = w v) := by
  obtain ⟨D, hD, μ, hμ⟩ := clear_denominators w (weights_nonnegative adj w ho)
  have hh := scaled_weighted_hall adj w D hD μ hμ (weighted_hall adj hsym w ho)
  have hh' : ∀ S : Finset V, ∑ u ∈ S, μ u ≤ ∑ v ∈ WeightedHall.neighbors adj S, μ v := hh
  obtain ⟨f, hf, hr, hc⟩ := WeightedHall.exists_transport adj μ hh'
  let flow : V → V → ℚ := fun u v => (f u v : ℚ) / (D : ℚ)
  have hDq : 0 < (D : ℚ) := by exact_mod_cast hD
  refine ⟨flow, ?_, ?_, ?_, ?_⟩
  · intro u v
    exact div_nonneg (Nat.cast_nonneg _) hDq.le
  · intro u v huv
    simp [flow, hf u v huv]
  · intro u
    change (∑ v, (f u v : ℚ) / (D : ℚ)) = w u
    rw [← Finset.sum_div, ← Nat.cast_sum, hr, hμ]
    field_simp
  · intro v
    change (∑ u, (f u v : ℚ) / (D : ℚ)) = w v
    rw [← Finset.sum_div, ← Nat.cast_sum, hc, hμ]
    field_simp

end WeightedMIS.RationalDual
