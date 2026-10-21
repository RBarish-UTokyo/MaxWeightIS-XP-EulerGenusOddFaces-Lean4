module

public import WeightedMIS.RationalDual

/-!
# The bipartite double cover and half-integral preprocessing

A vertex cover of the bipartite double cover is a pair of vertex subsets.
A minimum such cover yields a half-integral optimum of the original fractional
independent-set polytope. The comparison with every rational feasible point is
proved by a finite threshold decomposition.
-/

@[expose] public section

namespace WeightedMIS.DoubleCover

open scoped BigOperators
open Persistence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex cover of the double cover: its two sides are independent copies. -/
def Cover (adj : V → V → Prop) (A B : Finset V) : Prop :=
  ∀ u v, adj u v → u ∈ A ∨ v ∈ B

/-- The total weight on the two copies. -/
def coverCost (w : V → ℚ) (A B : Finset V) : ℚ :=
  objective w (fun v => indicator A v + indicator B v)

/-- Averaging the complements of the two copies produces an original vector. -/
def rounded (A B : Finset V) (v : V) : ℚ :=
  1 - (indicator A v + indicator B v) / 2

/-- The averaged vector is half-integral. -/
theorem rounded_half_integral (A B : Finset V) : HalfIntegral (rounded A B) := by
  intro v
  unfold rounded indicator
  split_ifs <;> norm_num

/-- Symmetry makes the two directed cover inequalities jointly feasible. -/
theorem rounded_feasible (adj : V → V → Prop) (hsym : Symmetric adj)
    (A B : Finset V) (hcover : Cover adj A B) : Feasible adj (rounded A B) := by
  constructor
  · intro v
    unfold rounded indicator
    split_ifs <;> norm_num
  · intro u v huv
    have hc := hcover u v huv
    have hd := hcover v u (hsym huv)
    unfold rounded indicator
    split_ifs <;> simp_all <;> norm_num

/-- Objective and cover cost are complementary. -/
theorem rounded_objective (w : V → ℚ) (A B : Finset V) :
    objective w (rounded A B) = (∑ v, w v) - coverCost w A B / 2 := by
  simp only [coverCost, objective, rounded]
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- A uniform threshold is selected exactly as often as its integral height. -/
theorem threshold_count (D m : ℕ) (hm : m ≤ D) :
    (∑ k ∈ Finset.range D, if k < m then (1 : ℚ) else 0) = m := by
  rw [← Finset.sum_filter]
  have hf : (Finset.range D).filter (fun k => k < m) = Finset.range m := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf]
  simp

/-- The reversed thresholds have the same marginal count. -/
theorem reverse_threshold_count (D m : ℕ) (hm : m ≤ D) :
    (∑ k ∈ Finset.range D, if D ≤ m + k then (1 : ℚ) else 0) = m := by
  have hi (k : ℕ) : (if D ≤ m + k then (1 : ℚ) else 0) =
      1 - (if k < D - m then (1 : ℚ) else 0) := by
    by_cases hk : k < D - m
    · have hn : ¬ D ≤ m + k := by omega
      simp [hk, hn]
    · have hy : D ≤ m + k := by omega
      simp [hk, hy]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, threshold_count D (D - m) (Nat.sub_le _ _)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have he : ((D - m : ℕ) : ℚ) = (D : ℚ) - (m : ℚ) := Nat.cast_sub hm
  rw [he]
  ring

/-- The two threshold sets are covers whenever their heights satisfy the
fractional cover inequality. -/
theorem threshold_cover (adj : V → V → Prop) (D : ℕ) (μ : V → ℕ)
    (hμ : ∀ u v, adj u v → D ≤ μ u + μ v) (k : ℕ) :
    Cover adj (Finset.univ.filter fun v => k < μ v)
      (Finset.univ.filter fun v => D ≤ μ v + k) := by
  intro u v huv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h := hμ u v huv
  omega

/-- The sum of threshold-cover costs is the exact scaled fractional cost. -/
theorem threshold_cost_sum (w : V → ℚ) (D : ℕ) (μ : V → ℕ)
    (hμ : ∀ v, μ v ≤ D) :
    (∑ k ∈ Finset.range D, coverCost w
      (Finset.univ.filter fun v => k < μ v)
      (Finset.univ.filter fun v => D ≤ μ v + k)) =
      2 * ∑ v, w v * (μ v : ℚ) := by
  simp only [coverCost, objective]
  rw [Finset.sum_comm]
  calc
    _ = ∑ v, 2 * (w v * (μ v : ℚ)) := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [indicator, Finset.mem_filter, Finset.mem_univ, true_and]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        threshold_count D (μ v) (hμ v), reverse_threshold_count D (μ v) (hμ v)]
      ring
    _ = _ := by rw [Finset.mul_sum]

/-- Every minimum double-cover vertex cover beats every rational fractional
cover. Its averaged complement is therefore an LP optimum. -/
theorem optimal_of_minimum_cover (adj : V → V → Prop) (hsym : Symmetric adj)
    (w : V → ℚ) (A B : Finset V) (hc : Cover adj A B)
    (hmin : ∀ C D, Cover adj C D → coverCost w A B ≤ coverCost w C D) :
    Optimal adj w (rounded A B) := by
  refine ⟨rounded_feasible adj hsym A B hc, ?_⟩
  intro x hx
  let q : V → ℚ := fun v => 1 - x v
  have hq : ∀ v, 0 ≤ q v := fun v => by dsimp [q]; linarith [(hx.1 v).2]
  obtain ⟨D, hD, μ, hμ⟩ := RationalDual.clear_denominators q hq
  have hDq : 0 < (D : ℚ) := by exact_mod_cast hD
  have hμle : ∀ v, μ v ≤ D := by
    intro v
    have hle : (μ v : ℚ) ≤ (D : ℚ) := by
      rw [hμ]
      have hh : q v ≤ 1 := by dsimp [q]; linarith [(hx.1 v).1]
      nlinarith
    exact_mod_cast hle
  have hμedge : ∀ u v, adj u v → D ≤ μ u + μ v := by
    intro u v huv
    have hh : (D : ℚ) ≤ (μ u : ℚ) + (μ v : ℚ) := by
      rw [hμ, hμ]
      have he : 1 ≤ q u + q v := by dsimp [q]; linarith [hx.2 u v huv]
      nlinarith
    exact_mod_cast hh
  have hh := Finset.sum_le_sum (s := Finset.range D) fun k _ =>
    hmin _ _ (threshold_cover adj D μ hμedge k)
  rw [threshold_cost_sum w D μ hμle] at hh
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
  have hscale : (∑ v, w v * (μ v : ℚ)) = (D : ℚ) * objective w q := by
    simp only [hμ, objective, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hscale] at hh
  have hcost : coverCost w A B ≤ 2 * objective w q := by nlinarith
  have hobj : objective w q = (∑ v, w v) - objective w x := by
    simp only [objective, q, mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hobj] at hcost
  rw [rounded_objective]
  linarith

/-- Capacity of an internal crossing in the standard double-cover network. -/
def largeCapacity (w : V → ℚ) : ℚ := 1 + ∑ v, w v

/-- Number of internal arcs crossing the cut represented by a pair of sets. -/
def violations (adj : V → V → Prop) [DecidableRel adj] (A B : Finset V) : ℚ :=
  ∑ u, ∑ v, if adj u v ∧ u ∉ A ∧ v ∉ B then 1 else 0

/-- The actual cut capacity: terminal arcs plus crossing internal arcs. -/
def cutCapacity (adj : V → V → Prop) [DecidableRel adj] (w : V → ℚ)
    (A B : Finset V) : ℚ := coverCost w A B + largeCapacity w * violations adj A B

theorem coverCost_nonnegative (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) (A B : Finset V) :
    0 ≤ coverCost w A B := by
  apply Finset.sum_nonneg
  intro v _
  apply mul_nonneg (hw v)
  simp only [indicator]
  split_ifs <;> norm_num

theorem violations_nonnegative (adj : V → V → Prop) [DecidableRel adj]
    (A B : Finset V) : 0 ≤ violations adj A B := by
  apply Finset.sum_nonneg
  intro u _
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> norm_num

theorem cover_violations (adj : V → V → Prop) [DecidableRel adj]
    (A B : Finset V) (hc : Cover adj A B) : violations adj A B = 0 := by
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  have h : ¬ (adj u v ∧ u ∉ A ∧ v ∉ B) := by
    rintro ⟨huv, hu, hv⟩
    exact (hc u v huv).elim hu hv
  simp only [ite_eq_right h]

theorem noncover_violations (adj : V → V → Prop) [DecidableRel adj]
    (A B : Finset V) (hc : ¬ Cover adj A B) : 1 ≤ violations adj A B := by
  classical
  obtain ⟨u, v, huv, hu, hv⟩ : ∃ u v, adj u v ∧ u ∉ A ∧ v ∉ B := by
    simpa only [Cover, not_forall, not_imp, not_or, exists_prop] using hc
  calc
    1 = (if adj u v ∧ u ∉ A ∧ v ∉ B then (1 : ℚ) else 0) := by simp [huv, hu, hv]
    _ ≤ ∑ b, if adj u b ∧ u ∉ A ∧ b ∉ B then (1 : ℚ) else 0 := by
      apply Finset.single_le_sum (fun b _ => ?_) (Finset.mem_univ v)
      split_ifs <;> norm_num
    _ ≤ violations adj A B := by
      apply Finset.single_le_sum (fun a _ => ?_) (Finset.mem_univ u)
      apply Finset.sum_nonneg
      intro b _
      split_ifs <;> norm_num

theorem cutCapacity_of_cover (adj : V → V → Prop) [DecidableRel adj]
    (w : V → ℚ) (A B : Finset V) (hc : Cover adj A B) :
    cutCapacity adj w A B = coverCost w A B := by
  simp only [cutCapacity, cover_violations adj A B hc, mul_zero, add_zero]

/-- An actual minimum network cut crosses no internal arc. -/
theorem minimum_cut_is_cover (adj : V → V → Prop) [DecidableRel adj]
    (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) (A B : Finset V)
    (hmin : ∀ C D, cutCapacity adj w A B ≤ cutCapacity adj w C D) : Cover adj A B := by
  have hbase : cutCapacity adj w Finset.univ ∅ = ∑ v, w v := by
    rw [cutCapacity_of_cover adj w _ _ (by intro u v _; exact Or.inl (Finset.mem_univ u))]
    simp [coverCost, objective, indicator]
  have hbound := hmin Finset.univ ∅
  rw [hbase] at hbound
  by_contra hn
  have hv := noncover_violations adj A B hn
  have hc := coverCost_nonnegative w hw A B
  have htotal : 0 ≤ ∑ v, w v := Finset.sum_nonneg fun v _ => hw v
  have hlarge : 0 < largeCapacity w := by unfold largeCapacity; linarith
  unfold cutCapacity at hbound
  have hprod : largeCapacity w ≤ largeCapacity w * violations adj A B := by nlinarith
  unfold largeCapacity at hprod hbound
  linarith

/-- Minimum-cut preprocessing is half-integral and optimal, without computing
an extreme point or appealing to a general linear-programming algorithm. -/
theorem optimal_of_minimum_cut (adj : V → V → Prop) [DecidableRel adj]
    (hsym : Symmetric adj) (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) (A B : Finset V)
    (hmin : ∀ C D, cutCapacity adj w A B ≤ cutCapacity adj w C D) :
    HalfIntegral (rounded A B) ∧ Optimal adj w (rounded A B) := by
  have hc := minimum_cut_is_cover adj w hw A B hmin
  refine ⟨rounded_half_integral A B, optimal_of_minimum_cover adj hsym w A B hc ?_⟩
  intro C D hCD
  have hh := hmin C D
  rwa [cutCapacity_of_cover adj w A B hc, cutCapacity_of_cover adj w C D hCD] at hh

end WeightedMIS.DoubleCover
