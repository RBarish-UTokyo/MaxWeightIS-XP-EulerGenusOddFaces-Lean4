module

public import WeightedMIS.MaxFlowPreprocessing

/-!
# Dual transport from the computed double-cover flow

A saturated feasible flow through the actual three-layer network is a
nonnegative transport matrix with the prescribed row and column sums. The
transport is read directly from the flow; its entries are not chosen by an
existence argument.
-/

@[expose] public section

namespace WeightedMIS.MaxFlowDual

open scoped BigOperators
open DoubleCoverNetwork MaxFlowCore MaxFlowPreprocessing

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj] (μ : V → ℕ)

def leftNode (v : V) : Node V := .inr (false, v)
def rightNode (v : V) : Node V := .inr (true, v)

theorem flow_zero {f : Node V → Node V → ℤ}
    (hf : Feasible (matrix adj μ) sourceNode sinkNode f)
    (u v : Node V) (huv : matrix adj μ u v = 0) (hvu : matrix adj μ v u = 0) :
    f u v = 0 := by
  have h1 := hf.2.1 u v
  have h2 := hf.2.1 v u
  have h3 := hf.1 u v
  rw [huv, Nat.cast_zero] at h1
  rw [hvu, Nat.cast_zero] at h2
  omega

theorem source_value {f : Node V → Node V → ℤ}
    (hf : Feasible (matrix adj μ) sourceNode sinkNode f) :
    value f sourceNode = ∑ u, f sourceNode (leftNode u) := by
  have hs : ∀ b, f sourceNode (.inl b) = 0 := by
    intro b
    apply flow_zero adj μ hf <;> cases b <;> rfl
  have hr : ∀ v, f sourceNode (rightNode v) = 0 := by
    intro v
    apply flow_zero adj μ hf <;> rfl
  simp only [value, divergence, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, hs, zero_add, add_zero]
  change (∑ v, f sourceNode (rightNode v)) + (∑ u, f sourceNode (leftNode u)) = _
  simp only [hr, Finset.sum_const_zero, zero_add]

theorem transport_nonnegative {f : Node V → Node V → ℤ}
    (hf : Feasible (matrix adj μ) sourceNode sinkNode f) (u v : V) :
    0 ≤ f (leftNode u) (rightNode v) := by
  have h := hf.2.1 (rightNode v) (leftNode u)
  have he := hf.1 (leftNode u) (rightNode v)
  change f (rightNode v) (leftNode u) ≤ 0 at h
  omega

theorem transport_supported {f : Node V → Node V → ℤ}
    (hf : Feasible (matrix adj μ) sourceNode sinkNode f) (u v : V) (h : ¬ adj u v) :
    f (leftNode u) (rightNode v) = 0 := by
  apply flow_zero adj μ hf <;> simp [matrix, leftNode, rightNode, h]

theorem transport_row {f : Node V → Node V → ℤ}
    (hf : Feasible (matrix adj μ) sourceNode sinkNode f) (u : V) :
    (∑ v, f (leftNode u) (rightNode v)) = f sourceNode (leftNode u) := by
  have hc := hf.2.2 (leftNode u) (by simp [leftNode, sourceNode])
    (by simp [leftNode, sinkNode])
  have ht : f (leftNode u) sinkNode = 0 := by
    apply flow_zero adj μ hf <;> rfl
  have hl : ∀ v, f (leftNode u) (leftNode v) = 0 := by
    intro v
    apply flow_zero adj μ hf <;> rfl
  simp only [divergence, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool] at hc
  change f (leftNode u) sinkNode + f (leftNode u) sourceNode +
    ((∑ v, f (leftNode u) (rightNode v)) + (∑ v, f (leftNode u) (leftNode v))) = 0 at hc
  rw [ht] at hc
  simp only [hl, Finset.sum_const_zero, zero_add, add_zero] at hc
  have hs := hf.1 (leftNode u) sourceNode
  omega

theorem transport_column {f : Node V → Node V → ℤ}
    (hf : Feasible (matrix adj μ) sourceNode sinkNode f) (v : V) :
    (∑ u, f (leftNode u) (rightNode v)) = f (rightNode v) sinkNode := by
  have hc := hf.2.2 (rightNode v) (by simp [rightNode, sourceNode])
    (by simp [rightNode, sinkNode])
  have hs : f (rightNode v) sourceNode = 0 := by
    apply flow_zero adj μ hf <;> rfl
  have hr : ∀ u, f (rightNode v) (rightNode u) = 0 := by
    intro u
    apply flow_zero adj μ hf <;> rfl
  simp only [divergence, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool] at hc
  change f (rightNode v) sinkNode + f (rightNode v) sourceNode +
    ((∑ u, f (rightNode v) (rightNode u)) + (∑ u, f (rightNode v) (leftNode u))) = 0 at hc
  rw [hs] at hc
  simp only [hr, Finset.sum_const_zero, zero_add, add_zero] at hc
  have hsk : (∑ u, f (rightNode v) (leftNode u)) =
      -(∑ u, f (leftNode u) (rightNode v)) := by
    simp only [hf.1 (rightNode v), Finset.sum_neg_distrib]
  rw [hsk] at hc
  omega

/-- Equality of total capacity forces equality on every bounded coordinate. -/
theorem saturated_coordinates {ι : Type*} [Fintype ι] (a b : ι → ℤ)
    (hle : ∀ i, a i ≤ b i) (hsum : (∑ i, a i) = ∑ i, b i) : ∀ i, a i = b i := by
  have hz : (∑ i, (b i - a i)) = 0 := by rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ b i - a i := fun i _ => sub_nonneg.mpr (hle i)
  have hh := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz
  intro i
  have := hh i (Finset.mem_univ i)
  omega

/-- The saturated network directly yields all dual transport constraints. -/
theorem saturated_transport {f : Node V → Node V → ℤ}
    (hf : Feasible (matrix adj μ) sourceNode sinkNode f)
    (hv : value f sourceNode = ∑ u, (μ u : ℤ)) :
    (∀ u v, 0 ≤ f (leftNode u) (rightNode v)) ∧
      (∀ u v, ¬ adj u v → f (leftNode u) (rightNode v) = 0) ∧
      (∀ u, (∑ v, f (leftNode u) (rightNode v)) = (μ u : ℤ)) ∧
      (∀ v, (∑ u, f (leftNode u) (rightNode v)) = (μ v : ℤ)) := by
  have hsource : ∀ u, f sourceNode (leftNode u) = (μ u : ℤ) := by
    apply saturated_coordinates
    · intro u
      exact hf.2.1 sourceNode (leftNode u)
    · rwa [source_value adj μ hf] at hv
  have hrow : ∀ u, (∑ v, f (leftNode u) (rightNode v)) = (μ u : ℤ) :=
    fun u => (transport_row adj μ hf u).trans (hsource u)
  refine ⟨transport_nonnegative adj μ hf, transport_supported adj μ hf, hrow, ?_⟩
  apply saturated_coordinates
  · intro v
    rw [transport_column adj μ hf v]
    exact hf.2.1 (rightNode v) sinkNode
  · rw [Finset.sum_comm]
    simp only [hrow]

/-- A minimum network cut, expressed as the two chosen cover sets. -/
theorem network_cut_minimum (adj : V → V → Prop) [DecidableRel adj]
    (nodes : List V) (complete : ∀ v, v ∈ nodes) (w : V → ℚ) :
    let X := membership (networkResult adj nodes w).cut
    IsCut X ∧ ∀ C D,
      DoubleCover.cutCapacity adj (fun v => (scaledWeight w v : ℚ))
        (leftCover X) (rightCover X) ≤
      DoubleCover.cutCapacity adj (fun v => (scaledWeight w v : ℚ)) C D := by
  have hs := MaxFlowScaling.solve_correct (matrix adj (scaledWeight w)) (networkNodes nodes)
    (networkNodes_complete nodes complete) sourceNode sinkNode (by simp [sourceNode, sinkNode])
  change Feasible _ _ _ (networkResult adj nodes w).flow ∧ _ at hs
  let X := membership (networkResult adj nodes w).cut
  have hX : IsCut X := by
    exact ⟨by simpa [X, membership, networkResult] using hs.2.1,
      by simpa [X, membership, networkResult] using hs.2.2.1⟩
  refine ⟨hX, ?_⟩
  intro C D
  let Y := side C D
  let T : Finset (Node V) := Finset.univ.filter fun v => Y v = true
  have ht : IsCut Y := side_isCut C D
  have hST : sourceNode ∈ T := by simp [T, ht.1]
  have hTT : sinkNode ∉ T := by simp [T, ht.2]
  have hh := hs.2.2.2.2 T hST hTT
  have hmem : membership T = Y := by
    funext v
    simp [membership, T]
  have hcast := (show (((cutCapacity _ _ : ℤ)) : ℚ) ≤
      (((cutCapacity _ T : ℤ)) : ℚ) from by exact_mod_cast hh)
  rw [matrix_cut, matrix_cut, hmem] at hcast
  change cutValue adj _ X ≤ cutValue adj _ (side C D) at hcast
  rwa [← side_recovery X hX, cutValue_side, cutValue_side] at hcast

/-- All-half optimality forces the computed flow to saturate every source arc. -/
theorem networkResult_value (adj : V → V → Prop) [DecidableRel adj]
    (hsym : Symmetric adj) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal adj w (fun _ => 1 / 2)) :
    value (networkResult adj nodes w).flow sourceNode = ∑ v, (scaledWeight w v : ℤ) := by
  have hs := MaxFlowScaling.solve_correct (matrix adj (scaledWeight w)) (networkNodes nodes)
    (networkNodes_complete nodes complete) sourceNode sinkNode (by simp [sourceNode, sinkNode])
  change Feasible _ _ _ (networkResult adj nodes w).flow ∧ _ at hs
  let X := membership (networkResult adj nodes w).cut
  let a := leftCover X
  let b := rightCover X
  let μq : V → ℚ := fun v => (scaledWeight w v : ℚ)
  have hm := network_cut_minimum adj nodes complete w
  change IsCut X ∧ _ at hm
  have hc := DoubleCover.minimum_cut_is_cover adj μq (fun v => Nat.cast_nonneg _) a b hm.2
  have hp := DoubleCover.optimal_of_minimum_cut adj hsym μq
    (fun v => Nat.cast_nonneg _) a b hm.2
  have he (y : V → ℚ) : Persistence.objective μq y =
      (denominator w : ℚ) * Persistence.objective w y := by
    simp only [Persistence.objective, μq, scaledWeight_exact w hw, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hhalf : Persistence.Optimal adj μq (fun _ => 1 / 2) := by
    refine ⟨ho.1, ?_⟩
    intro y hy
    rw [he, he]
    exact mul_le_mul_of_nonneg_left (ho.2 y hy) (Nat.cast_nonneg _)
  have heq : Persistence.objective μq (DoubleCover.rounded a b) =
      Persistence.objective μq (fun _ => 1 / 2) :=
    le_antisymm (hhalf.2 _ hp.2.1) (hp.2.2 _ hhalf.1)
  rw [DoubleCover.rounded_objective] at heq
  have hobj : Persistence.objective μq (fun _ => 1 / 2) = (∑ v, μq v) / 2 := by
    simp only [Persistence.objective, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hobj] at heq
  have hcost : DoubleCover.coverCost μq a b = ∑ v, μq v := by linarith
  have hcut := matrix_cut adj (scaledWeight w) (networkResult adj nodes w).cut
  change (((cutCapacity _ _ : ℤ)) : ℚ) = cutValue adj μq X at hcut
  rw [← side_recovery X hm.1, cutValue_side,
    DoubleCover.cutCapacity_of_cover adj μq a b hc, hcost] at hcut
  have hv := hs.2.2.2.1
  change value (networkResult adj nodes w).flow sourceNode =
    cutCapacity (matrix adj (scaledWeight w)) (networkResult adj nodes w).cut at hv
  have hval : ((value (networkResult adj nodes w).flow sourceNode : ℤ) : ℚ) =
      ∑ v, (scaledWeight w v : ℚ) := by
    rw [hv]
    exact hcut
  exact_mod_cast hval

/-- The actual computed ordered-pair flow is a transport after positive scaling. -/
def rationalTransport (adj : V → V → Prop) [DecidableRel adj]
    (nodes : List V) (w : V → ℚ) (u v : V) : ℚ :=
  ((networkResult adj nodes w).flow (leftNode u) (rightNode v) : ℚ) / denominator w

/-- Nonnegative rational transport with exactly the original vertex marginals. -/
theorem rationalTransport_correct (adj : V → V → Prop) [DecidableRel adj]
    (hsym : Symmetric adj) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal adj w (fun _ => 1 / 2)) :
    (∀ u v, 0 ≤ rationalTransport adj nodes w u v) ∧
      (∀ u v, ¬ adj u v → rationalTransport adj nodes w u v = 0) ∧
      (∀ u, (∑ v, rationalTransport adj nodes w u v) = w u) ∧
      (∀ v, (∑ u, rationalTransport adj nodes w u v) = w v) := by
  have hs := MaxFlowScaling.solve_correct (matrix adj (scaledWeight w)) (networkNodes nodes)
    (networkNodes_complete nodes complete) sourceNode sinkNode (by simp [sourceNode, sinkNode])
  have hv := networkResult_value adj hsym nodes complete w hw ho
  have hf : Feasible (matrix adj (scaledWeight w)) sourceNode sinkNode
      (networkResult adj nodes w).flow := hs.1
  have ht := saturated_transport adj (scaledWeight w) hf hv
  have hd : (0 : ℚ) < denominator w := by exact_mod_cast denominator_positive w
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v
    exact div_nonneg (by exact_mod_cast ht.1 u v) hd.le
  · intro u v h
    simp only [rationalTransport, ht.2.1 u v h, Int.cast_zero, zero_div]
  · intro u
    simp only [rationalTransport, ← Finset.sum_div, ← Int.cast_sum, ht.2.2.1 u,
      Int.cast_natCast, scaledWeight_exact w hw]
    exact mul_div_cancel_left₀ (w u) (ne_of_gt hd)
  · intro v
    simp only [rationalTransport, ← Finset.sum_div, ← Int.cast_sum, ht.2.2.2 v,
      Int.cast_natCast, scaledWeight_exact w hw]
    exact mul_div_cancel_left₀ (w v) (ne_of_gt hd)

end WeightedMIS.MaxFlowDual
