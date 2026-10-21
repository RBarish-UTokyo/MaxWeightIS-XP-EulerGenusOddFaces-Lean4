module

public import WeightedMIS.MaxFlowScaling
public import WeightedMIS.DoubleCoverNetwork

/-!
# Concrete maximum-flow preprocessing for rational weights

Rational weights are cleared by their denominator product. The explicit
integral double-cover network is solved by capacity scaling, and its minimum
cut is converted to a half-integral optimum of the original rational LP.
-/

@[expose] public section

namespace WeightedMIS.MaxFlowPreprocessing

open scoped BigOperators
open DoubleCoverNetwork

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The common denominator used by the actual preprocessing program. -/
def denominator (w : V → ℚ) : ℕ := ∏ v, (w v).den

/-- Integer scaled weights, with exact natural division of the denominator product. -/
def scaledWeight (w : V → ℚ) (v : V) : ℕ :=
  (w v).num.natAbs * (denominator w / (w v).den)

theorem denominator_positive (w : V → ℚ) : 0 < denominator w :=
  Finset.prod_pos fun v _ => (w v).den_pos

theorem scaledWeight_exact (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) (v : V) :
    (scaledWeight w v : ℚ) = (denominator w : ℚ) * w v := by
  have hdvd : (w v).den ∣ denominator w :=
    Finset.dvd_prod_of_mem (fun u => (w u).den) (Finset.mem_univ v)
  have hn : ((w v).num.natAbs : ℚ) = ((w v).num : ℚ) := by
    calc
      _ = (((w v).num.natAbs : ℤ) : ℚ) := by simp
      _ = _ := congrArg (fun z : ℤ => (z : ℚ))
        (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr (hw v)))
  have hd : (denominator w : ℚ) = ((w v).den : ℚ) *
      ((denominator w / (w v).den : ℕ) : ℚ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
  have hden : ((w v).den : ℚ) ≠ 0 := by exact_mod_cast (w v).den_ne_zero
  have hmul : ((w v).num : ℚ) = w v * ((w v).den : ℚ) :=
    (div_eq_iff hden).mp (Rat.num_div_den (w v))
  unfold scaledWeight
  rw [Nat.cast_mul, hn, hmul, hd]
  ring

/-- Natural-capacity matrix of the standard double-cover network. -/
def matrix (adj : V → V → Prop) [DecidableRel adj] (μ : V → ℕ) :
    Node V → Node V → ℕ
  | .inl false, .inr (false, v) => μ v
  | .inr (false, u), .inr (true, v) => if adj u v then 1 + ∑ x, μ x else 0
  | .inr (true, v), .inl true => μ v
  | _, _ => 0

/-- Source-side membership as a Boolean function. -/
def membership (S : Finset (Node V)) (v : Node V) : Bool := decide (v ∈ S)

/-- The explicit node enumeration, avoiding any choice of an ordering. -/
def networkNodes (nodes : List V) : List (Node V) :=
  [sourceNode, sinkNode] ++ (nodes.map fun v => Sum.inr (false, v)) ++
    (nodes.map fun v => Sum.inr (true, v))

theorem networkNodes_complete (nodes : List V) (complete : ∀ v, v ∈ nodes) :
    ∀ v, v ∈ networkNodes nodes := by
  intro v
  rcases v with b | ⟨b, v⟩
  · cases b <;> simp [networkNodes, sourceNode, sinkNode]
  · cases b <;> simp [networkNodes, complete]

/-- The matrix and labelled-arc conventions compute the same cut capacity. -/
theorem matrix_cut (adj : V → V → Prop) [DecidableRel adj] (μ : V → ℕ)
    (S : Finset (Node V)) :
    ((MaxFlowCore.cutCapacity (matrix adj μ) S : ℤ) : ℚ) =
      cutValue adj (fun v => (μ v : ℚ)) (membership S) := by
  simp only [MaxFlowCore.cutCapacity, MaxFlowCore.boundary, Int.cast_sum, Int.cast_natCast]
  have he (f : Node V → Node V → ℚ) :
      (∑ u ∈ S, ∑ v ∈ Sᶜ, f u v) =
      ∑ u, ∑ v, if u ∈ S ∧ v ∉ S then f u v else 0 := by
    simp only [ite_and]
    simp_rw [Finset.sum_ite_irrel]
    simp only [Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp
  rw [he]
  simp only [cutValue, membership, decide_eq_true_eq, decide_eq_false_iff_not]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [matrix, source, target, sourceNode, sinkNode, capacity,
    Nat.cast_zero, Nat.cast_ite, Nat.cast_add, Nat.cast_one, Nat.cast_sum,
    DoubleCover.largeCapacity, ite_self, Finset.sum_const_zero, zero_add, add_zero]
  ac_rfl

/-- The concrete integral network result. -/
def networkResult (adj : V → V → Prop) [DecidableRel adj] (nodes : List V)
    (w : V → ℚ) : MaxFlowScaling.Result (Node V) :=
  MaxFlowScaling.solve (matrix adj (scaledWeight w)) (networkNodes nodes) sourceNode sinkNode

/-- The computed half-integral LP vector. -/
def lpPoint (adj : V → V → Prop) [DecidableRel adj] (nodes : List V) (w : V → ℚ) : V → ℚ :=
  let X := membership (networkResult adj nodes w).cut
  DoubleCover.rounded (leftCover X) (rightCover X)

/-- Positive scaling transports LP optimality back to the original weights. -/
theorem optimal_of_scaled (adj : V → V → Prop) (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (x : V → ℚ) (hx : Persistence.Optimal adj (fun v => (scaledWeight w v : ℚ)) x) :
    Persistence.Optimal adj w x := by
  have he (y : V → ℚ) : Persistence.objective (fun v => (scaledWeight w v : ℚ)) y =
      (denominator w : ℚ) * Persistence.objective w y := by
    simp only [Persistence.objective, scaledWeight_exact w hw, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  refine ⟨hx.1, ?_⟩
  intro y hy
  have hh := hx.2 y hy
  rw [he, he] at hh
  have hd : (0 : ℚ) < denominator w := by exact_mod_cast denominator_positive w
  exact (mul_le_mul_iff_right₀ hd).mp hh

/-- The executable maximum-flow preprocessing returns a genuine half-integral
LP optimum for the given rational weights. -/
theorem lpPoint_correct (adj : V → V → Prop) [DecidableRel adj]
    (hsym : Symmetric adj) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) :
    Persistence.HalfIntegral (lpPoint adj nodes w) ∧
      Persistence.Optimal adj w (lpPoint adj nodes w) := by
  have hsolve := MaxFlowScaling.solve_correct (matrix adj (scaledWeight w)) (networkNodes nodes)
    (networkNodes_complete nodes complete) sourceNode sinkNode (by simp [sourceNode, sinkNode])
  change MaxFlowCore.Feasible _ _ _ (networkResult adj nodes w).flow ∧ _ at hsolve
  let X := membership (networkResult adj nodes w).cut
  have hX : IsCut X := by
    exact ⟨by simpa [X, membership, networkResult] using hsolve.2.1,
      by simpa [X, membership, networkResult] using hsolve.2.2.1⟩
  have hmin : ∀ Y, IsCut Y → cutValue adj (fun v => (scaledWeight w v : ℚ)) X ≤
      cutValue adj (fun v => (scaledWeight w v : ℚ)) Y := by
    intro Y hY
    let T : Finset (Node V) := Finset.univ.filter fun v => Y v = true
    have hST : sourceNode ∈ T := by simp [T, hY.1]
    have hTT : sinkNode ∉ T := by simp [T, hY.2]
    have hh := hsolve.2.2.2.2 T hST hTT
    have hmem : membership T = Y := by
      funext v
      simp [membership, T]
    have hcast := (show (((MaxFlowCore.cutCapacity _ _ : ℤ)) : ℚ) ≤
        (((MaxFlowCore.cutCapacity _ T : ℤ)) : ℚ) from by exact_mod_cast hh)
    rw [matrix_cut, matrix_cut, hmem] at hcast
    exact hcast
  have hp := optimal_of_minimum_network_cut adj hsym (fun v => (scaledWeight w v : ℚ))
    (fun v => Nat.cast_nonneg _) X hX hmin
  exact ⟨hp.1, optimal_of_scaled adj w hw _ hp.2⟩

end WeightedMIS.MaxFlowPreprocessing
