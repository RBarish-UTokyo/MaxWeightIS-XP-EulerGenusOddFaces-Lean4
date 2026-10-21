module

public import WeightedMIS.MaxFlowPreprocessing
public import WeightedMIS.MaxFlowScaling

/-!
# Capacity bit bounds for rational preprocessing

The product of rational denominators has polynomial binary length. Explicit
bounds below propagate a common numerator/denominator bit bound through the
actual integer network and its capacity-scaling iteration budget.
-/

@[expose] public section

namespace WeightedMIS.MaxFlowSize

open scoped BigOperators
open MaxFlowPreprocessing DoubleCoverNetwork

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Denominator clearing multiplies bit lengths additively. -/
theorem denominator_le_pow (w : V → ℚ) (B : ℕ)
    (hden : ∀ v, (w v).den ≤ 2 ^ B) :
    denominator w ≤ 2 ^ (B * Fintype.card V) := by
  calc
    denominator w ≤ ∏ _v : V, 2 ^ B := Finset.prod_le_prod' fun v _ => hden v
    _ = _ := by simp [pow_mul]

/-- Exact scaled numerators also have polynomial binary length. -/
theorem scaledWeight_le_pow (w : V → ℚ) (B : ℕ)
    (hden : ∀ v, (w v).den ≤ 2 ^ B) (hnum : ∀ v, (w v).num.natAbs ≤ 2 ^ B) (v : V) :
    scaledWeight w v ≤ 2 ^ (B * (Fintype.card V + 1)) := by
  calc
    scaledWeight w v ≤ (w v).num.natAbs * denominator w :=
      Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
    _ ≤ 2 ^ B * 2 ^ (B * Fintype.card V) :=
      Nat.mul_le_mul (hnum v) (denominator_le_pow w B hden)
    _ = _ := by rw [← pow_add]; congr 1; ring

/-- Exact size of the constructed node set. -/
theorem node_card : Fintype.card (Node V) = 2 * (Fintype.card V + 1) := by
  simp [Node, Fintype.card_sum, Fintype.card_prod]
  omega

/-- The node count is bounded by a power with a linear exponent. -/
theorem node_card_le_pow : Fintype.card (Node V) ≤ 2 ^ (Fintype.card V + 1) := by
  rw [node_card, pow_succ]
  have hh : Fintype.card V + 1 ≤ 2 ^ Fintype.card V := Nat.lt_two_pow_self
  nlinarith

/-- Each natural capacity is bounded by the total scaled vertex weight plus one. -/
theorem matrix_entry_bound (adj : V → V → Prop) [DecidableRel adj] (μ : V → ℕ)
    (u v : Node V) : matrix adj μ u v ≤ 1 + ∑ x, μ x := by
  have hm (x : V) : μ x ≤ ∑ x, μ x :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
  rcases u with b | ⟨b, u⟩ <;> rcases v with d | ⟨d, v⟩ <;>
    cases b <;> cases d <;> simp only [matrix]
  all_goals first | omega | exact (hm _).trans (by omega) | (split_ifs <;> omega)

/-- A polynomial exponent bounds the complete integer network capacity sum. -/
def inputExponent (V : Type*) [Fintype V] (B : ℕ) : ℕ :=
  B * (Fintype.card V + 1) + 3 * Fintype.card V + 2

theorem capacitySum_le_pow (adj : V → V → Prop) [DecidableRel adj]
    (w : V → ℚ) (B : ℕ) (hden : ∀ v, (w v).den ≤ 2 ^ B)
    (hnum : ∀ v, (w v).num.natAbs ≤ 2 ^ B) :
    MaxFlowScaling.capacitySum (matrix adj (scaledWeight w)) ≤ 2 ^ inputExponent V B := by
  let n := Fintype.card V
  let W := B * (n + 1)
  have hμ : ∀ v, scaledWeight w v ≤ 2 ^ W := scaledWeight_le_pow w B hden hnum
  have hsum : (∑ v, scaledWeight w v) ≤ n * 2 ^ W := by
    calc
      _ ≤ ∑ _v : V, 2 ^ W := Finset.sum_le_sum fun v _ => hμ v
      _ = _ := by simp [n]
  have hn : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have hp : 1 ≤ 2 ^ W := Nat.one_le_two_pow
  have hM : 1 + ∑ v, scaledWeight w v ≤ 2 ^ (n + W) := by
    calc
      _ ≤ (n + 1) * 2 ^ W := by nlinarith
      _ ≤ 2 ^ n * 2 ^ W := Nat.mul_le_mul_right _ hn
      _ = _ := by rw [pow_add]
  have hentry (u v : Node V) : matrix adj (scaledWeight w) u v ≤ 2 ^ (n + W) :=
    (matrix_entry_bound adj (scaledWeight w) u v).trans hM
  have hall : MaxFlowScaling.capacitySum (matrix adj (scaledWeight w)) ≤
      Fintype.card (Node V) ^ 2 * 2 ^ (n + W) := by
    calc
      _ ≤ ∑ _u : Node V, ∑ _v : Node V, 2 ^ (n + W) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hentry u v
      _ = _ := by simp; ring
  have hcard := node_card_le_pow (V := V)
  calc
    _ ≤ Fintype.card (Node V) ^ 2 * 2 ^ (n + W) := hall
    _ ≤ (2 ^ (n + 1)) ^ 2 * 2 ^ (n + W) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hcard 2)
    _ = 2 ^ inputExponent V B := by
      rw [← pow_mul, ← pow_add]
      congr 1
      dsimp [inputExponent, n, W]
      ring

/-- The number of scales is polynomial in vertex count and input bit bound. -/
theorem initialScale_le (adj : V → V → Prop) [DecidableRel adj]
    (w : V → ℚ) (B : ℕ) (hden : ∀ v, (w v).den ≤ 2 ^ B)
    (hnum : ∀ v, (w v).num.natAbs ≤ 2 ^ B) :
    MaxFlowScaling.initialScale (matrix adj (scaledWeight w)) ≤ inputExponent V B := by
  have hc := capacitySum_le_pow adj w B hden hnum
  unfold MaxFlowScaling.initialScale
  by_cases hz : MaxFlowScaling.capacitySum (matrix adj (scaledWeight w)) = 0
  · simp [hz]
  · have hstrict : MaxFlowScaling.capacitySum (matrix adj (scaledWeight w)) <
        2 ^ (inputExponent V B + 1) := by
      have hp : 0 < 2 ^ inputExponent V B := by positivity
      rw [pow_succ]
      omega
    exact Nat.le_of_lt_succ ((Nat.log2_lt hz).mpr hstrict)

/-- Search-count bound expressed entirely in input dimensions and bit lengths. -/
theorem network_searches_bound (adj : V → V → Prop) [DecidableRel adj]
    (nodes : List V) (w : V → ℚ) (B : ℕ) (hden : ∀ v, (w v).den ≤ 2 ^ B)
    (hnum : ∀ v, (w v).num.natAbs ≤ 2 ^ B) :
    (networkResult adj nodes w).searches ≤ (inputExponent V B + 1) *
      (8 * (Fintype.card V + 1) ^ 2 + 2) := by
  have hh := (MaxFlowScaling.solve_counts (matrix adj (scaledWeight w))
    (networkNodes nodes) sourceNode sinkNode).1
  have hs := initialScale_le adj w B hden hnum
  change (MaxFlowScaling.capacitySum (matrix adj (scaledWeight w))).log2 ≤ _ at hs
  rw [node_card] at hh
  change (MaxFlowScaling.solve _ _ _ _).searches ≤ _
  calc
    _ ≤ ((MaxFlowScaling.capacitySum (matrix adj (scaledWeight w))).log2 + 1) *
        (2 * (2 * (Fintype.card V + 1)) ^ 2 + 2) := hh
    _ ≤ (inputExponent V B + 1) * (2 * (2 * (Fintype.card V + 1)) ^ 2 + 2) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right hs 1)
    _ = _ := by ring

end WeightedMIS.MaxFlowSize
