module

public import WeightedMIS.SupportConstructionCost

/-!
# Polynomial operation bounds for kernel preprocessing

The explicit counts for initial elimination, supported-cycle decomposition,
and complement selection are bounded by fixed-degree polynomials in the input
dimensions. These are operation bounds; scalar encodings are handled separately.
-/

@[expose] public section

namespace WeightedMIS.PreprocessingPolynomial

open SupportConstructionCost

theorem candidatesBudget_le {n m N : ℕ} (hn : n ≤ N) (hm : m ≤ N) (hN : 1 ≤ N) :
    candidatesBudget n m ≤ 203 * N ^ 5 := by
  have hmono : candidatesBudget n m ≤ candidatesBudget N N := by
    unfold candidatesBudget roundBudget cycleBudget StoredEliminationCost.cutFactor
    gcongr
  apply hmono.trans
  have h0 : 1 ≤ N ^ 5 := one_le_pow₀ hN
  have h1 : N ≤ N ^ 5 := by simpa using Nat.pow_le_pow_right hN (show 1 ≤ 5 by omega)
  have h2 : N ^ 2 ≤ N ^ 5 := Nat.pow_le_pow_right hN (by omega)
  have h3 : N ^ 3 ≤ N ^ 5 := Nat.pow_le_pow_right hN (by omega)
  have h4 : N ^ 4 ≤ N ^ 5 := Nat.pow_le_pow_right hN (by omega)
  unfold candidatesBudget roundBudget cycleBudget StoredEliminationCost.cutFactor
  ring_nf
  omega

theorem selectionBudget_le {m r N : ℕ} (hm : m ≤ N) (hr : r ≤ N) (hN : 1 ≤ N) :
    (m * m) * (StoredEliminationCost.outsideBound m (r + m * m) + 1) ≤ 55 * N ^ 7 := by
  have hmono : (m * m) * (StoredEliminationCost.outsideBound m (r + m * m) + 1) ≤
      (N * N) * (StoredEliminationCost.outsideBound N (N + N * N) + 1) := by
    unfold StoredEliminationCost.outsideBound StoredEliminationCost.cutFactor
    gcongr
  apply hmono.trans
  have h2 : N ^ 2 ≤ N ^ 7 := Nat.pow_le_pow_right hN (by omega)
  have h3 : N ^ 3 ≤ N ^ 7 := Nat.pow_le_pow_right hN (by omega)
  have h4 : N ^ 4 ≤ N ^ 7 := Nat.pow_le_pow_right hN (by omega)
  have h5 : N ^ 5 ≤ N ^ 7 := Nat.pow_le_pow_right hN (by omega)
  have h6 : N ^ 6 ≤ N ^ 7 := Nat.pow_le_pow_right hN (by omega)
  unfold StoredEliminationCost.outsideBound StoredEliminationCost.cutFactor
  ring_nf
  omega

/-- The full deterministic bounded-row preprocessing has fixed-degree
polynomial scalar/list work, including all complement membership tests. -/
theorem complementWork_polynomial {n m : ℕ} (left right : Fin m → Fin n)
    (rows : List (Fin m → ℚ)) :
    complementWork left right rows ≤ 258 * (n + m + rows.length + 1) ^ 7 := by
  let N := n + m + rows.length + 1
  have hn : n ≤ N := by omega
  have hm : m ≤ N := by omega
  have hr : rows.length ≤ N := by omega
  have hN : 1 ≤ N := by omega
  have hc := candidatesBudget_le hn hm hN
  have hs := selectionBudget_le hm hr hN
  have hp : N ^ 5 ≤ N ^ 7 := Nat.pow_le_pow_right hN (by omega)
  have hw := complementWork_le left right rows
  change complementWork left right rows ≤ 258 * N ^ 7
  omega

end WeightedMIS.PreprocessingPolynomial
