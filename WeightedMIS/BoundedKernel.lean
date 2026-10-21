module

public import Mathlib

/-!
# Integral elimination on an odd unicycle

The results here verify the integer arithmetic and the sharp coefficient
bounds used in Lemma 7. Leaf removal preserves an even total right-hand side
and does not increase its absolute sum. An odd cyclic recurrence has a unique
integer solution when that total is even; if the absolute sum is at most two,
every cyclic coordinate is at most one in absolute value.

Construction of a spanning odd unicycle and extraction of a polynomial-time
kernel basis are separate obligations. These results do not assume them.
-/

@[expose] public section

namespace WeightedMIS.BoundedKernel

/-- Alternating sum, beginning with a positive sign. -/
def alternating : List ℤ → ℤ
  | [] => 0
  | a :: h => a - alternating h

/-- The absolute sum of a finite right-hand side. -/
def normOne (h : List ℤ) : ℤ := (h.map abs).sum

/-- Propagate successive edge values through the equations `xᵢ+xᵢ₊₁=hᵢ`. -/
def propagate : List ℤ → ℤ → ℤ
  | [], t => t
  | a :: h, t => propagate h (a - t)

theorem alternating_mod_two (h : List ℤ) : alternating h % 2 = h.sum % 2 := by
  induction h with
  | nil => simp [alternating]
  | cons a h ih =>
      simp only [alternating, List.sum_cons]
      omega

theorem alternating_abs_le (h : List ℤ) : |alternating h| ≤ normOne h := by
  induction h with
  | nil => simp [alternating, normOne]
  | cons a h ih =>
      calc
        |alternating (a :: h)| = |a - alternating h| := rfl
        _ ≤ |a| + |alternating h| := by simpa [sub_eq_add_neg] using abs_add_le a (-alternating h)
        _ ≤ |a| + normOne h := by omega
        _ = normOne (a :: h) := by simp [normOne]

theorem propagate_append (h k : List ℤ) (t : ℤ) :
    propagate (h ++ k) t = propagate k (propagate h t) := by
  induction h generalizing t with
  | nil => rfl
  | cons a h ih =>
      simp only [List.cons_append, propagate]
      exact ih _

/-- The closed form of the cyclic recurrence. -/
theorem propagate_eq (h : List ℤ) (t : ℤ) :
    propagate h t = (-1 : ℤ) ^ h.length * (t - alternating h) := by
  induction h generalizing t with
  | nil => simp [propagate, alternating]
  | cons a h ih =>
      simp only [propagate, alternating, List.length_cons]
      rw [ih, pow_succ]
      ring

/-- On odd length, closure is exactly the doubled alternating-sum equation. -/
theorem odd_closure_iff (h : List ℤ) (hn : Odd h.length) (t : ℤ) :
    propagate h t = t ↔ 2 * t = alternating h := by
  rw [propagate_eq, hn.neg_one_pow]
  omega

/-- An even total right-hand side gives the unique integral odd-cycle solution. -/
theorem odd_cycle_unique_solution (h : List ℤ) (hn : Odd h.length)
    (heven : Even h.sum) :
    ∃! t : ℤ, propagate h t = t := by
  have he : h.sum % 2 = 0 := Int.even_iff.mp heven
  have ha : alternating h % 2 = 0 := by rw [alternating_mod_two, he]
  refine ⟨alternating h / 2, ?_, ?_⟩
  · change propagate h (alternating h / 2) = alternating h / 2
    rw [odd_closure_iff h hn]
    omega
  · intro t ht
    rw [odd_closure_iff h hn] at ht
    omega

/-- Any closed solution to an odd recurrence with absolute sum at most two
has its initial value bounded by one. -/
theorem odd_cycle_initial_bound (h : List ℤ) (hn : Odd h.length)
    (hb : normOne h ≤ 2) (t : ℤ) (ht : propagate h t = t) : |t| ≤ 1 := by
  have he := (odd_closure_iff h hn t).mp ht
  have ha : |alternating h| ≤ 2 := le_trans (alternating_abs_le h) hb
  rw [abs_le] at ha ⊢
  omega

/-- The same bound applies at every intermediate coordinate, by rotating the
cyclic equations. The statement covers every possible prefix, including empty. -/
theorem odd_cycle_prefix_bound (h : List ℤ) (hn : Odd h.length)
    (hb : normOne h ≤ 2) (t : ℤ) (ht : propagate h t = t)
    (pre post : List ℤ) (hsplit : h = pre ++ post) :
    |propagate pre t| ≤ 1 := by
  have hclosed : propagate (post ++ pre) (propagate pre t) = propagate pre t := by
    rw [propagate_append]
    have hf : propagate post (propagate pre t) = t := by
      rw [← propagate_append, ← hsplit]
      exact ht
    rw [hf]
  have hlen : (post ++ pre).length = h.length := by
    rw [hsplit]
    simp [Nat.add_comm]
  have hnorm : normOne (post ++ pre) = normOne h := by
    rw [hsplit]
    simp [normOne, add_comm]
  exact odd_cycle_initial_bound (post ++ pre) (hlen ▸ hn)
    (hnorm ▸ hb) (propagate pre t) hclosed

/-- Existence, uniqueness, integrality, and all coordinate bounds for the
odd-cycle elimination stage of Lemma 7. -/
theorem odd_cycle_bounded_solution (h : List ℤ) (hn : Odd h.length)
    (heven : Even h.sum) (hb : normOne h ≤ 2) :
    ∃ t : ℤ, propagate h t = t ∧
      (∀ pre post, h = pre ++ post → |propagate pre t| ≤ 1) ∧
      ∀ s : ℤ, propagate h s = s → s = t := by
  obtain ⟨t, ht, huniq⟩ := odd_cycle_unique_solution h hn heven
  exact ⟨t, ht, fun pre post hs => odd_cycle_prefix_bound h hn hb t ht pre post hs,
    huniq⟩

/-- Removing a leaf of value `a` subtracts `a` from its parent's right-hand side. -/
def leafUpdate {V : Type*} [DecidableEq V] (h : V → ℤ) (parent : V) (a : ℤ)
    (v : V) : ℤ := h v - if v = parent then a else 0

/-- Exact total-sum change at one leaf elimination. -/
theorem leaf_sum {V : Type*} [DecidableEq V] (remaining : Finset V)
    (parent : V) (hp : parent ∈ remaining) (h : V → ℤ) (a : ℤ) :
    (∑ v ∈ remaining, leafUpdate h parent a v) =
      (a + ∑ v ∈ remaining, h v) - 2 * a := by
  simp [leafUpdate, Finset.sum_sub_distrib, hp]
  ring

/-- Leaf elimination cannot increase the absolute sum. -/
theorem leaf_norm_nonincreasing {V : Type*} [DecidableEq V]
    (remaining : Finset V) (parent : V) (hp : parent ∈ remaining)
    (h : V → ℤ) (a : ℤ) :
    (∑ v ∈ remaining, |leafUpdate h parent a v|) ≤
      |a| + ∑ v ∈ remaining, |h v| := by
  calc
    (∑ v ∈ remaining, |leafUpdate h parent a v|) ≤
        ∑ v ∈ remaining, (|h v| + |if v = parent then a else 0|) := by
      apply Finset.sum_le_sum
      intro v hv
      exact le_trans (by rfl : |leafUpdate h parent a v| ≤ |h v - (if v = parent then a else 0)|)
        (by simpa [sub_eq_add_neg] using abs_add_le (h v) (-(if v = parent then a else 0)))
    _ = |a| + ∑ v ∈ remaining, |h v| := by
      simp [Finset.sum_add_distrib, abs_ite, hp, add_comm]

/-- The coordinate sum remains even after removing a leaf. -/
theorem leaf_even {V : Type*} [DecidableEq V]
    (remaining : Finset V) (parent : V) (hp : parent ∈ remaining)
    (h : V → ℤ) (a : ℤ) (heven : Even (a + ∑ v ∈ remaining, h v)) :
    Even (∑ v ∈ remaining, leafUpdate h parent a v) := by
  rw [leaf_sum remaining parent hp h a]
  exact heven.sub (even_two_mul a)

/-- In the bounded elimination invariant, every removed tree-edge coefficient
is at most two, and the remaining right-hand side keeps the same bound. -/
theorem leaf_bounded {V : Type*} [DecidableEq V]
    (remaining : Finset V) (parent : V) (hp : parent ∈ remaining)
    (h : V → ℤ) (a : ℤ)
    (hb : |a| + ∑ v ∈ remaining, |h v| ≤ 2) :
    |a| ≤ 2 ∧ (∑ v ∈ remaining, |leafUpdate h parent a v|) ≤ 2 := by
  have hn : 0 ≤ ∑ v ∈ remaining, |h v| :=
    Finset.sum_nonneg (fun v _ => abs_nonneg (h v))
  exact ⟨by omega, le_trans (leaf_norm_nonincreasing remaining parent hp h a) hb⟩

end WeightedMIS.BoundedKernel
