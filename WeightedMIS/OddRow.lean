module

public import WeightedMIS.Incidence

/-!
# The alternating row of an odd closed walk

The integer row is constructed by induction on actual edge traversals. Repeated
edge labels are added with their alternating signs. The resulting functional
identity needs neither a simple cycle nor an extra algebraic premise.
-/

@[expose] public section

namespace WeightedMIS.OddRow

open Finset
open WeightedMIS.Incidence

variable {V E : Type*}

/-- Concatenation preserves the sum of the two walk lengths. -/
theorem walk_append (left right : E → V) {a b c : V} {n m : ℕ}
    (p : Walk left right a b n) (q : Walk left right b c m) :
    Walk left right a c (n + m) := by
  induction q with
  | nil => simpa using p
  | @forward c m e hc q ih =>
      simpa [Nat.add_assoc] using Walk.forward e hc ih
  | @backward c m e hc q ih =>
      simpa [Nat.add_assoc] using Walk.backward e hc ih

/-- Reversing an edge walk preserves its length. -/
theorem walk_reverse (left right : E → V) {a b : V} {n : ℕ}
    (p : Walk left right a b n) : Walk left right b a n := by
  induction p with
  | nil => exact Walk.nil _
  | @forward b n e hb p ih =>
      subst b
      have step : Walk left right (right e) (left e) 1 :=
        Walk.backward e rfl (Walk.nil (right e))
      simpa [Nat.add_comm] using walk_append left right step ih
  | @backward b n e hb p ih =>
      subst b
      have step : Walk left right (left e) (right e) 1 :=
        Walk.forward e rfl (Walk.nil (left e))
      simpa [Nat.add_comm] using walk_append left right step ih

/-- Without an odd closed walk, all walks joining the same ordered pair
have the same length parity. -/
theorem walk_parity_unique (left right : E → V)
    (hno : ¬ HasOddClosedWalk left right)
    {a b : V} {n m : ℕ} (p : Walk left right a b n)
    (q : Walk left right a b m) : n % 2 = m % 2 := by
  by_contra h
  apply hno
  refine ⟨a, n + m, ?_, walk_append left right p (walk_reverse left right q)⟩
  rw [Nat.odd_iff]
  omega

/-- A connected graph without an odd closed walk has the ordinary path-parity
two-coloring. Thus nonbipartiteness supplies an actual odd closed walk. -/
theorem exists_odd_closed_walk (left right : E → V)
    (hconn : Connected left right) (hnot : ¬ Bipartite left right) :
    HasOddClosedWalk left right := by
  classical
  by_contra hno
  have hV : Nonempty V := by
    by_contra h
    have : IsEmpty V := not_nonempty_iff.mp h
    exact hnot ⟨fun _ => false, fun e => isEmptyElim (left e)⟩
  let a : V := Classical.choice hV
  choose len path using hconn a
  apply hnot
  refine ⟨fun b => decide (len b % 2 = 1), ?_⟩
  intro e heq
  have he := walk_parity_unique left right hno
    (Walk.forward e rfl (path (left e))) (path (right e))
  by_cases hl : len (left e) % 2 = 1
  · have hr : ¬ len (right e) % 2 = 1 := by omega
    simp [hl, hr] at heq
  · have hr : len (right e) % 2 = 1 := by omega
    simp [hl, hr] at heq

/-- For any walk, its integer alternating row telescopes to the signed
endpoint difference. The doubled row sum records the same parity. -/
theorem exists_walk_row [Fintype E] (left right : E → V)
    {a b : V} {n : ℕ} (p : Walk left right a b n) :
    ∃ π : E → ℤ,
      2 * (∑ e, π e) = 1 - (-1 : ℤ) ^ n ∧
      ∀ x : V → ℚ,
        (∑ e, (π e : ℚ) * (x (left e) + x (right e))) =
          x a - (-1 : ℚ) ^ n * x b := by
  classical
  induction p with
  | nil =>
      refine ⟨0, ?_, ?_⟩
      · simp
      · intro x; simp
  | @forward b n e hb p ih =>
      obtain ⟨π, hsum, hπ⟩ := ih
      refine ⟨fun f => π f + if f = e then (-1 : ℤ) ^ n else 0, ?_, ?_⟩
      · simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true, pow_succ] at *
        linarith
      · intro x
        have hx := hπ x
        subst b
        simp only [Int.cast_add, Int.cast_ite, Int.cast_pow, Int.cast_neg,
          Int.cast_one, Int.cast_zero, add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true, pow_succ]
        linarith
  | @backward b n e hb p ih =>
      obtain ⟨π, hsum, hπ⟩ := ih
      refine ⟨fun f => π f + if f = e then (-1 : ℤ) ^ n else 0, ?_, ?_⟩
      · simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true, pow_succ] at *
        linarith
      · intro x
        have hx := hπ x
        subst b
        simp only [Int.cast_add, Int.cast_ite, Int.cast_pow, Int.cast_neg,
          Int.cast_one, Int.cast_zero, add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true, pow_succ]
        linarith

/-- The alternating integer row of an odd closed walk has sum one and sends
unsigned edge sums to twice the value at its root. -/
theorem exists_odd_row [Fintype E] (left right : E → V)
    {a : V} {n : ℕ} (hn : Odd n) (p : Walk left right a a n) :
    ∃ π : E → ℤ, (∑ e, π e) = 1 ∧
      ∀ x : V → ℚ,
        (∑ e, (π e : ℚ) * (x (left e) + x (right e))) = 2 * x a := by
  obtain ⟨π, hsum, hπ⟩ := exists_walk_row left right p
  refine ⟨π, ?_, ?_⟩
  · rw [hn.neg_one_pow] at hsum
    linarith
  · intro x
    have hx := hπ x
    rw [hn.neg_one_pow] at hx
    linarith

/-- Connected nonbipartite endpoint graphs supply the row used for the single
parity constraint, including its actual root and both required identities. -/
theorem exists_odd_row_of_nonbipartite [Fintype E]
    (left right : E → V) (hconn : Connected left right)
    (hnot : ¬ Bipartite left right) :
    ∃ a : V, ∃ π : E → ℤ, (∑ e, π e) = 1 ∧
      ∀ x : V → ℚ,
        (∑ e, (π e : ℚ) * (x (left e) + x (right e))) = 2 * x a := by
  obtain ⟨a, n, hn, p⟩ := exists_odd_closed_walk left right hconn hnot
  exact ⟨a, exists_odd_row left right hn p⟩

end WeightedMIS.OddRow
