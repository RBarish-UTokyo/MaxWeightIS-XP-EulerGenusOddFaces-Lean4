module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
Arithmetic and finite-set support for the parameter estimates in
"Maximum-weight independent set in embedded graphs parameterized by Euler
genus and number of odd faces".

Scope: the genus equation, boundary parity, and residual rank inequalities
are explicit premises. This file does not establish them for surface
embeddings, and does not assert a running-time theorem for an algorithm.
-/

@[expose] public section

namespace WeightedMIS.Parameters

open scoped BigOperators

/-- The paper's nonnegative parameter exponent. Natural-number subtraction
implements truncation at zero, so this is `max {0, γ + k - 2, γ - 1}`. -/
def exponent (γ k : ℕ) : ℕ := max (γ + k - 2) (γ - 1)

/-- The corresponding orientable parameter exponent. -/
def orientableExponent (γ k : ℕ) : ℕ := γ + k - 2

/-- The local arithmetic estimate in Lemma 2. Here `b` is the number of
boundary circles, `o` counts odd boundary walks, and `t` counts odd original
regions on this side. Their geometric interpretation is not assumed. -/
theorem boundary_bound (b o t : ℕ) (hb : 1 ≤ b) (ho : o ≤ b)
    (hpar : o % 2 = t % 2) : o ≤ t + 2 * (b - 1) := by
  by_cases h : b = 1
  · omega
  · omega

/-- Summing the local boundary estimate, with all premises explicit. -/
theorem sum_boundary_bound {ι : Type*} [Fintype ι]
    (b o t : ι → ℕ) (hb : ∀ i, 1 ≤ b i) (ho : ∀ i, o i ≤ b i)
    (hpar : ∀ i, o i % 2 = t i % 2) :
    (∑ i, o i) ≤ (∑ i, t i) + 2 * ∑ i, (b i - 1) := by
  calc
    (∑ i, o i) ≤ ∑ i, (t i + 2 * (b i - 1)) :=
      Finset.sum_le_sum fun i _ => boundary_bound (b i) (o i) (t i)
        (hb i) (ho i) (hpar i)
    _ = (∑ i, t i) + 2 * ∑ i, (b i - 1) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The numerical consequence of Euler-characteristic gluing and the
odd-boundary estimate. Neither premise is a theorem about surfaces here. -/
theorem genus_bookkeeping (γ γH k kH η excess : ℕ)
    (hgenus : γ = γH + η + 2 * excess)
    (hodd : kH ≤ k + 2 * excess) :
    γH ≤ γ ∧ γH + kH + η ≤ γ + k := by
  omega

/-- The summed arithmetic conclusion of Lemma 2, conditional on the
stated genus equation and boundary parities. -/
theorem summed_genus_bookkeeping {ι : Type*} [Fintype ι]
    (γ γH k : ℕ) (b η o t : ι → ℕ)
    (hb : ∀ i, 1 ≤ b i) (ho : ∀ i, o i ≤ b i)
    (hpar : ∀ i, o i % 2 = t i % 2)
    (hk : ∑ i, t i = k)
    (hgenus : γ = γH + (∑ i, η i) + 2 * ∑ i, (b i - 1)) :
    γH ≤ γ ∧ γH + (∑ i, o i) ≤ γ + k := by
  have hodd := sum_boundary_bound b o t hb ho hpar
  rw [hk] at hodd
  have h := genus_bookkeeping γ γH k (∑ i, o i) (∑ i, η i)
    (∑ i, (b i - 1)) hgenus hodd
  omega

/-- Transfer of the two residual rank inequalities to the original
parameters. The `+ 1` and `+ 2` formulation retains their signed meaning
without accidentally weakening an impossible negative bound to zero. -/
theorem parameter_transfer (γ k γH kH d : ℕ)
    (hgenus : γH ≤ γ) (hcombined : γH + kH ≤ γ + k)
    (heven : kH = 0 → d + 1 ≤ γH)
    (hodd : kH ≠ 0 → d + 2 ≤ γH + kH) :
    d ≤ exponent γ k := by
  unfold exponent
  by_cases hk : kH = 0
  · have hd := heven hk
    omega
  · have hd := hodd hk
    omega

/-- Transfer of the sharper orientable rank bound. -/
theorem orientable_parameter_transfer (γ k γH kH d : ℕ)
    (hcombined : γH + kH ≤ γ + k)
    (hd : d + 2 ≤ γH + kH) :
    d ≤ orientableExponent γ k := by
  unfold orientableExponent
  omega

theorem exponent_le_parameter (γ k : ℕ) : exponent γ k ≤ γ + k := by
  unfold exponent
  omega

theorem orientable_exponent_le (γ k : ℕ) :
    orientableExponent γ k ≤ exponent γ k := by
  unfold orientableExponent exponent
  omega

theorem exponent_no_odd_faces (γ : ℕ) : exponent γ 0 = γ - 1 := by
  unfold exponent
  omega

theorem exponent_with_odd_faces (γ k : ℕ) (hk : 1 ≤ k) :
    exponent γ k = γ + k - 2 := by
  unfold exponent
  omega

theorem plane_exponent (k : ℕ) : exponent 0 k = k - 2 := by
  unfold exponent
  omega

/-- Shifted finite labels for the integer box `[-2m,2m]^d`.
This definition specifies a finite set, not reachability in a search graph. -/
abbrev Signature (m d : ℕ) := Fin d → Fin (4 * m + 1)

/-- The hub/working-state carrier used for the size calculation.
`q` is the number of states of the auxiliary directed graph. -/
abbrev ExpandedState (m d q : ℕ) :=
  (Signature m d × Fin 2) ⊕ (Fin q × Fin q × Signature m d × Fin 2)

theorem signature_card (m d : ℕ) :
    Fintype.card (Signature m d) = (4 * m + 1) ^ d := by
  simp [Signature]

/-- Exact count of the displayed carrier, rather than a claim that an
implemented graph has this carrier. -/
theorem expanded_state_card (m d q : ℕ) :
    Fintype.card (ExpandedState m d q) =
      2 * (4 * m + 1) ^ d * (1 + q ^ 2) := by
  simp [ExpandedState, Signature]
  ring

/-- The exponential-factor estimate used in Section 7. -/
theorem box_size_bound (m d N : ℕ) (hm : m ≤ N) (hN : 1 ≤ N) :
    (4 * m + 1) ^ d ≤ 5 ^ d * N ^ d := by
  calc
    (4 * m + 1) ^ d ≤ (5 * N) ^ d := Nat.pow_le_pow_left (by omega) d
    _ = 5 ^ d * N ^ d := Nat.mul_pow 5 N d

/-- Absorb both a bounded residual exponent and its exponential constant
into the ambient parameter. This is an arithmetic estimate only. -/
theorem box_size_parameter_bound (m d N γ k : ℕ)
    (hm : m ≤ N) (hN : 1 ≤ N) (hd : d ≤ exponent γ k) :
    (4 * m + 1) ^ d ≤ 5 ^ (γ + k) * N ^ exponent γ k := by
  have hdparam : d ≤ γ + k := le_trans hd (exponent_le_parameter γ k)
  calc
    (4 * m + 1) ^ d ≤ 5 ^ d * N ^ d := box_size_bound m d N hm hN
    _ ≤ 5 ^ (γ + k) * N ^ exponent γ k :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hdparam)
        (Nat.pow_le_pow_right (by omega) hd)

end WeightedMIS.Parameters
