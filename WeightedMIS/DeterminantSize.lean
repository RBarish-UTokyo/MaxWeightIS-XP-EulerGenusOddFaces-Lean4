module

public import Mathlib

/-!
# Binary size bounds for integer determinants and rational minor ratios

The Leibniz formula gives a factorial bound for an integer determinant.
Bounding the factorial by n^n yields a polynomial binary-length bound.
Reduction of an integer ratio cannot increase its numerator or denominator.
-/

@[expose] public section

namespace WeightedMIS.DeterminantSize

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Leibniz's formula bounds the absolute integer determinant without any
nonsingularity premise. -/
theorem det_natAbs_le (A : Matrix I I ℤ) (M : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ M) :
    A.det.natAbs ≤ (Fintype.card I).factorial * M ^ Fintype.card I := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm I, (Equiv.Perm.sign σ • ∏ i, A (σ i) i).natAbs :=
      Int.natAbs_sum_le _ _
    _ = ∑ σ : Equiv.Perm I, ∏ i, (A (σ i) i).natAbs := by
      apply Finset.sum_congr rfl
      intro σ _
      simp only [Units.smul_def, zsmul_eq_mul, Int.cast_id, Int.natAbs_mul, Int.units_natAbs, one_mul]
      exact map_prod Int.natAbsHom _ _
    _ ≤ ∑ _σ : Equiv.Perm I, M ^ Fintype.card I := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ _i : I, M := Finset.prod_le_prod fun i _ => hA (σ i) i
        _ = _ := by simp
    _ = _ := by simp [Fintype.card_perm]

/-- The determinant is bounded by a power with a quadratic dimension term. -/
theorem det_natAbs_le_pow (A : Matrix I I ℤ) (B : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ B) :
    A.det.natAbs ≤ 2 ^ (B * Fintype.card I + Fintype.card I ^ 2) := by
  have hn : Fintype.card I ≤ 2 ^ Fintype.card I := Nat.lt_two_pow_self.le
  calc
    _ ≤ (Fintype.card I).factorial * (2 ^ B) ^ Fintype.card I := det_natAbs_le A _ hA
    _ ≤ (Fintype.card I) ^ Fintype.card I * (2 ^ B) ^ Fintype.card I :=
      Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
    _ ≤ (2 ^ Fintype.card I) ^ Fintype.card I * (2 ^ B) ^ Fintype.card I :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hn _)
    _ = _ := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring

/-- Polynomial binary length of the signed determinant's magnitude. -/
theorem det_size_le (A : Matrix I I ℤ) (B : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ B) :
    A.det.natAbs.size ≤ B * Fintype.card I + Fintype.card I ^ 2 + 1 := by
  apply Nat.size_le.mpr
  have hh := det_natAbs_le_pow A B hA
  have hp : 0 < 2 ^ (B * Fintype.card I + Fintype.card I ^ 2) := by positivity
  rw [pow_succ]
  omega

/-- Normalization of a rational integer ratio cannot enlarge its numerator. -/
theorem ratio_num_le (a b : ℤ) (hb : b ≠ 0) :
    ((a : ℚ) / b).num.natAbs ≤ a.natAbs := by
  rw [Rat.intCast_div_eq_divInt, Rat.num_divInt]
  calc
    _ ≤ (b.sign * a).natAbs := Int.natAbs_ediv_le_natAbs _ _
    _ = _ := by rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hb, one_mul]

/-- Normalization of a rational integer ratio cannot enlarge its denominator. -/
theorem ratio_den_le (a b : ℤ) (hb : b ≠ 0) :
    ((a : ℚ) / b).den ≤ b.natAbs := by
  rw [Rat.intCast_div_eq_divInt, Rat.den_divInt, ite_eq_right hb]
  exact Nat.div_le_self _ _

/-- A ratio of bounded integer determinants has bounded normalized components. -/
theorem det_ratio_bounds (A C : Matrix I I ℤ) (M : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ M) (hC : ∀ i j, (C i j).natAbs ≤ M)
    (hdet : C.det ≠ 0) :
    (((A.det : ℚ) / C.det).num.natAbs ≤ (Fintype.card I).factorial * M ^ Fintype.card I) ∧
      (((A.det : ℚ) / C.det).den ≤ (Fintype.card I).factorial * M ^ Fintype.card I) :=
  ⟨(ratio_num_le A.det C.det hdet).trans (det_natAbs_le A M hA),
    (ratio_den_le A.det C.det hdet).trans (det_natAbs_le C M hC)⟩

/-- Binary sizes of the normalized numerator and denominator of a minor ratio. -/
theorem det_ratio_size_le (A C : Matrix I I ℤ) (B : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ B) (hC : ∀ i j, (C i j).natAbs ≤ 2 ^ B)
    (hdet : C.det ≠ 0) :
    (((A.det : ℚ) / C.det).num.natAbs.size ≤ B * Fintype.card I + Fintype.card I ^ 2 + 1) ∧
      (((A.det : ℚ) / C.det).den.size ≤ B * Fintype.card I + Fintype.card I ^ 2 + 1) :=
  ⟨(Nat.size_le_size (ratio_num_le A.det C.det hdet)).trans (det_size_le A B hA),
    (Nat.size_le_size (ratio_den_le A.det C.det hdet)).trans (det_size_le C B hC)⟩

/-- A Cramer column update by a unit coordinate vector keeps the same entry
bound whenever that bound includes one. -/
theorem updateCol_single_bound (A : Matrix I I ℤ) (M : ℕ) (hM : 1 ≤ M)
    (hA : ∀ i j, (A i j).natAbs ≤ M) (j k : I) :
    ∀ i l, ((A.updateCol j (Pi.single k 1)) i l).natAbs ≤ M := by
  intro i l
  by_cases hl : l = j
  · subst l
    simp only [Matrix.updateCol_self]
    by_cases hi : i = k
    · subst i
      simpa using hM
    · simp [Pi.single_eq_of_ne hi]
  · simpa [Matrix.updateCol_ne hl] using hA i l

/-- Cramer ratios with a unit right-hand side have polynomial binary size. -/
theorem cramer_unit_size_le (A : Matrix I I ℤ) (B : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ B) (hdet : A.det ≠ 0) (j k : I) :
    ((((A.updateCol j (Pi.single k 1)).det : ℚ) / A.det).num.natAbs.size ≤
      B * Fintype.card I + Fintype.card I ^ 2 + 1) ∧
    ((((A.updateCol j (Pi.single k 1)).det : ℚ) / A.det).den.size ≤
      B * Fintype.card I + Fintype.card I ^ 2 + 1) :=
  det_ratio_size_le _ A B
    (updateCol_single_bound A _ Nat.one_le_two_pow hA j k) hA hdet

end WeightedMIS.DeterminantSize
