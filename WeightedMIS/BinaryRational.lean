module

public import WeightedMIS.BinaryGCD

/-!
# Exact binary rational normalization

A rational is stored as a sign bit and two fixed-width natural words.
Normalization uses the verified binary gcd and two verified binary divisions;
it returns the canonical numerator magnitude and positive denominator.
The displayed count is a cubic bound on the underlying Boolean arithmetic
cells, not a unit-cost assumption for unbounded rational arithmetic.
-/

@[expose] public section

namespace WeightedMIS.BinaryRational

open EfficientSearch

/-- Sign and two explicitly stored unsigned binary words. -/
structure Word (n : ℕ) where
  negative : Bool
  magnitude : Bits n
  denominator : Bits n
  deriving Repr

def Word.numerator {n : ℕ} (q : Word n) : ℤ :=
  if q.negative then -(q.magnitude.value : ℤ) else q.magnitude.value

def Word.value {n : ℕ} (q : Word n) : ℚ :=
  (q.numerator : ℚ) / q.denominator.value

@[simp] theorem numerator_natAbs {n : ℕ} (q : Word n) :
    q.numerator.natAbs = q.magnitude.value := by
  unfold Word.numerator
  split <;> simp

def normalize {n : ℕ} (q : Word n) : Word n × ℕ :=
  let g := Bits.gcd q.magnitude q.denominator
  let a := Bits.divide q.magnitude g.1
  let b := Bits.divide q.denominator g.1
  (⟨q.negative, a.1, b.1⟩, g.2 + a.2.2 + b.2.2 + 3)

theorem normalize_magnitude {n : ℕ} (q : Word n) :
    (normalize q).1.magnitude.value =
      q.magnitude.value / Nat.gcd q.magnitude.value q.denominator.value := by
  simp only [normalize]
  rw [(Bits.divide_value _ _).1, Bits.gcd_value]

theorem normalize_denominator {n : ℕ} (q : Word n) :
    (normalize q).1.denominator.value =
      q.denominator.value / Nat.gcd q.magnitude.value q.denominator.value := by
  simp only [normalize]
  rw [(Bits.divide_value _ _).1, Bits.gcd_value]

theorem normalize_denominator_pos {n : ℕ} (q : Word n)
    (hd : 0 < q.denominator.value) : 0 < (normalize q).1.denominator.value := by
  rw [normalize_denominator]
  exact Nat.div_pos (Nat.gcd_le_right _ hd) (Nat.gcd_pos_of_pos_right _ hd)

theorem normalize_coprime {n : ℕ} (q : Word n)
    (hd : 0 < q.denominator.value) :
    Nat.Coprime (normalize q).1.magnitude.value (normalize q).1.denominator.value := by
  rw [normalize_magnitude, normalize_denominator]
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ hd)

theorem quotient_fraction (a b : ℕ) (hb : 0 < b) :
    ((a / Nat.gcd a b : ℕ) : ℚ) / (b / Nat.gcd a b : ℕ) = (a : ℚ) / b := by
  have hg : Nat.gcd a b ≠ 0 := (Nat.gcd_pos_of_pos_right _ hb).ne'
  rw [Nat.cast_div (Nat.gcd_dvd_left a b), Nat.cast_div (Nat.gcd_dvd_right a b)]
  exact div_div_div_cancel_right₀ (show (Nat.gcd a b : ℚ) ≠ 0 by exact_mod_cast hg) _ _
  all_goals exact_mod_cast hg

theorem normalize_value {n : ℕ} (q : Word n) (hd : 0 < q.denominator.value) :
    (normalize q).1.value = q.value := by
  have h := quotient_fraction q.magnitude.value q.denominator.value hd
  unfold Word.value Word.numerator
  have hs : (normalize q).1.negative = q.negative := rfl
  rw [hs]
  split
  · push_cast
    rw [neg_div, neg_div, normalize_magnitude, normalize_denominator, h]
  · push_cast
    rw [normalize_magnitude, normalize_denominator, h]

/-- The output denominator is exactly Lean's reduced rational denominator. -/
theorem normalize_canonical_denominator {n : ℕ} (q : Word n)
    (hd : 0 < q.denominator.value) :
    (normalize q).1.denominator.value = q.value.den := by
  let r := (normalize q).1
  have hp : 0 < (r.denominator.value : ℤ) := by
    exact_mod_cast normalize_denominator_pos q hd
  have hc : Nat.Coprime r.numerator.natAbs (r.denominator.value : ℤ).natAbs := by
    simpa using normalize_coprime q hd
  have he := Rat.den_div_eq_of_coprime hp hc
  have hv : ((r.numerator : ℚ) / (r.denominator.value : ℤ)) = q.value := by
    simpa [r, Word.value] using normalize_value q hd
  rw [hv] at he
  exact_mod_cast he.symm

/-- The output numerator magnitude is exactly Lean's reduced numerator size. -/
theorem normalize_canonical_magnitude {n : ℕ} (q : Word n)
    (hd : 0 < q.denominator.value) :
    (normalize q).1.magnitude.value = q.value.num.natAbs := by
  let r := (normalize q).1
  have hp : 0 < (r.denominator.value : ℤ) := by
    exact_mod_cast normalize_denominator_pos q hd
  have hc : Nat.Coprime r.numerator.natAbs (r.denominator.value : ℤ).natAbs := by
    simpa using normalize_coprime q hd
  have he := Rat.num_div_eq_of_coprime hp hc
  have hv : ((r.numerator : ℚ) / (r.denominator.value : ℤ)) = q.value := by
    simpa [r, Word.value] using normalize_value q hd
  rw [hv] at he
  rw [he, numerator_natAbs]

/-- Boolean arithmetic-cell bound for actual binary normalization. -/
theorem normalize_steps {n : ℕ} (q : Word n) :
    (normalize q).2 ≤ 8 * n ^ 3 + 38 * n ^ 2 + 53 * n + 21 := by
  have hg := Bits.gcd_steps q.magnitude q.denominator
  have ha := Bits.divide_steps q.magnitude (Bits.gcd q.magnitude q.denominator).1
  have hb := Bits.divide_steps q.denominator (Bits.gcd q.magnitude q.denominator).1
  unfold normalize
  nlinarith

end WeightedMIS.BinaryRational
