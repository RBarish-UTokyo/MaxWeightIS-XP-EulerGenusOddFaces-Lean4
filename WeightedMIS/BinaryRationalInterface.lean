module

public import WeightedMIS.BinaryRationalArithmetic
public import WeightedMIS.RationalWidth

/-!
# Width-safe binary rational operations

Canonical stored words recover precisely the numerator and denominator used in
the rational-width proofs. The lemmas below turn those width bounds into the
raw no-overflow conditions of the verified binary arithmetic implementation.
-/

@[expose] public section

namespace WeightedMIS.BinaryRational

open EfficientSearch

variable {n : ℕ}

/-- A positive-denominator word with reduced magnitude and denominator. -/
def Canonical (q : Word n) : Prop :=
  0 < q.denominator.value ∧ q.magnitude.value = q.value.num.natAbs ∧
    q.denominator.value = q.value.den

theorem normalize_canonical (q : Word n) (hd : 0 < q.denominator.value) :
    Canonical (normalize q).1 := by
  refine ⟨normalize_denominator_pos q hd, ?_, ?_⟩
  · rw [normalize_value q hd]
    exact normalize_canonical_magnitude q hd
  · rw [normalize_value q hd]
    exact normalize_canonical_denominator q hd

theorem canonical_width (q : Word n) (B : ℕ) (hq : Canonical q)
    (h : RationalWidth.Fits q.value B) :
    q.magnitude.value < 2 ^ B ∧ q.denominator.value < 2 ^ B := by
  rw [hq.2.1, hq.2.2]
  exact (RationalWidth.fits_iff _ _).mp h

/-- Two rational input widths and one guard bit suffice for every raw cross
product, denominator product, and signed numerator sum in addition. -/
theorem cross_bounds (q r : Word n) (a b : ℕ) (hq : Canonical q) (hr : Canonical r)
    (hqa : RationalWidth.Fits q.value a) (hrb : RationalWidth.Fits r.value b)
    (hn : a + b + 1 ≤ n) :
    q.magnitude.value * r.denominator.value +
        r.magnitude.value * q.denominator.value < 2 ^ n ∧
      q.denominator.value * r.denominator.value < 2 ^ n ∧
      q.magnitude.value * r.magnitude.value < 2 ^ n ∧
      q.denominator.value * r.magnitude.value < 2 ^ n := by
  have hqv := canonical_width q a hq hqa
  have hrv := canonical_width r b hr hrb
  have hp : 2 ^ (a + b + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hbase : 2 ^ (a + b) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ < 2 ^ a * 2 ^ b + 2 ^ b * 2 ^ a :=
        Nat.add_lt_add (Nat.mul_lt_mul_of_lt_of_lt hqv.1 hrv.2)
          (Nat.mul_lt_mul_of_lt_of_lt hrv.1 hqv.2)
      _ = 2 ^ (a + b + 1) := by rw [pow_succ, pow_add]; ring
      _ ≤ 2 ^ n := hp
  · apply lt_of_lt_of_le _ hbase
    simpa only [pow_add] using Nat.mul_lt_mul_of_lt_of_lt hqv.2 hrv.2
  · apply lt_of_lt_of_le _ hbase
    simpa only [pow_add] using Nat.mul_lt_mul_of_lt_of_lt hqv.1 hrv.1
  · apply lt_of_lt_of_le _ hbase
    simpa only [pow_add] using Nat.mul_lt_mul_of_lt_of_lt hqv.2 hrv.1

theorem multiply_canonical (q r : Word n)
    (hq : 0 < q.denominator.value) (hr : 0 < r.denominator.value)
    (hd : q.denominator.value * r.denominator.value < 2 ^ n) :
    Canonical (multiply q r).1 := by
  apply normalize_canonical
  change 0 < (Bits.multiply q.denominator r.denominator).1.value
  rw [Bits.multiply_value_of_lt _ _ hd]
  positivity

theorem add_canonical (q r : Word n)
    (hq : 0 < q.denominator.value) (hr : 0 < r.denominator.value)
    (hd : q.denominator.value * r.denominator.value < 2 ^ n) :
    Canonical (add q r).1 := by
  apply normalize_canonical
  change 0 < (Bits.multiply q.denominator r.denominator).1.value
  rw [Bits.multiply_value_of_lt _ _ hd]
  positivity

theorem divide_canonical (q r : Word n)
    (hq : 0 < q.denominator.value) (hr : 0 < r.magnitude.value)
    (hd : q.denominator.value * r.magnitude.value < 2 ^ n) :
    Canonical (divide q r).1 := by
  apply normalize_canonical
  change 0 < (Bits.multiply q.denominator r.magnitude).1.value
  rw [Bits.multiply_value_of_lt _ _ hd]
  positivity

/-- A binary zero test, including construction of its comparison word. -/
def isZero (q : Word n) : Bool × ℕ :=
  let r := Bits.compare q.magnitude (Bits.zero n)
  (decide (r.1 = .eq), r.2 + n + 2)

theorem isZero_correct (q : Word n) (hq : 0 < q.denominator.value) :
    (isZero q).1 = true ↔ q.value = 0 := by
  have hc := (Bits.compare_correct q.magnitude (Bits.zero n)).2.1
  have hd : (q.denominator.value : ℚ) ≠ 0 := by positivity
  simp only [Bits.value_zero] at hc
  simp only [isZero, decide_eq_true_eq, hc]
  unfold Word.value Word.numerator
  split <;> simp [hd]

theorem isZero_steps (q : Word n) : (isZero q).2 ≤ 2 * n + 3 := by
  have h := Bits.compare_steps q.magnitude (Bits.zero n)
  simp only [isZero]
  omega

/-- Addition is exact and returns a reduced representation whenever the
working word contains the two input widths and a guard bit. -/
theorem add_width_safe (q r : Word n) (a b : ℕ) (hq : Canonical q) (hr : Canonical r)
    (hqa : RationalWidth.Fits q.value a) (hrb : RationalWidth.Fits r.value b)
    (hn : a + b + 1 ≤ n) :
    (add q r).1.value = q.value + r.value ∧ Canonical (add q r).1 ∧
      (add q r).2 ≤ 8 * n ^ 3 + 44 * n ^ 2 + 68 * n + 36 := by
  have h := cross_bounds q r a b hq hr hqa hrb hn
  exact ⟨add_value q r hq.1 hr.1 h.1 h.2.1,
    add_canonical q r hq.1 hr.1 h.2.1, add_steps q r⟩

theorem multiply_width_safe (q r : Word n) (a b : ℕ) (hq : Canonical q) (hr : Canonical r)
    (hqa : RationalWidth.Fits q.value a) (hrb : RationalWidth.Fits r.value b)
    (hn : a + b + 1 ≤ n) :
    (multiply q r).1.value = q.value * r.value ∧ Canonical (multiply q r).1 ∧
      (multiply q r).2 ≤ 8 * n ^ 3 + 42 * n ^ 2 + 61 * n + 27 := by
  have h := cross_bounds q r a b hq hr hqa hrb hn
  exact ⟨multiply_value q r hq.1 hr.1 h.2.2.1 h.2.1,
    multiply_canonical q r hq.1 hr.1 h.2.1, multiply_steps q r⟩

theorem divide_width_safe (q r : Word n) (a b : ℕ) (hq : Canonical q) (hr : Canonical r)
    (hqa : RationalWidth.Fits q.value a) (hrb : RationalWidth.Fits r.value b)
    (hn : a + b + 1 ≤ n) (hr0 : r.value ≠ 0) :
    (divide q r).1.value = q.value / r.value ∧ Canonical (divide q r).1 ∧
      (divide q r).2 ≤ 8 * n ^ 3 + 42 * n ^ 2 + 61 * n + 27 := by
  have h := cross_bounds q r a b hq hr hqa hrb hn
  have hm : 0 < r.magnitude.value := by
    rw [hr.2.1]
    exact Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hr0)
  have hp : q.magnitude.value * r.denominator.value < 2 ^ n := by omega
  exact ⟨divide_value q r hq.1 hr.1 hm hp h.2.2.2,
    divide_canonical q r hq.1 hm h.2.2.2, divide_steps q r⟩

end WeightedMIS.BinaryRational
