module

public import WeightedMIS.BinaryRational

/-!
# Rational operations on fixed binary words

Raw products and sums are computed by the verified Boolean arithmetic routines,
then normalized by binary Euclid. Correctness hypotheses are explicit bounds
preventing overflow of raw intermediate integers. Polynomial rational-width
lemmas discharge these bounds when a common working word size is chosen.
-/

@[expose] public section

namespace WeightedMIS.BinaryRational

open EfficientSearch

variable {n : ℕ}

/-- Signed magnitude evaluation, used by the signed binary adder. -/
def signed (negative : Bool) (a : ℕ) : ℤ := if negative then -(a : ℤ) else a

theorem signed_mul (s t : Bool) (a b : ℕ) :
    signed (xor s t) (a * b) = signed s a * signed t b := by
  cases s <;> cases t <;> simp [signed]

/-- Signed addition branches only on sign bits and a bitwise comparison. -/
def signedAdd (s t : Bool) (a b : Bits n) : (Bool × Bits n) × ℕ :=
  if s = t then
    let r := Bits.add a b
    ((s, r.1), r.2.2 + 1)
  else
    let c := Bits.compare a b
    if c.1 = .lt then
      let r := Bits.subtract b a
      ((t, r.1), c.2 + r.2.2 + 2)
    else
      let r := Bits.subtract a b
      ((s, r.1), c.2 + r.2.2 + 2)

theorem signedAdd_value (s t : Bool) (a b : Bits n)
    (h : a.value + b.value < 2 ^ n) :
    signed (signedAdd s t a b).1.1 (signedAdd s t a b).1.2.value =
      signed s a.value + signed t b.value := by
  have ha := (Bits.add_value_of_lt a b h).2
  have hc := (Bits.compare_correct a b).1
  simp only [signedAdd]
  split
  next heq =>
    subst t
    rw [ha]
    cases s <;> simp [signed, add_comm]
  next hne =>
    split
    next hlt =>
      have hab : a.value ≤ b.value := (hc.mp hlt).le
      rw [(Bits.subtract_value_of_le _ _ hab).2]
      cases s <;> cases t <;> simp_all [signed, Int.ofNat_sub, sub_eq_add_neg, add_comm]
    next hge =>
      have hba : b.value ≤ a.value := Nat.le_of_not_gt (mt hc.mpr hge)
      rw [(Bits.subtract_value_of_le _ _ hba).2]
      cases s <;> cases t <;> simp_all [signed, Int.ofNat_sub, sub_eq_add_neg, add_comm]

theorem signedAdd_steps (s t : Bool) (a b : Bits n) :
    (signedAdd s t a b).2 ≤ 3 * n + 6 := by
  have ha := Bits.add_steps a b
  have hc := Bits.compare_steps a b
  have hab := Bits.subtract_steps a b
  have hba := Bits.subtract_steps b a
  simp only [signedAdd]
  split
  · omega
  · split <;> omega

/-- Raw signed multiplication, followed by canonical binary normalization. -/
def multiply (q r : Word n) : Word n × ℕ :=
  let a := Bits.multiply q.magnitude r.magnitude
  let d := Bits.multiply q.denominator r.denominator
  let z := normalize ⟨xor q.negative r.negative, a.1, d.1⟩
  (z.1, a.2 + d.2 + z.2 + 2)

theorem multiply_value (q r : Word n)
    (hq : 0 < q.denominator.value) (hr : 0 < r.denominator.value)
    (ha : q.magnitude.value * r.magnitude.value < 2 ^ n)
    (hd : q.denominator.value * r.denominator.value < 2 ^ n) :
    (multiply q r).1.value = q.value * r.value := by
  let raw : Word n := ⟨xor q.negative r.negative,
    (Bits.multiply q.magnitude r.magnitude).1,
    (Bits.multiply q.denominator r.denominator).1⟩
  have hn : raw.numerator = q.numerator * r.numerator := by
    change signed (xor q.negative r.negative)
      (Bits.multiply q.magnitude r.magnitude).1.value = _
    rw [Bits.multiply_value_of_lt _ _ ha, signed_mul]
    rfl
  have hden : raw.denominator.value = q.denominator.value * r.denominator.value :=
    Bits.multiply_value_of_lt _ _ hd
  have hraw : 0 < raw.denominator.value := by rw [hden]; positivity
  change (normalize raw).1.value = _
  rw [normalize_value raw hraw]
  unfold Word.value
  rw [hn, hden]
  push_cast
  ring

theorem multiply_steps (q r : Word n) :
    (multiply q r).2 ≤ 8 * n ^ 3 + 42 * n ^ 2 + 61 * n + 27 := by
  have ha := Bits.multiply_steps q.magnitude r.magnitude
  have hd := Bits.multiply_steps q.denominator r.denominator
  have hn := normalize_steps (Word.mk (xor q.negative r.negative)
    (Bits.multiply q.magnitude r.magnitude).1
    (Bits.multiply q.denominator r.denominator).1)
  unfold multiply
  nlinarith

/-- Division by a nonzero rational uses a crossed product before normalization. -/
def divide (q r : Word n) : Word n × ℕ :=
  let a := Bits.multiply q.magnitude r.denominator
  let d := Bits.multiply q.denominator r.magnitude
  let z := normalize ⟨xor q.negative r.negative, a.1, d.1⟩
  (z.1, a.2 + d.2 + z.2 + 2)

theorem divide_value (q r : Word n)
    (hq : 0 < q.denominator.value) (hr : 0 < r.denominator.value)
    (hrn : 0 < r.magnitude.value)
    (ha : q.magnitude.value * r.denominator.value < 2 ^ n)
    (hd : q.denominator.value * r.magnitude.value < 2 ^ n) :
    (divide q r).1.value = q.value / r.value := by
  let raw : Word n := ⟨xor q.negative r.negative,
    (Bits.multiply q.magnitude r.denominator).1,
    (Bits.multiply q.denominator r.magnitude).1⟩
  have hnum : raw.magnitude.value = q.magnitude.value * r.denominator.value :=
    Bits.multiply_value_of_lt _ _ ha
  have hden : raw.denominator.value = q.denominator.value * r.magnitude.value :=
    Bits.multiply_value_of_lt _ _ hd
  have hraw : 0 < raw.denominator.value := by rw [hden]; positivity
  change (normalize raw).1.value = _
  rw [normalize_value raw hraw]
  unfold Word.value Word.numerator
  have hs : raw.negative = xor q.negative r.negative := rfl
  rw [hs, hnum, hden]
  cases hqs : q.negative <;> cases hrs : r.negative <;>
    simp [hqs, hrs, div_div_eq_mul_div, div_mul_eq_mul_div]
  all_goals ring

theorem divide_steps (q r : Word n) :
    (divide q r).2 ≤ 8 * n ^ 3 + 42 * n ^ 2 + 61 * n + 27 := by
  have ha := Bits.multiply_steps q.magnitude r.denominator
  have hd := Bits.multiply_steps q.denominator r.magnitude
  have hn := normalize_steps (Word.mk (xor q.negative r.negative)
    (Bits.multiply q.magnitude r.denominator).1
    (Bits.multiply q.denominator r.magnitude).1)
  unfold divide
  nlinarith

/-- Addition computes both cross products and their signed sum explicitly. -/
def add (q r : Word n) : Word n × ℕ :=
  let a := Bits.multiply q.magnitude r.denominator
  let b := Bits.multiply r.magnitude q.denominator
  let d := Bits.multiply q.denominator r.denominator
  let s := signedAdd q.negative r.negative a.1 b.1
  let z := normalize ⟨s.1.1, s.1.2, d.1⟩
  (z.1, a.2 + b.2 + d.2 + s.2 + z.2 + 3)

theorem add_value (q r : Word n)
    (hq : 0 < q.denominator.value) (hr : 0 < r.denominator.value)
    (ha : q.magnitude.value * r.denominator.value +
      r.magnitude.value * q.denominator.value < 2 ^ n)
    (hd : q.denominator.value * r.denominator.value < 2 ^ n) :
    (add q r).1.value = q.value + r.value := by
  let a := Bits.multiply q.magnitude r.denominator
  let b := Bits.multiply r.magnitude q.denominator
  let d := Bits.multiply q.denominator r.denominator
  let s := signedAdd q.negative r.negative a.1 b.1
  let raw : Word n := ⟨s.1.1, s.1.2, d.1⟩
  have hav : a.1.value = q.magnitude.value * r.denominator.value :=
    Bits.multiply_value_of_lt _ _ (by omega)
  have hbv : b.1.value = r.magnitude.value * q.denominator.value :=
    Bits.multiply_value_of_lt _ _ (by omega)
  have hdv : raw.denominator.value = q.denominator.value * r.denominator.value :=
    Bits.multiply_value_of_lt _ _ hd
  have hs : raw.numerator = q.numerator * r.denominator.value +
      r.numerator * q.denominator.value := by
    have hh := signedAdd_value q.negative r.negative a.1 b.1 (by rw [hav, hbv]; exact ha)
    change signed s.1.1 s.1.2.value = _
    rw [hh, hav, hbv]
    cases hqs : q.negative <;> cases hrs : r.negative <;>
      simp [signed, Word.numerator, hqs, hrs]
  have hraw : 0 < raw.denominator.value := by rw [hdv]; positivity
  change (normalize raw).1.value = _
  rw [normalize_value raw hraw]
  unfold Word.value
  rw [hs, hdv]
  push_cast
  have hq0 : (q.denominator.value : ℚ) ≠ 0 := by positivity
  have hr0 : (r.denominator.value : ℚ) ≠ 0 := by positivity
  field_simp <;> ring

theorem add_steps (q r : Word n) :
    (add q r).2 ≤ 8 * n ^ 3 + 44 * n ^ 2 + 68 * n + 36 := by
  have ha := Bits.multiply_steps q.magnitude r.denominator
  have hb := Bits.multiply_steps r.magnitude q.denominator
  have hd := Bits.multiply_steps q.denominator r.denominator
  have hs := signedAdd_steps q.negative r.negative
    (Bits.multiply q.magnitude r.denominator).1 (Bits.multiply r.magnitude q.denominator).1
  have hn := normalize_steps (Word.mk
    (signedAdd q.negative r.negative (Bits.multiply q.magnitude r.denominator).1
      (Bits.multiply r.magnitude q.denominator).1).1.1
    (signedAdd q.negative r.negative (Bits.multiply q.magnitude r.denominator).1
      (Bits.multiply r.magnitude q.denominator).1).1.2
    (Bits.multiply q.denominator r.denominator).1)
  unfold add
  nlinarith

/-- Negation only changes the sign bit. -/
def negate (q : Word n) : Word n := ⟨!q.negative, q.magnitude, q.denominator⟩

theorem negate_value (q : Word n) : (negate q).value = -q.value := by
  cases h : q.negative <;> simp [Word.value, Word.numerator, negate, h, neg_div]

def subtract (q r : Word n) : Word n × ℕ :=
  let z := add q (negate r)
  (z.1, z.2 + 1)

theorem subtract_value (q r : Word n)
    (hq : 0 < q.denominator.value) (hr : 0 < r.denominator.value)
    (ha : q.magnitude.value * r.denominator.value +
      r.magnitude.value * q.denominator.value < 2 ^ n)
    (hd : q.denominator.value * r.denominator.value < 2 ^ n) :
    (subtract q r).1.value = q.value - r.value := by
  simpa [subtract, negate_value, sub_eq_add_neg] using add_value q (negate r) hq hr ha hd

theorem subtract_steps (q r : Word n) :
    (subtract q r).2 ≤ 8 * n ^ 3 + 44 * n ^ 2 + 68 * n + 37 := by
  have h := add_steps q (negate r)
  simp only [subtract]
  omega

end WeightedMIS.BinaryRational
