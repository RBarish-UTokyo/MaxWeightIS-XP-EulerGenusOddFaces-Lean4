module

public import WeightedMIS.EfficientSearchArithmetic

/-!
# Binary comparison, subtraction, and shifts

The algorithms below inspect stored Boolean cells. Their counters record
those recursive cell operations, rather than assigning unit cost to an
unbounded natural arithmetic operation. Values are used only in specifications.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Bits

/-- Lexicographic comparison of equal-width big-endian words. -/
def compare : {n : ℕ} → Bits n → Bits n → Ordering × ℕ
  | 0, .nil, .nil => (.eq, 1)
  | _ + 1, .cons a as, .cons b bs =>
      if a = b then
        let r := compare as bs
        (r.1, r.2 + 1)
      else (if a then .gt else .lt, 1)

theorem compare_steps {n : ℕ} (a b : Bits n) : (compare a b).2 ≤ n + 1 := by
  induction a with
  | nil => cases b; rfl
  | cons a as ih =>
    cases b with
    | cons b bs =>
      have h := ih bs
      by_cases hab : a = b <;> simp [compare, hab] <;> omega

theorem compare_correct {n : ℕ} (a b : Bits n) :
    ((compare a b).1 = .lt ↔ a.value < b.value) ∧
    ((compare a b).1 = .eq ↔ a.value = b.value) ∧
    ((compare a b).1 = .gt ↔ b.value < a.value) := by
  induction a with
  | nil => cases b; simp [compare, value]
  | @cons n a as ih =>
    cases b with
    | cons b bs =>
      have h := ih bs
      have ha := value_lt as
      have hb := value_lt bs
      cases a <;> cases b <;> simp [compare, value] at * <;> omega

/-- Complement every stored bit, counting the bit visits. -/
def complement : {n : ℕ} → Bits n → Bits n × ℕ
  | 0, .nil => (.nil, 1)
  | _ + 1, .cons a as =>
      let r := complement as
      (.cons (!a) r.1, r.2 + 1)

theorem complement_steps {n : ℕ} (a : Bits n) : (complement a).2 = n + 1 := by
  induction a <;> simp [complement, *]

theorem complement_value {n : ℕ} (a : Bits n) :
    (complement a).1.value + a.value + 1 = 2 ^ n := by
  induction a with
  | nil => rfl
  | cons a as ih => cases a <;> simp [complement, value, pow_succ] at * <;> omega

/-- Subtraction by two's-complement addition. A true final carry means there
was no underflow. -/
def subtract {n : ℕ} (a b : Bits n) : Bits n × Bool × ℕ :=
  let nb := complement b
  let r := addCarry a nb.1 true
  (r.1, r.2.1, nb.2 + r.2.2 + 1)

theorem subtract_steps {n : ℕ} (a b : Bits n) : (subtract a b).2.2 = 2 * n + 3 := by
  simp [subtract, complement_steps, addCarry_steps]
  omega

theorem subtract_value_of_le {n : ℕ} (a b : Bits n) (h : b.value ≤ a.value) :
    (subtract a b).2.1 = true ∧ (subtract a b).1.value = a.value - b.value := by
  have hn := complement_value b
  have hv := addCarry_value a (complement b).1 true
  have hr := value_lt (addCarry a (complement b).1 true).1
  simp only [↓reduceIte] at hv
  unfold subtract
  cases hc : (addCarry a (complement b).1 true).2.1 <;> simp [hc] at * <;> omega

/-- Append a least-significant bit by traversing the stored word. -/
def snoc : {n : ℕ} → Bits n → Bool → Bits (n + 1) × ℕ
  | 0, .nil, b => (.cons b .nil, 1)
  | _ + 1, .cons a as, b =>
      let r := snoc as b
      (.cons a r.1, r.2 + 1)

theorem snoc_steps {n : ℕ} (a : Bits n) (b : Bool) : (snoc a b).2 = n + 1 := by
  induction a <;> simp [snoc, *]

theorem snoc_value {n : ℕ} (a : Bits n) (b : Bool) :
    (snoc a b).1.value = 2 * a.value + (if b then 1 else 0) := by
  induction a with
  | nil => cases b <;> rfl
  | cons a as ih => cases a <;> simp [snoc, value, ih, pow_succ] <;> omega

/-- Shift left one place, dropping the most-significant bit and recording the
traversal needed to append the trailing zero. -/
def shift : {n : ℕ} → Bits n → Bits n × ℕ
  | 0, .nil => (.nil, 1)
  | _ + 1, .cons _ as =>
      let r := snoc as false
      (r.1, r.2 + 1)

theorem shift_steps {n : ℕ} (a : Bits n) : (shift a).2 = n + 1 := by
  cases a <;> simp [shift, snoc_steps]

theorem shift_value {n : ℕ} (a : Bits n) :
    (shift a).1.value = (2 * a.value) % 2 ^ n := by
  cases a with
  | nil => simp [shift, value]
  | @cons n b as =>
    have ha := value_lt as
    have hlt : 2 * as.value < 2 ^ (n + 1) := by rw [pow_succ]; omega
    cases b
    · simpa [shift, snoc_value, value] using (Nat.mod_eq_of_lt hlt).symm
    · have heq : 2 * (2 ^ n + as.value) = 2 ^ (n + 1) + 2 * as.value := by
        rw [pow_succ]
        ring
      simpa [shift, snoc_value, value, heq] using (Nat.mod_eq_of_lt hlt).symm

/-- Addition computes the low bits even when an overflow is returned. -/
theorem add_modEq {n : ℕ} (a b : Bits n) :
    Nat.ModEq (2 ^ n) (add a b).1.value (a.value + b.value) := by
  have h := addCarry_value a b false
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
  change (addCarry a b false).1.value % 2 ^ n = (a.value + b.value) % 2 ^ n
  rw [← h]
  cases hc : (addCarry a b false).2.1 <;> simp [hc]

theorem shift_modEq {n : ℕ} (a : Bits n) :
    Nat.ModEq (2 ^ n) (shift a).1.value (2 * a.value) := by
  rw [shift_value]
  exact Nat.mod_modEq _ _

/-- Horner multiplication scans the multiplier from its most-significant bit.
The accumulator always has the fixed output width. -/
def multiplyAcc {n : ℕ} (a : Bits n) : {m : ℕ} → Bits m → Bits n → Bits n × ℕ
  | 0, .nil, acc => (acc, 1)
  | _ + 1, .cons bit tail, acc =>
      let sh := shift acc
      if bit then
        let ad := add sh.1 a
        let r := multiplyAcc a tail ad.1
        (r.1, sh.2 + ad.2.2 + r.2 + 1)
      else
        let r := multiplyAcc a tail sh.1
        (r.1, sh.2 + r.2 + 1)

theorem multiplyAcc_steps {n m : ℕ} (a : Bits n) (b : Bits m) (acc : Bits n) :
    (multiplyAcc a b acc).2 ≤ (2 * n + 3) * m + 1 := by
  induction b generalizing acc with
  | nil => simp [multiplyAcc]
  | @cons m bit tail ih =>
    have ht := ih (add (shift acc).1 a).1
    have hf := ih (shift acc).1
    cases bit <;> simp only [multiplyAcc, Bool.false_eq_true, ↓reduceIte, shift_steps, add_steps]
    all_goals nlinarith

theorem multiplyAcc_modEq {n m : ℕ} (a : Bits n) (b : Bits m) (acc : Bits n) :
    Nat.ModEq (2 ^ n) (multiplyAcc a b acc).1.value
      (acc.value * 2 ^ m + a.value * b.value) := by
  induction b generalizing acc with
  | nil => simp [multiplyAcc, value, Nat.ModEq]
  | @cons m bit tail ih =>
    cases bit
    · simp only [multiplyAcc, Bool.false_eq_true, ↓reduceIte]
      have hstep := (shift_modEq acc).mul_right (2 ^ m)
      have h := (ih (shift acc).1).trans (hstep.add_right (a.value * tail.value))
      convert h using 1 <;> simp [value, pow_succ] <;> ring
    · simp only [multiplyAcc, ↓reduceIte]
      have hadd := (add_modEq (shift acc).1 a).trans ((shift_modEq acc).add_right a.value)
      have h := (ih (add (shift acc).1 a).1).trans
        ((hadd.mul_right (2 ^ m)).add_right (a.value * tail.value))
      convert h using 1 <;> simp [value, pow_succ] <;> ring

/-- Fixed-width multiplication, with zero-word construction included in the
cell budget. -/
def multiply {n : ℕ} (a b : Bits n) : Bits n × ℕ :=
  let r := multiplyAcc a b (zero n)
  (r.1, n + 1 + r.2)

theorem multiply_steps {n : ℕ} (a b : Bits n) :
    (multiply a b).2 ≤ (2 * n + 3) * n + n + 2 := by
  have h := multiplyAcc_steps a b (zero n)
  simp only [multiply]
  omega

theorem multiply_value {n : ℕ} (a b : Bits n) :
    (multiply a b).1.value = (a.value * b.value) % 2 ^ n := by
  have h := multiplyAcc_modEq a b (zero n)
  simp only [value_zero, Nat.zero_mul, Nat.zero_add] at h
  exact (Nat.mod_eq_of_lt (value_lt _)).symm.trans h

theorem multiply_value_of_lt {n : ℕ} (a b : Bits n)
    (h : a.value * b.value < 2 ^ n) :
    (multiply a b).1.value = a.value * b.value := by
  rw [multiply_value, Nat.mod_eq_of_lt h]

/-- Shift in a specified bit while retaining the fixed word width. -/
def shiftIn : {n : ℕ} → Bits n → Bool → Bits n × ℕ
  | 0, .nil, _ => (.nil, 1)
  | _ + 1, .cons _ as, bit =>
      let r := snoc as bit
      (r.1, r.2 + 1)

theorem shiftIn_steps {n : ℕ} (a : Bits n) (b : Bool) :
    (shiftIn a b).2 = n + 1 := by
  cases a <;> simp [shiftIn, snoc_steps]

theorem shiftIn_value {n : ℕ} (a : Bits n) (bit : Bool) :
    (shiftIn a bit).1.value = (2 * a.value + (if bit then 1 else 0)) % 2 ^ n := by
  cases a with
  | nil => cases bit <;> simp [shiftIn, value]
  | @cons n b as =>
    have ha := value_lt as
    have hb : (if bit then 1 else 0 : ℕ) ≤ 1 := by cases bit <;> decide
    have hlt : 2 * as.value + (if bit then 1 else 0) < 2 ^ (n + 1) := by
      rw [pow_succ]
      omega
    cases b
    · simpa [shiftIn, snoc_value, value] using (Nat.mod_eq_of_lt hlt).symm
    · have heq : 2 * (2 ^ n + as.value) + (if bit then 1 else 0) =
          2 ^ (n + 1) + (2 * as.value + (if bit then 1 else 0)) := by
        rw [pow_succ]
        ring
      simpa [shiftIn, snoc_value, value, heq] using (Nat.mod_eq_of_lt hlt).symm

/-- Restoring long division. The remainder uses one more bit than the
original divisor, so its intermediate left shift cannot overflow. -/
def divideAux {n : ℕ} (den : Bits n) :
    {m : ℕ} → Bits m → Bits n → Bits m × Bits n × ℕ
  | 0, .nil, rem => (.nil, rem, 1)
  | _ + 1, .cons bit tail, rem =>
      let sh := shiftIn rem bit
      let cmp := compare sh.1 den
      if cmp.1 = .lt then
        let r := divideAux den tail sh.1
        (.cons false r.1, r.2.1, sh.2 + cmp.2 + r.2.2 + 1)
      else
        let sub := subtract sh.1 den
        let r := divideAux den tail sub.1
        (.cons true r.1, r.2.1, sh.2 + cmp.2 + sub.2.2 + r.2.2 + 1)

theorem divideAux_steps {n m : ℕ} (den : Bits n) (a : Bits m) (rem : Bits n) :
    (divideAux den a rem).2.2 ≤ (4 * n + 6) * m + 1 := by
  induction a generalizing rem with
  | nil => simp [divideAux]
  | @cons m bit tail ih =>
    have hcmp := compare_steps (shiftIn rem bit).1 den
    have hlo := ih (shiftIn rem bit).1
    have hhi := ih (subtract (shiftIn rem bit).1 den).1
    simp only [divideAux]
    split <;> simp only [shiftIn_steps, subtract_steps]
    all_goals nlinarith

theorem divideAux_correct {n m : ℕ} (den : Bits n) (a : Bits m) (rem : Bits n)
    (hden : 0 < den.value) (hwidth : 2 * den.value ≤ 2 ^ n)
    (hrem : rem.value < den.value) :
    (divideAux den a rem).2.1.value < den.value ∧
      (divideAux den a rem).1.value * den.value + (divideAux den a rem).2.1.value =
        rem.value * 2 ^ m + a.value := by
  induction a generalizing rem with
  | nil => simpa [divideAux, value] using hrem
  | @cons m bit tail ih =>
    have hb : (if bit then 1 else 0 : ℕ) ≤ 1 := by cases bit <;> decide
    have hbound : 2 * rem.value + (if bit then 1 else 0) < 2 * den.value := by omega
    have hsh : (shiftIn rem bit).1.value = 2 * rem.value + (if bit then 1 else 0) := by
      rw [shiftIn_value, Nat.mod_eq_of_lt (hbound.trans_le hwidth)]
    simp only [divideAux]
    split
    · rename_i hcmp
      have hlo := (compare_correct (shiftIn rem bit).1 den).1.mp hcmp
      have hr := ih (shiftIn rem bit).1 hlo
      refine ⟨hr.1, ?_⟩
      simp only [value, Bool.false_eq_true, ↓reduceIte, zero_add]
      rw [hr.2, hsh]
      cases bit <;> simp [value, pow_succ] <;> ring
    · rename_i hcmp
      have hle : den.value ≤ (shiftIn rem bit).1.value := by
        have hnot := mt (compare_correct (shiftIn rem bit).1 den).1.mpr hcmp
        omega
      have hsub := (subtract_value_of_le (shiftIn rem bit).1 den hle).2
      have hrange : (subtract (shiftIn rem bit).1 den).1.value < den.value := by
        rw [hsub, hsh]
        omega
      have hr := ih (subtract (shiftIn rem bit).1 den).1 hrange
      refine ⟨hr.1, ?_⟩
      simp only [value, ↓reduceIte]
      have hsum : (subtract (shiftIn rem bit).1 den).1.value + den.value =
          2 * rem.value + (if bit then 1 else 0) := by
        rw [hsub, Nat.sub_add_cancel hle, hsh]
      have hprod := congrArg (fun x : ℕ => x * 2 ^ m) hsum
      cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, pow_succ] at *
      all_goals nlinarith only [hr.2, hprod]

/-- Long division of two n-bit words. The zero-divisor convention agrees
with natural division and remainder. -/
def divide {n : ℕ} (a den : Bits n) : Bits n × Bits (n + 1) × ℕ :=
  let z := zero n
  let cmp := compare den z
  if cmp.1 = .eq then (z, .cons false a, cmp.2 + n + 3)
  else
    let r := divideAux (.cons false den) a (zero (n + 1))
    (r.1, r.2.1, cmp.2 + 2 * n + 6 + r.2.2)

theorem divide_steps {n : ℕ} (a den : Bits n) :
    (divide a den).2.2 ≤ (4 * (n + 1) + 6) * n + 3 * n + 8 := by
  have hcmp := compare_steps den (zero n)
  have haux := divideAux_steps (.cons false den) a (zero (n + 1))
  simp only [divide]
  split <;> nlinarith

theorem divide_value {n : ℕ} (a den : Bits n) :
    (divide a den).1.value = a.value / den.value ∧
      (divide a den).2.1.value = a.value % den.value := by
  have hcmp := (compare_correct den (zero n)).2.1
  simp only [value_zero] at hcmp
  simp only [divide]
  split
  · rename_i hzero
    have hden := hcmp.mp hzero
    simp [value_zero, value, hden]
  · rename_i hne
    have hd : 0 < den.value := Nat.pos_of_ne_zero (mt hcmp.mpr hne)
    have hr := divideAux_correct (.cons false den) a (zero (n + 1))
      (by simpa [value] using hd)
      (by
        simp only [value, Bool.false_eq_true, ↓reduceIte, zero_add, pow_succ]
        have hv := value_lt den
        omega)
      (by simpa [value] using hd)
    simp only [value, Bool.false_eq_true, ↓reduceIte, zero_add, value_zero,
      Nat.zero_mul, Nat.zero_add] at hr
    dsimp only
    constructor
    · apply Eq.symm
      apply Nat.div_eq_of_lt_le
      · omega
      · nlinarith only [hr.1, hr.2]
    · have hmod := congrArg (fun x => x % den.value) hr.2
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hr.1] using hmod

end WeightedMIS.EfficientSearch.Bits
