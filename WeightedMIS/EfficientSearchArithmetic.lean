module

public import WeightedMIS.EfficientSearchQueue

/-!
# Explicit binary arithmetic for search keys

The ripple-carry adder operates directly on stored bits.  Its recursive counter
counts one full-adder cell per bit plus the terminal carry cell.  It neither
normalizes rationals nor treats unbounded integer addition as a primitive.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Bits

def zero : (n : ℕ) → Bits n
  | 0 => .nil
  | n + 1 => .cons false (zero n)

@[simp] theorem value_zero (n : ℕ) : (zero n).value = 0 := by
  induction n <;> simp [zero, value, *]

/-- A single Boolean full-adder cell. -/
def fullAdd (a b c : Bool) : Bool × Bool :=
  (xor (xor a b) c, (a && b) || (a && c) || (b && c))

theorem fullAdd_value (a b c : Bool) :
    (if (fullAdd a b c).1 then 1 else 0) +
      2 * (if (fullAdd a b c).2 then 1 else 0) =
    (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> decide

/-- Big-endian ripple-carry addition.  The carry returned from the tail feeds
the next full-adder cell toward the most significant bit. -/
def addCarry : {n : ℕ} → Bits n → Bits n → Bool → Bits n × Bool × ℕ
  | 0, .nil, .nil, carry => (.nil, carry, 1)
  | _ + 1, .cons a as, .cons b bs, carry =>
      let tail := addCarry as bs carry
      let head := fullAdd a b tail.2.1
      (.cons head.1 tail.1, head.2, tail.2.2 + 1)

theorem addCarry_steps {n : ℕ} (a b : Bits n) (carry : Bool) :
    (addCarry a b carry).2.2 = n + 1 := by
  induction a with
  | nil => cases b; rfl
  | cons a as ih => cases b; simp [addCarry, ih]

theorem addCarry_value {n : ℕ} (a b : Bits n) (carry : Bool) :
    (addCarry a b carry).1.value +
      2 ^ n * (if (addCarry a b carry).2.1 then 1 else 0) =
    a.value + b.value + (if carry then 1 else 0) := by
  induction a with
  | nil => cases b; cases carry <;> rfl
  | @cons n a as ih =>
    cases b with
    | cons b bs =>
      have hitail := ih bs
      have hfull := fullAdd_value a b (addCarry as bs carry).2.1
      simp only [addCarry, value, pow_succ]
      cases a <;> cases b <;> cases hc : (addCarry as bs carry).2.1 <;>
        simp [fullAdd, hc] at * <;> omega

/-- Addition returns the low bits and an overflow flag. -/
def add {n : ℕ} (a b : Bits n) : Bits n × Bool × ℕ := addCarry a b false

theorem add_steps {n : ℕ} (a b : Bits n) : (add a b).2.2 = n + 1 :=
  addCarry_steps a b false

theorem add_value_of_lt {n : ℕ} (a b : Bits n) (h : a.value + b.value < 2 ^ n) :
    (add a b).2.1 = false ∧ (add a b).1.value = a.value + b.value := by
  have hv := addCarry_value a b false
  simp only [add, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at *
  cases hc : (addCarry a b false).2.1
  · simp [hc] at hv
    exact ⟨rfl, hv⟩
  · simp [hc] at hv
    omega

theorem add_value_of_no_overflow {n : ℕ} (a b : Bits n) (h : (add a b).2.1 = false) :
    (add a b).1.value = a.value + b.value := by
  have hv := addCarry_value a b false
  change (add a b).1.value + 2 ^ n * (if (add a b).2.1 then 1 else 0) =
    a.value + b.value + 0 at hv
  simpa [h] using hv

end WeightedMIS.EfficientSearch.Bits
