module

public import WeightedMIS.NodeEncoding

/-!
# Instrumented positional arithmetic

These executable routines record every digit read, loop visit, and natural
addition/multiplication/division/remainder operation. Their output is proved to
match the vertex-encoding tuple arithmetic. Trace lengths and operand widths
are separate from bit-operation complexity: a bit-machine refinement of the
listed arithmetic primitives is still required before asserting a bit runtime.
-/

@[expose] public section

namespace WeightedMIS.EncodingCost

/-- Arithmetic operations charged separately by a later bit-machine refinement. -/
inductive Op where
  | visit
  | read (a : ℕ)
  | add (a b : ℕ)
  | mul (a b : ℕ)
  | div (a b : ℕ)
  | mod (a b : ℕ)
  deriving DecidableEq

/-- The largest operand carried by a trace event. -/
def operand : Op → ℕ
  | .visit => 0
  | .read a => a
  | .add a b | .mul a b | .div a b | .mod a b => max a b

/-- Result and the exact arithmetic trace of a recursive routine. -/
structure Run (α : Type*) where
  value : α
  trace : List Op

/-- Horner encoding, recording one digit read, one multiplication, and one
addition per digit, together with one visit per recursive call. -/
def encodeDigits (base : ℕ) : (n : ℕ) → (Fin n → Fin base) → Run ℕ
  | 0, _ => ⟨0, [.visit]⟩
  | n + 1, f =>
      let tail := encodeDigits base n (fun i => f i.succ)
      let digit := (f 0).val
      let product := base * tail.value
      ⟨digit + product, tail.trace ++ [.visit, .read digit, .mul base tail.value, .add digit product]⟩

/-- Horner encoding equals the positional numeral map used for signature IDs. -/
theorem encodeDigits_value (base n : ℕ) (f : Fin n → Fin base) :
    (encodeDigits base n f).value = (finFunctionFinEquiv f).val := by
  rw [finFunctionFinEquiv_apply]
  induction n with
  | zero => simp [encodeDigits]
  | succ n ih =>
      simp only [encodeDigits, Fin.sum_univ_succ, Fin.val_zero, pow_zero, Nat.mul_one,
        Fin.val_succ]
      rw [ih]
      simp_rw [pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Exact instrumented operation count, including the base call. -/
theorem encodeDigits_trace_length (base n : ℕ) (f : Fin n → Fin base) :
    (encodeDigits base n f).trace.length = 4 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [encodeDigits, List.length_append, List.length_cons, List.length_nil]
      rw [ih]
      omega

theorem encodeDigits_value_lt (base n : ℕ) (f : Fin n → Fin base) :
    (encodeDigits base n f).value < base ^ n := by
  rw [encodeDigits_value]
  exact (finFunctionFinEquiv f).isLt

/-- All arithmetic operands in an encoding stay within its numeral range,
plus the base itself. -/
theorem encodeDigits_operand_le (base n : ℕ) (hb : 1 ≤ base) (f : Fin n → Fin base)
    (op : Op) (hop : op ∈ (encodeDigits base n f).trace) : operand op ≤ base ^ n + base := by
  induction n with
  | zero =>
      simp only [encodeDigits, List.mem_singleton] at hop
      subst op
      simp [operand]
  | succ n ih =>
      simp only [encodeDigits, List.mem_append] at hop
      have hpow : base ^ n ≤ base ^ (n + 1) := by
        rw [pow_succ]
        exact Nat.le_mul_of_pos_right _ hb
      have ht := encodeDigits_value_lt base n (fun i => f i.succ)
      have hd := (f 0).isLt
      rcases hop with hop | hop
      · exact le_trans (ih _ hop) (Nat.add_le_add_right hpow base)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
        rcases hop with rfl | rfl | rfl | rfl
        · simp [operand]
        · simp only [operand]; omega
        · simp only [operand, max_le_iff]; omega
        · simp only [operand, max_le_iff]
          constructor
          · omega
          · have hm := Nat.mul_le_mul_left base (Nat.le_of_lt ht)
            rw [← pow_succ'] at hm
            omega

/-- Repeated quotient/remainder decoding, not a search through all tuples. -/
def decodeDigits (base : ℕ) (hb : 0 < base) : (n : ℕ) → ℕ → Run (Fin n → Fin base)
  | 0, _ => ⟨Fin.elim0, [.visit]⟩
  | n + 1, value =>
      let tail := decodeDigits base hb n (value / base)
      let digit : Fin base := ⟨value % base, Nat.mod_lt value hb⟩
      ⟨Fin.cases digit tail.value, tail.trace ++ [.visit, .mod value base, .div value base]⟩

/-- Exact arithmetic count for decoding every digit of a signature. -/
theorem decodeDigits_trace_length (base n value : ℕ) (hb : 0 < base) :
    (decodeDigits base hb n value).trace.length = 3 * n + 1 := by
  induction n generalizing value with
  | zero => rfl
  | succ n ih =>
      simp only [decodeDigits, List.length_append, List.length_cons, List.length_nil]
      rw [ih]
      omega

/-- Decoding never increases the numeric operand beyond the initial ID or base. -/
theorem decodeDigits_operand_le (base n value : ℕ) (hb : 0 < base)
    (op : Op) (hop : op ∈ (decodeDigits base hb n value).trace) : operand op ≤ max value base := by
  induction n generalizing value with
  | zero =>
      simp only [decodeDigits, List.mem_singleton] at hop
      subst op
      simp [operand]
  | succ n ih =>
      simp only [decodeDigits, List.mem_append] at hop
      rcases hop with hop | hop
      · have h := ih (value / base) hop
        exact le_trans h (max_le_max (Nat.div_le_self _ _) le_rfl)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
        rcases hop with rfl | rfl | rfl <;> simp [operand]

/-- The decoded digit at index i is the ordinary quotient/remainder digit. -/
theorem decodeDigits_digit (base n value : ℕ) (hb : 0 < base) (i : Fin n) :
    ((decodeDigits base hb n value).value i).val = value / base ^ i.val % base := by
  induction n generalizing value with
  | zero => exact i.elim0
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [decodeDigits]
      · simp only [decodeDigits, Fin.cases_succ, Fin.val_succ]
        rw [ih]
        congr 1
        rw [Nat.div_div_eq_div_mul, pow_succ']

/-- Decoding agrees with the executable inverse of the signature-ID equivalence. -/
theorem decodeDigits_equiv (base n : ℕ) (hb : 0 < base) (value : Fin (base ^ n)) :
    (decodeDigits base hb n value.val).value = finFunctionFinEquiv.symm value := by
  funext i
  apply Fin.ext
  rw [decodeDigits_digit]
  rfl

/-- The number of bits in a product is bounded by the sum of operand widths. -/
theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  calc
    a * b < 2 ^ a.size * 2 ^ b.size :=
      Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)
    _ = 2 ^ (a.size + b.size) := (pow_add 2 a.size b.size).symm

/-- Polynomial-size exponents yield linearly growing encoded widths. -/
theorem size_pow_le (base n : ℕ) : (base ^ n).size ≤ n * base.size + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      calc
        (base ^ n * base).size ≤ (base ^ n).size + base.size := size_mul_le _ _
        _ ≤ n * base.size + 1 + base.size := Nat.add_le_add_right ih _
        _ = (n + 1) * base.size + 1 := by ring

/-- Arithmetic operands have an explicit bit-width bound. -/
theorem encodeDigits_operand_bits (base n : ℕ) (hb : 1 ≤ base) (f : Fin n → Fin base)
    (op : Op) (hop : op ∈ (encodeDigits base n f).trace) :
    (operand op).size ≤ (base ^ n + base).size :=
  Nat.size_le_size (encodeDigits_operand_le base n hb f op hop)

theorem decodeDigits_operand_bits (base n value : ℕ) (hb : 0 < base)
    (op : Op) (hop : op ∈ (decodeDigits base hb n value).trace) :
    (operand op).size ≤ (max value base).size :=
  Nat.size_le_size (decodeDigits_operand_le base n value hb op hop)

end WeightedMIS.EncodingCost
