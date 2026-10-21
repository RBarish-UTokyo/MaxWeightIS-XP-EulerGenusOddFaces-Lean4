module

public import WeightedMIS.EfficientSearchArithmeticMore

/-!
# Binary Euclidean normalization

The Euclidean algorithm below uses the verified bitwise long divider. Each
recursive round performs at most two divisions. The second remainder is less
than half the previous divisor, giving a linear number of rounds in the input
word width and a cubic bound on the recorded bit-operation count.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Bits

/-- Drop the most significant bit. Remainders fit the original input width. -/
def low {n : ℕ} : Bits (n + 1) → Bits n
  | .cons _ tail => tail

theorem low_value {n : ℕ} (a : Bits (n + 1)) (h : a.value < 2 ^ n) :
    (low a).value = a.value := by
  cases a with
  | cons bit tail => cases bit <;> simp_all [low, value]

/-- The remainder of long division, stored in the original word width. -/
def remainder {n : ℕ} (a b : Bits n) : Bits n × ℕ :=
  let q := divide a b
  (low q.2.1, q.2.2 + 1)

theorem remainder_value {n : ℕ} (a b : Bits n) :
    (remainder a b).1.value = a.value % b.value := by
  have h := (divide_value a b).2
  have hlt : (divide a b).2.1.value < 2 ^ n := by
    rw [h]
    exact (Nat.mod_le _ _).trans_lt (value_lt a)
  exact (low_value _ hlt).trans h

def divisionBound (n : ℕ) : ℕ := (4 * (n + 1) + 6) * n + 3 * n + 8

theorem remainder_steps {n : ℕ} (a b : Bits n) :
    (remainder a b).2 ≤ divisionBound n + 1 := by
  exact Nat.add_le_add_right (divide_steps a b) 1

/-- The second remainder reduces the divisor's power-of-two bound. -/
theorem second_remainder_lt {b r k : ℕ} (hb : b < 2 ^ (k + 1)) (hr : r < b) (hz : r ≠ 0) :
    b % r < 2 ^ k := by
  by_cases hs : r ≤ 2 ^ k
  · exact (Nat.mod_lt b (Nat.pos_of_ne_zero hz)).trans_le hs
  · have hbr : r ≤ b := Nat.le_of_lt hr
    have hsub : b - r < r := by
      rw [pow_succ] at hb
      omega
    rw [Nat.mod_eq_sub_mod hbr, Nat.mod_eq_of_lt hsub]
    rw [pow_succ] at hb
    omega

/-- Euclidean iteration, with at most two long divisions per round. -/
def euclid {n : ℕ} : ℕ → Bits n → Bits n → Bits n × ℕ
  | 0, a, _ => (a, 1)
  | k + 1, a, b =>
      let cb := compare b (zero n)
      if cb.1 = .eq then (a, cb.2 + n + 2)
      else
        let r := remainder a b
        let cr := compare r.1 (zero n)
        if cr.1 = .eq then (b, cb.2 + r.2 + cr.2 + 2 * n + 4)
        else
          let t := remainder b r.1
          let next := euclid k r.1 t.1
          (next.1, cb.2 + r.2 + cr.2 + t.2 + next.2 + 2 * n + 5)

theorem gcd_step (a b : ℕ) : Nat.gcd a b = Nat.gcd b (a % b) := by
  rw [Nat.gcd_comm a b, Nat.gcd_rec]
  exact Nat.gcd_comm _ _

/-- The fuel needed is a bound on the divisor's binary width, independent of
the numerical size of the dividend. -/
theorem euclid_value {n k : ℕ} (a b : Bits n) (hb : b.value < 2 ^ k) :
    (euclid k a b).1.value = Nat.gcd a.value b.value := by
  induction k generalizing a b with
  | zero =>
      have hb0 : b.value = 0 := by simpa using hb
      simp [euclid, hb0]
  | succ k ih =>
      have hc := (compare_correct b (zero n)).2.1
      simp only [value_zero] at hc
      simp only [euclid]
      split
      next hz => simp [hc.mp hz]
      next hn =>
        have hb0 : b.value ≠ 0 := mt hc.mpr hn
        have hr := remainder_value a b
        have hrc := (compare_correct (remainder a b).1 (zero n)).2.1
        simp only [value_zero] at hrc
        split
        next hz =>
          rw [gcd_step, ← hr, hrc.mp hz, Nat.gcd_zero_right]
        next hne =>
          have hrl : (remainder a b).1.value < b.value := by
            rw [hr]
            exact Nat.mod_lt _ (Nat.pos_of_ne_zero hb0)
          have ht := remainder_value b (remainder a b).1
          have htbound : (remainder b (remainder a b).1).1.value < 2 ^ k := by
            rw [ht]
            exact second_remainder_lt hb hrl (mt hrc.mpr hne)
          rw [ih _ _ htbound, gcd_step a.value b.value, ← hr,
            gcd_step b.value (remainder a b).1.value, ← ht]

def euclidRoundBound (n : ℕ) : ℕ := 2 * divisionBound n + 4 * n + 10

theorem euclid_steps {n : ℕ} (k : ℕ) (a b : Bits n) :
    (euclid k a b).2 ≤ k * euclidRoundBound n + n + 2 := by
  induction k generalizing a b with
  | zero => simp [euclid]
  | succ k ih =>
      have hc := compare_steps b (zero n)
      have hr := remainder_steps a b
      have hrc := compare_steps (remainder a b).1 (zero n)
      have ht := remainder_steps b (remainder a b).1
      have hi := ih (remainder a b).1 (remainder b (remainder a b).1).1
      simp only [euclid]
      split
      · unfold euclidRoundBound; nlinarith
      · split <;> (unfold euclidRoundBound at *; nlinarith)

/-- Binary gcd on n-bit input words. -/
def gcd {n : ℕ} (a b : Bits n) : Bits n × ℕ := euclid n a b

theorem gcd_value {n : ℕ} (a b : Bits n) :
    (gcd a b).1.value = Nat.gcd a.value b.value :=
  euclid_value a b (value_lt b)

theorem gcd_steps {n : ℕ} (a b : Bits n) :
    (gcd a b).2 ≤ 8 * n ^ 3 + 30 * n ^ 2 + 27 * n + 2 := by
  have h := euclid_steps n a b
  unfold euclidRoundBound divisionBound at h
  change (euclid n a b).2 ≤ _
  nlinarith

end WeightedMIS.EfficientSearch.Bits
