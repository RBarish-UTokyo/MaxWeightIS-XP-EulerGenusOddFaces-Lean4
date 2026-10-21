module

public import WeightedMIS.EliminationCertificate
public import WeightedMIS.StoredElimination

/-!
# Width of rational arithmetic in elimination

Normalized rational coordinates have the Gram determinant bounds. The local
arithmetic lemmas below also bound every dot-product partial sum, pivot ratio,
product, and subtraction evaluated between stored elimination states.
-/

@[expose] public section

namespace WeightedMIS.RationalWidth

open Matrix RationalElimination

/-- Both normalized rational components fit the given binary width. -/
def Fits (q : ℚ) (B : ℕ) : Prop := q.num.natAbs.size ≤ B ∧ q.den.size ≤ B

theorem fits_iff (q : ℚ) (B : ℕ) : Fits q B ↔
    q.num.natAbs < 2 ^ B ∧ q.den < 2 ^ B := by
  simp only [Fits, Nat.size_le]

theorem fits_mono {q : ℚ} {a b : ℕ} (h : Fits q a) (hab : a ≤ b) : Fits q b :=
  ⟨h.1.trans hab, h.2.trans hab⟩

theorem fits_zero : Fits 0 1 := by simp [Fits]

theorem fits_int (z : ℤ) (B : ℕ) (hz : z.natAbs ≤ 2 ^ B) : Fits (z : ℚ) (B + 1) := by
  apply (fits_iff _ _).mpr
  simp only [Rat.num_intCast, Rat.den_intCast]
  constructor
  · have hp : 0 < 2 ^ B := by positivity
    rw [pow_succ]
    omega
  · exact Nat.one_lt_two_pow (by omega)

theorem fits_ratio (a b : ℤ) (hb : b ≠ 0) (B : ℕ)
    (ha : a.natAbs < 2 ^ B) (hbb : b.natAbs < 2 ^ B) : Fits ((a : ℚ) / b) B := by
  apply (fits_iff _ _).mpr
  exact ⟨(DeterminantSize.ratio_num_le a b hb).trans_lt ha,
    (DeterminantSize.ratio_den_le a b hb).trans_lt hbb⟩

theorem fits_mul {q r : ℚ} {a b : ℕ} (hq : Fits q a) (hr : Fits r b) :
    Fits (q * r) (a + b) := by
  have hq' := (fits_iff q a).mp hq
  have hr' := (fits_iff r b).mp hr
  have heq : q * r = ((q.num * r.num : ℤ) : ℚ) / (((q.den : ℤ) * r.den : ℤ) : ℚ) := by
    push_cast
    rw [← div_mul_div_comm, Rat.num_div_den, Rat.num_div_den]
  rw [heq]
  apply fits_ratio _ _ (by exact_mod_cast (Nat.mul_ne_zero q.den_ne_zero r.den_ne_zero))
  · simpa only [Int.natAbs_mul, pow_add] using
      Nat.mul_lt_mul_of_lt_of_lt hq'.1 hr'.1
  · simpa only [Int.natAbs_mul, Int.natAbs_natCast, pow_add] using
      Nat.mul_lt_mul_of_lt_of_lt hq'.2 hr'.2

theorem fits_inv {q : ℚ} {a : ℕ} (hq : Fits q a) : Fits q⁻¹ a := by
  by_cases hq0 : q = 0
  · simpa [hq0] using hq
  · have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq0
    simpa [Fits, Rat.num_inv, Rat.den_inv, hn, Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero hn] using And.intro hq.2 hq.1

theorem fits_div {q r : ℚ} {a b : ℕ} (hq : Fits q a) (hr : Fits r b) :
    Fits (q / r) (a + b) := by
  rw [div_eq_mul_inv]
  exact fits_mul hq (fits_inv hr)

theorem fits_neg {q : ℚ} {a : ℕ} (hq : Fits q a) : Fits (-q) a := by
  simpa [Fits] using hq

theorem fits_add {q r : ℚ} {a b : ℕ} (hq : Fits q a) (hr : Fits r b) :
    Fits (q + r) (a + b + 1) := by
  have hq' := (fits_iff q a).mp hq
  have hr' := (fits_iff r b).mp hr
  have heq : q + r = ((q.num * r.den + r.num * q.den : ℤ) : ℚ) /
      (((q.den : ℤ) * r.den : ℤ) : ℚ) := by
    push_cast
    have hqd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    have hrd : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    rw [mul_comm (r.num : ℚ) (q.den : ℚ), ← div_add_div _ _ hqd hrd,
      Rat.num_div_den, Rat.num_div_den]
  rw [heq]
  apply fits_ratio _ _ (by exact_mod_cast (Nat.mul_ne_zero q.den_ne_zero r.den_ne_zero))
  · calc
      _ ≤ (q.num * r.den).natAbs + (r.num * q.den).natAbs := Int.natAbs_add_le _ _
      _ < 2 ^ a * 2 ^ b + 2 ^ b * 2 ^ a := by
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.add_lt_add (Nat.mul_lt_mul_of_lt_of_lt hq'.1 hr'.2)
          (Nat.mul_lt_mul_of_lt_of_lt hr'.1 hq'.2)
      _ = 2 ^ (a + b + 1) := by rw [pow_succ, pow_add]; ring
  · calc
      _ < 2 ^ a * 2 ^ b := by
        simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
          Nat.mul_lt_mul_of_lt_of_lt hq'.2 hr'.2
      _ ≤ 2 ^ (a + b + 1) := by rw [← pow_add, pow_succ]; omega

theorem fits_sub {q r : ℚ} {a b : ℕ} (hq : Fits q a) (hr : Fits r b) :
    Fits (q - r) (a + b + 1) := by
  rw [sub_eq_add_neg]
  exact fits_add hq (fits_neg hr)

/-- Every partial sum has width linear in the number and width of its terms. -/
theorem fits_sum (xs : List ℚ) (B : ℕ) (hxs : ∀ x ∈ xs, Fits x B) :
    Fits xs.sum ((B + 1) * xs.length + 1) := by
  induction xs with
  | nil => simpa using fits_zero
  | cons x xs ih =>
      have hh := fits_add (hxs x (by simp))
        (ih (fun y hy => hxs y (by simp [hy])))
      convert hh using 1 <;> simp only [List.sum_cons, List.length_cons] <;> congr 1 <;> ring

theorem fits_sum_take (xs : List ℚ) (B : ℕ) (hxs : ∀ x ∈ xs, Fits x B) (k : ℕ) :
    Fits (xs.take k).sum ((B + 1) * xs.length + 1) := by
  apply fits_mono (fits_sum (xs.take k) B (fun x hx => hxs x (List.mem_of_mem_take hx)))
  have hlen : (xs.take k).length ≤ xs.length := by simp
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (B + 1) hlen) 1

theorem fits_dot {m : ℕ} (c v : Fin m → ℚ) (B W : ℕ)
    (hc : ∀ i, Fits (c i) B) (hv : ∀ i, Fits (v i) W) :
    Fits (dotProduct c v) ((B + W + 1) * m + 1) := by
  have h := fits_sum (List.ofFn (fun i => c i * v i)) (B + W) (by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact fits_mul (hc i) (hv i))
  simpa only [List.sum_ofFn, List.length_ofFn, dotProduct] using h

/-- A projection's transient ratio, multiplication and subtraction have
polynomial width in the dimensions and stored coordinate widths. -/
theorem project_coordinate_fits {m : ℕ} (c p v : Fin m → ℚ) (B W : ℕ)
    (hc : ∀ i, Fits (c i) B) (hp : ∀ i, Fits (p i) W) (hv : ∀ i, Fits (v i) W)
    (j : Fin m) :
    Fits (project (rowMap c) p v j) (2 * ((B + W + 1) * m + 1) + 2 * W + 1) := by
  rw [project_apply]
  change Fits (v j - (dotProduct c v / dotProduct c p) * p j) _
  have h := fits_sub (hv j)
    (fits_mul (fits_div (fits_dot c v B W hc hv) (fits_dot c p B W hc hp)) (hp j))
  convert h using 1 <;> congr 1 <;> omega

/-- Materialized generator arrays inherit the same bound at every prefix. -/
theorem stored_prefix_fits {m : ℕ} (rows : List (Fin m → ℤ)) (B : ℕ)
    (hrows : ∀ r ∈ rows, ∀ j, (r j).natAbs ≤ 2 ^ B) (k : ℕ)
    (v : Vector ℚ m)
    (hv : v ∈ StoredElimination.eliminateRows
      ((rows.take k).map (fun r => StoredElimination.encode (fun j => (r j : ℚ))))
      (StoredElimination.coordinateVectors m)) (j : Fin m) :
    Fits (StoredElimination.decode v j) ((rows.length + m + 2 * B) * m + m ^ 2 + 1) := by
  have hx := List.mem_map_of_mem (f := StoredElimination.decode) hv
  rw [StoredElimination.decode_eliminateRows, StoredElimination.decode_coordinateVectors] at hx
  simp only [List.map_map, Function.comp_def, StoredElimination.decode_encode] at hx
  exact EliminationCertificate.prefix_coordinate_size rows B hrows k _ hx j

end WeightedMIS.RationalWidth
