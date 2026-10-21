module

public import WeightedMIS.Parameters
public import WeightedMIS.Spec
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Normal forms for the final running-time budget

A budget in normal form is `Shape c a b N L = c * N ^ a * (L + 1) ^ b`, where
`N` is the instance size, `L` the weight-bit length and `c` a coefficient that
may depend on the parameter only. This file collects the closure properties of
such shapes, the per-component estimate for the hard-component search
(`K (4m+1)^d (r+m+d+G+2)^6`) in normal form with a single-exponential
coefficient `stageFactor K a p`, and the summation over at most `N`
components.
-/

@[expose] public section

namespace WeightedMIS.FinalBudget

open scoped BigOperators

/-- The normal form `c * N ^ a * (L + 1) ^ b`. -/
def Shape (c a b N L : ℕ) : ℕ := c * N ^ a * (L + 1) ^ b

theorem size_le_self (x : ℕ) : x.size ≤ x := Nat.size_le.mpr x.lt_two_pow_self

theorem succ_le_two_pow (p : ℕ) : p + 1 ≤ 2 ^ p := p.lt_two_pow_self

theorem shape_mono {c c' a a' b b' N L : ℕ} (hN : 1 ≤ N) (hc : c ≤ c') (ha : a ≤ a')
    (hb : b ≤ b') : Shape c a b N L ≤ Shape c' a' b' N L := by
  unfold Shape
  exact Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_right hN ha))
    (Nat.pow_le_pow_right (by omega) hb)

theorem shape_mono_size {c a b N N' L L' : ℕ} (hN : N ≤ N') (hL : L ≤ L') :
    Shape c a b N L ≤ Shape c a b N' L' := by
  unfold Shape
  exact Nat.mul_le_mul (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hN a))
    (Nat.pow_le_pow_left (by omega) b)

theorem shape_add_same (c₁ c₂ a b N L : ℕ) :
    Shape c₁ a b N L + Shape c₂ a b N L = Shape (c₁ + c₂) a b N L := by
  unfold Shape; ring

/-- A sum of shapes is bounded by the shape with summed coefficients and
maximal exponents. -/
theorem shape_add {c₁ c₂ a₁ a₂ b₁ b₂ N L : ℕ} (hN : 1 ≤ N) :
    Shape c₁ a₁ b₁ N L + Shape c₂ a₂ b₂ N L ≤
      Shape (c₁ + c₂) (max a₁ a₂) (max b₁ b₂) N L := by
  rw [← shape_add_same]
  exact Nat.add_le_add (shape_mono hN le_rfl (le_max_left _ _) (le_max_left _ _))
    (shape_mono hN le_rfl (le_max_right _ _) (le_max_right _ _))

theorem shape_mul (c₁ c₂ a₁ a₂ b₁ b₂ N L : ℕ) :
    Shape c₁ a₁ b₁ N L * Shape c₂ a₂ b₂ N L = Shape (c₁ * c₂) (a₁ + a₂) (b₁ + b₂) N L := by
  unfold Shape; ring

theorem shape_pow (c a b N L k : ℕ) :
    Shape c a b N L ^ k = Shape (c ^ k) (a * k) (b * k) N L := by
  unfold Shape; rw [mul_pow, mul_pow, pow_mul, pow_mul]

theorem shape_scale (e c a b N L : ℕ) : e * Shape c a b N L = Shape (e * c) a b N L := by
  unfold Shape; ring

theorem const_le_shape {c a b N L : ℕ} (hN : 1 ≤ N) : c ≤ Shape c a b N L := by
  have := shape_mono (c := c) (a := 0) (b := 0) (N := N) (L := L) (a' := a) (b' := b) hN le_rfl
    (Nat.zero_le _) (Nat.zero_le _)
  simpa [Shape] using this

theorem size_le_shape (N L : ℕ) : N ≤ Shape 1 1 0 N L := by simp [Shape]

theorem bits_le_shape (N L : ℕ) : L + 1 ≤ Shape 1 0 1 N L := by simp [Shape]

/-- `(x + y)^k ≤ 2^k (x^k + y^k)`. -/
theorem add_pow_le (x y k : ℕ) : (x + y) ^ k ≤ 2 ^ k * (x ^ k + y ^ k) := by
  calc (x + y) ^ k ≤ (2 * max x y) ^ k := Nat.pow_le_pow_left (by omega) k
    _ = 2 ^ k * max x y ^ k := Nat.mul_pow 2 _ k
    _ ≤ 2 ^ k * (x ^ k + y ^ k) := by
      apply Nat.mul_le_mul_left
      rcases le_total x y with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega

theorem linear_le (N L : ℕ) (hN : 1 ≤ N) : N + L + 1 ≤ 2 * (N * (L + 1)) := by
  nlinarith

/-- Absorb an affine expression in `N` and `L` into one shape. -/
theorem affine_le_shape (c₀ c₁ c₂ N L : ℕ) (hN : 1 ≤ N) :
    c₀ + c₁ * N + c₂ * (L + 1) ≤ Shape (c₀ + c₁ + c₂) 1 1 N L := by
  unfold Shape
  have h1 : 1 ≤ N * (L + 1) := Nat.mul_pos (by omega) (by omega)
  have h2 : N ≤ N * (L + 1) := Nat.le_mul_of_pos_right N (by omega)
  have h3 : L + 1 ≤ N * (L + 1) := Nat.le_mul_of_pos_left (L + 1) (by omega)
  have e : (c₀ + c₁ + c₂) * N ^ 1 * (L + 1) ^ 1 =
      c₀ * (N * (L + 1)) + c₁ * (N * (L + 1)) + c₂ * (N * (L + 1)) := by ring
  rw [e]
  have := Nat.mul_le_mul_left c₀ h1
  have := Nat.mul_le_mul_left c₁ h2
  have := Nat.mul_le_mul_left c₂ h3
  omega

/-- Absorb a polynomial `X ^ j` where `X ≤ c N (L+1)`. -/
theorem pow_le_shape {X c N L : ℕ} (hX : X ≤ c * (N * (L + 1))) (j : ℕ) :
    X ^ j ≤ Shape (c ^ j) j j N L := by
  unfold Shape
  calc X ^ j ≤ (c * (N * (L + 1))) ^ j := Nat.pow_le_pow_left hX j
    _ = _ := by rw [mul_pow, mul_pow, mul_assoc]

/-! ## Exponents -/

theorem exponentD_eq (γ k : ℕ) : Spec.exponentD γ k = Parameters.exponent γ k := rfl

theorem exponentD_le (γ k : ℕ) : Spec.exponentD γ k ≤ γ + k :=
  Parameters.exponent_le_parameter γ k

theorem orientableExponentD_le_exponentD (γ k : ℕ) :
    Spec.orientableExponentD γ k ≤ Spec.exponentD γ k := by
  unfold Spec.orientableExponentD Spec.exponentD; omega

theorem orientableExponentD_le (γ k : ℕ) : Spec.orientableExponentD γ k ≤ γ + k :=
  (orientableExponentD_le_exponentD γ k).trans (exponentD_le γ k)

/-! ## The per-component search estimate -/

/-- Single-exponential coefficient of the per-component search estimate. -/
def stageFactor (K a p : ℕ) : ℕ := (320 * (K + 1) * (a + 4) ^ 6) ^ (p + 1)

theorem stageFactor_pos (K a p : ℕ) : 0 < stageFactor K a p := by
  unfold stageFactor; positivity

/-- The search width `r + m + d + G + 2` is linear in `N (L+1)` with a
coefficient linear in the parameter. -/
theorem width_le {N L m r d p G a : ℕ} (hN : 1 ≤ N) (hm : m ≤ N) (hr : r ≤ 4 * N)
    (hd : d ≤ p) (hG : G ≤ a * (d + 1) * (N + L + 1)) :
    r + m + d + G + 2 ≤ 2 * (a + 4) * (p + 1) * (N * (L + 1)) := by
  set M := N * (L + 1) with hMdef
  have hM1 : 1 ≤ M := Nat.mul_pos (by omega) (by omega)
  have hNM : N ≤ M := Nat.le_mul_of_pos_right N (by omega)
  have hLM : N + L + 1 ≤ 2 * M := linear_le N L hN
  have hG' : G ≤ a * (p + 1) * (2 * M) :=
    hG.trans (Nat.mul_le_mul (Nat.mul_le_mul_left a (by omega)) hLM)
  have hdM : d + 2 ≤ (p + 2) * M :=
    le_trans (by omega : d + 2 ≤ (p + 2) * 1) (Nat.mul_le_mul_left _ hM1)
  have e1 : a * (p + 1) * (2 * M) = 2 * (a * ((p + 1) * M)) := by ring
  have e2 : (p + 2) * M = (p + 1) * M + M := by ring
  have e3 : 2 * (a + 4) * (p + 1) * M = 2 * (a * ((p + 1) * M)) + 8 * ((p + 1) * M) := by ring
  have h4 : M ≤ (p + 1) * M := Nat.le_mul_of_pos_left M (by omega)
  omega

/-- The per-component hard-search estimate in normal form. The width `G` is a
parameter bounded by `a (d+1) (N+L+1)`; `m ≤ N` counts the component's
residual vertices, `r ≤ 4N` is the residual radius and `d ≤ D ≤ p`. -/
theorem stage_bound {K a N L m r d D p G : ℕ} (hN : 1 ≤ N) (hm : m ≤ N) (hr : r ≤ 4 * N)
    (hdD : d ≤ D) (hDp : D ≤ p) (hG : G ≤ a * (d + 1) * (N + L + 1)) :
    K * (4 * m + 1) ^ d * (r + m + d + G + 2) ^ 6 ≤
      stageFactor K a p * N ^ (D + 6) * (L + 1) ^ 6 := by
  have hbox : (4 * m + 1) ^ d ≤ 5 ^ p * N ^ D :=
    (Parameters.box_size_bound m d N hm hN).trans
      (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (hdD.trans hDp))
        (Nat.pow_le_pow_right hN hdD))
  have hw := width_le (L := L) (a := a) hN hm hr (hdD.trans hDp) hG
  have hX : (r + m + d + G + 2) ^ 6 ≤
      (2 * (a + 4)) ^ 6 * (p + 1) ^ 6 * N ^ 6 * (L + 1) ^ 6 := by
    calc _ ≤ (2 * (a + 4) * (p + 1) * (N * (L + 1))) ^ 6 := Nat.pow_le_pow_left hw 6
      _ = _ := by ring
  have hp : (p + 1) ^ 6 ≤ 64 ^ p := by
    calc (p + 1) ^ 6 ≤ (2 ^ p) ^ 6 := Nat.pow_le_pow_left (succ_le_two_pow p) 6
      _ = 64 ^ p := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hcoef : K * 5 ^ p * ((2 * (a + 4)) ^ 6 * 64 ^ p) ≤ stageFactor K a p := by
    have hK : K ≤ (K + 1) ^ (p + 1) :=
      (Nat.le_succ K).trans (Nat.le_self_pow (by omega) _)
    have hA : (a + 4) ^ 6 ≤ ((a + 4) ^ 6) ^ (p + 1) :=
      Nat.le_self_pow (by omega) _
    have e : K * 5 ^ p * ((2 * (a + 4)) ^ 6 * 64 ^ p) =
        64 * 320 ^ p * (K * (a + 4) ^ 6) := by
      rw [show (320 : ℕ) ^ p = 5 ^ p * 64 ^ p by rw [← mul_pow]; norm_num]; ring
    rw [e]
    unfold stageFactor
    calc 64 * 320 ^ p * (K * (a + 4) ^ 6) = 320 ^ p * 64 * (K * (a + 4) ^ 6) := by ring
      _ ≤ 320 ^ p * 320 * ((K + 1) ^ (p + 1) * ((a + 4) ^ 6) ^ (p + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by norm_num)) (Nat.mul_le_mul hK hA)
      _ = _ := by rw [mul_pow (320 * (K + 1)), mul_pow 320 (K + 1), pow_succ 320 p]; ring
  calc K * (4 * m + 1) ^ d * (r + m + d + G + 2) ^ 6 ≤
      K * (5 ^ p * N ^ D) * ((2 * (a + 4)) ^ 6 * 64 ^ p * N ^ 6 * (L + 1) ^ 6) := by
        refine Nat.mul_le_mul (Nat.mul_le_mul_left K hbox) (hX.trans ?_)
        gcongr
    _ = (K * 5 ^ p * ((2 * (a + 4)) ^ 6 * 64 ^ p)) * N ^ (D + 6) * (L + 1) ^ 6 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoef)

/-- `stage_bound` for the general exponent, with parameter `γ + k`. -/
theorem stage_bound_exponentD {K a N L m r d G γ k : ℕ} (hN : 1 ≤ N) (hm : m ≤ N)
    (hr : r ≤ 4 * N) (hd : d ≤ Spec.exponentD γ k) (hG : G ≤ a * (d + 1) * (N + L + 1)) :
    K * (4 * m + 1) ^ d * (r + m + d + G + 2) ^ 6 ≤
      stageFactor K a (γ + k) * N ^ (Spec.exponentD γ k + 6) * (L + 1) ^ 6 :=
  stage_bound hN hm hr hd (exponentD_le γ k) hG

/-- `stage_bound` for the orientable exponent, with parameter `γ + k`. -/
theorem stage_bound_orientableExponentD {K a N L m r d G γ k : ℕ} (hN : 1 ≤ N) (hm : m ≤ N)
    (hr : r ≤ 4 * N) (hd : d ≤ Spec.orientableExponentD γ k)
    (hG : G ≤ a * (d + 1) * (N + L + 1)) :
    K * (4 * m + 1) ^ d * (r + m + d + G + 2) ^ 6 ≤
      stageFactor K a (γ + k) * N ^ (Spec.orientableExponentD γ k + 6) * (L + 1) ^ 6 :=
  stage_bound hN hm hr hd (orientableExponentD_le γ k) hG

/-! ## Summation over components -/

theorem finset_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℕ) {N B : ℕ} (hs : s.card ≤ N)
    (hc : ∀ i ∈ s, c i ≤ B) : ∑ i ∈ s, c i ≤ N * B :=
  (Finset.sum_le_card_nsmul s c B hc).trans (by rw [smul_eq_mul]; exact Nat.mul_le_mul_right B hs)

theorem list_sum_le (l : List ℕ) {N B : ℕ} (hl : l.length ≤ N) (hc : ∀ x ∈ l, x ≤ B) :
    l.sum ≤ N * B :=
  (List.sum_le_length_nsmul l B hc).trans (by rw [smul_eq_mul]; exact Nat.mul_le_mul_right B hl)

theorem mul_shape (F N L e b : ℕ) : N * (F * N ^ e * (L + 1) ^ b) = F * N ^ (e + 1) * (L + 1) ^ b := by
  ring

/-- At most `N` components, each within `F N^e (L+1)^b`, cost at most
`F N^(e+1) (L+1)^b` together. -/
theorem components_sum {ι : Type*} (s : Finset ι) (c : ι → ℕ) {F N L e b : ℕ}
    (hs : s.card ≤ N) (hc : ∀ i ∈ s, c i ≤ F * N ^ e * (L + 1) ^ b) :
    ∑ i ∈ s, c i ≤ F * N ^ (e + 1) * (L + 1) ^ b :=
  (finset_sum_le s c hs hc).trans_eq (mul_shape F N L e b)

theorem components_list_sum (l : List ℕ) {F N L e b : ℕ} (hl : l.length ≤ N)
    (hc : ∀ x ∈ l, x ≤ F * N ^ e * (L + 1) ^ b) :
    l.sum ≤ F * N ^ (e + 1) * (L + 1) ^ b :=
  (list_sum_le l hl hc).trans_eq (mul_shape F N L e b)

/-- Per-component search costs summed over at most `N` components, with the
parameter `γ + k` and the general exponent. -/
theorem search_sum_exponentD {ι : Type*} (s : Finset ι) (cost : ι → ℕ)
    {K a N L γ k : ℕ} (m r d G : ι → ℕ) (hN : 1 ≤ N) (hs : s.card ≤ N)
    (hm : ∀ i ∈ s, m i ≤ N) (hr : ∀ i ∈ s, r i ≤ 4 * N)
    (hd : ∀ i ∈ s, d i ≤ Spec.exponentD γ k)
    (hG : ∀ i ∈ s, G i ≤ a * (d i + 1) * (N + L + 1))
    (hc : ∀ i ∈ s, cost i ≤ K * (4 * m i + 1) ^ d i * (r i + m i + d i + G i + 2) ^ 6) :
    ∑ i ∈ s, cost i ≤
      stageFactor K a (γ + k) * N ^ (Spec.exponentD γ k + 6 + 1) * (L + 1) ^ 6 :=
  components_sum s cost hs fun i hi =>
    (hc i hi).trans (stage_bound_exponentD hN (hm i hi) (hr i hi) (hd i hi) (hG i hi))

/-- Orientable counterpart of `search_sum_exponentD`. -/
theorem search_sum_orientableExponentD {ι : Type*} (s : Finset ι) (cost : ι → ℕ)
    {K a N L γ k : ℕ} (m r d G : ι → ℕ) (hN : 1 ≤ N) (hs : s.card ≤ N)
    (hm : ∀ i ∈ s, m i ≤ N) (hr : ∀ i ∈ s, r i ≤ 4 * N)
    (hd : ∀ i ∈ s, d i ≤ Spec.orientableExponentD γ k)
    (hG : ∀ i ∈ s, G i ≤ a * (d i + 1) * (N + L + 1))
    (hc : ∀ i ∈ s, cost i ≤ K * (4 * m i + 1) ^ d i * (r i + m i + d i + G i + 2) ^ 6) :
    ∑ i ∈ s, cost i ≤
      stageFactor K a (γ + k) * N ^ (Spec.orientableExponentD γ k + 6 + 1) * (L + 1) ^ 6 :=
  components_sum s cost hs fun i hi =>
    (hc i hi).trans (stage_bound_orientableExponentD hN (hm i hi) (hr i hi) (hd i hi) (hG i hi))

end WeightedMIS.FinalBudget
