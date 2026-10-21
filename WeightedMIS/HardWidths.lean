module

public import WeightedMIS.ExpandedParameterValues
public import WeightedMIS.IncrementalComplement
public import WeightedMIS.DecomposeWords
public import WeightedMIS.NetworkWeights

/-!
# Working widths of the hard-component solver

The hard-component solver builds its words at widths computed from its
inputs only: the numbers `n` and `m` of vertices and edges, the cost width
`c`, and the number `d` of global kernel rows. Every width is the type of a
zero word that the machine builds by doubling a one-bit word thirteen times
(`baseWidth = 2 ^ 13`), padding over lists of known lengths
(`padW w L = (w + 1) * L`) and widening.

* `ratWidth n m` is the rational width of the kernel stage; it dominates the
  elimination, decomposition and selection widths and the face widths.
* `searchWidth c n m d` is the common width of the search and the recovery;
  `(3 n + 1) * fitBound r d cost < 2 ^ searchWidth c n m d` whenever
  `r ≤ 4 m` and every cost is below `2 ^ c`.
-/

@[expose] public section

namespace WeightedMIS.HardWidths

open WeightedMIS.SparseSearchGraph WeightedMIS.NodeEncoding
open scoped BigOperators

/-- The width of the doubled one-bit zero word. -/
def baseWidth : ℕ := 2 ^ 13

/-- The width of a padding word: `(w + 1) * L`. -/
def padW (w L : ℕ) : ℕ := (w + 1) * L

/-- The rational working width of the kernel stage. -/
def ratCore (n m : ℕ) : ℕ :=
  padW (padW (padW (padW (padW (padW baseWidth (n + 1)) (n + 1)) (n + 1)) (m + 1)) (m + 1))
    (m + 1)

def ratWidth (n m : ℕ) : ℕ := 2 + ratCore n m

/-- The shape width of the search stage, from the cost width `c`. -/
def shapeWidth (c n m : ℕ) : ℕ := baseWidth + c + padW baseWidth m + padW baseWidth n

/-- The working width of the search and the recovery. -/
def searchCore (c n m d : ℕ) : ℕ := padW (shapeWidth c n m) (d + 1)

def searchWidth (c n m d : ℕ) : ℕ := 2 + searchCore c n m d

/-! ## Elementary bounds -/

theorem padW_ge (w L : ℕ) : w * L ≤ padW w L := by
  unfold padW; exact Nat.mul_le_mul_right _ (Nat.le_succ w)

theorem padW_le (w L : ℕ) : padW w L ≤ (w + 1) * L := le_rfl

theorem le_two_pow (x : ℕ) : x ≤ 2 ^ x := (Nat.lt_two_pow_self).le

theorem ratCore_ge (n m : ℕ) : baseWidth * (n + 1) ^ 3 * (m + 1) ^ 3 ≤ ratCore n m := by
  unfold ratCore
  have h1 := padW_ge baseWidth (n + 1)
  have h2 := padW_ge (padW baseWidth (n + 1)) (n + 1)
  have h3 := padW_ge (padW (padW baseWidth (n + 1)) (n + 1)) (n + 1)
  have h4 := padW_ge (padW (padW (padW baseWidth (n + 1)) (n + 1)) (n + 1)) (m + 1)
  have h5 := padW_ge (padW (padW (padW (padW baseWidth (n + 1)) (n + 1)) (n + 1)) (m + 1)) (m + 1)
  have h6 := padW_ge (padW (padW (padW (padW (padW baseWidth (n + 1)) (n + 1)) (n + 1)) (m + 1))
    (m + 1)) (m + 1)
  calc baseWidth * (n + 1) ^ 3 * (m + 1) ^ 3
      = ((((baseWidth * (n + 1)) * (n + 1)) * (n + 1)) * (m + 1) * (m + 1)) * (m + 1) := by ring
    _ ≤ _ := by
      refine le_trans ?_ h6
      refine Nat.mul_le_mul_right _ (le_trans ?_ h5)
      refine Nat.mul_le_mul_right _ (le_trans ?_ h4)
      refine Nat.mul_le_mul_right _ (le_trans ?_ h3)
      refine Nat.mul_le_mul_right _ (le_trans ?_ h2)
      exact Nat.mul_le_mul_right _ h1

theorem cube_le (n m : ℕ) : 64 * (n + 5 * m + 3) ^ 3 ≤ baseWidth * (n + 1) ^ 3 * (m + 1) ^ 3 := by
  have h : n + 5 * m + 3 ≤ 5 * ((n + 1) * (m + 1)) := by nlinarith
  have h3 : (n + 5 * m + 3) ^ 3 ≤ (5 * ((n + 1) * (m + 1))) ^ 3 := Nat.pow_le_pow_left h 3
  have e : (5 * ((n + 1) * (m + 1))) ^ 3 = 125 * ((n + 1) ^ 3 * (m + 1) ^ 3) := by ring
  have e2 : baseWidth * (n + 1) ^ 3 * (m + 1) ^ 3 = 8192 * ((n + 1) ^ 3 * (m + 1) ^ 3) := by
    simp only [baseWidth]; ring
  rw [e] at h3; rw [e2]; omega

theorem kernelWidth_le (n m : ℕ) : RationalWordRows.kernelWidth n m ≤ ratWidth n m := by
  have h1 := RationalWordRows.kernelWidth_le n m
  have h2 : 64 * (n + m + 3) ^ 3 ≤ 64 * (n + 5 * m + 3) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have := cube_le n m; have := ratCore_ge n m
  unfold ratWidth; omega

theorem decomposeWidth_le (n m : ℕ) : SupportCycleWords.decomposeWidth n m ≤ ratWidth n m := by
  have h1 := SupportCycleWords.decomposeWidth_le n m
  have h2 : 64 * (n + m + 3) ^ 3 ≤ 64 * (n + 5 * m + 3) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have := cube_le n m; have := ratCore_ge n m
  unfold ratWidth; omega

theorem selectWidth_le (n m : ℕ) :
    IncrementalComplement.selectWidth (4 * m) m ≤ ratWidth n m := by
  have h1 := IncrementalComplement.selectWidth_le (4 * m) m
  have h2 : 64 * (4 * m + m + 3) ^ 3 ≤ 64 * (n + 5 * m + 3) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have := cube_le n m; have := ratCore_ge n m
  unfold ratWidth; omega

theorem edges_lt_ratWidth (n m : ℕ) : 8 * m + 1 < 2 ^ ratWidth n m := by
  have h := ratCore_ge n m
  have h1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2 : m + 1 ≤ (m + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h3 : baseWidth * (m + 1) ≤ baseWidth * (n + 1) ^ 3 * (m + 1) ^ 3 := by
    calc baseWidth * (m + 1) = baseWidth * 1 * (m + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
  have h5 : 8 * m + 1 < baseWidth * (m + 1) := by norm_num [baseWidth]; omega
  have h4 : 8 * m + 1 < ratWidth n m := by
    unfold ratWidth; omega
  exact h4.trans Nat.lt_two_pow_self

theorem four_edges_lt_ratWidth (n m : ℕ) : 4 * m < 2 ^ ratWidth n m := by
  have := edges_lt_ratWidth n m; omega

/-! ## The search width -/

theorem searchCore_ge (c n m d : ℕ) :
    c + 27 * m + 3 * n + 10 + (4 * m + 1) * d ≤ searchCore c n m d := by
  simp only [searchCore, padW, shapeWidth, baseWidth]
  have e : (2 ^ 13 + c + (2 ^ 13 + 1) * m + (2 ^ 13 + 1) * n + 1) * (d + 1) =
      (2 ^ 13 + c + (2 ^ 13 + 1) * m + (2 ^ 13 + 1) * n + 1) +
        (2 ^ 13 + c + (2 ^ 13 + 1) * m + (2 ^ 13 + 1) * n + 1) * d := by ring
  rw [e]
  have : (4 * m + 1) * d ≤ (2 ^ 13 + c + (2 ^ 13 + 1) * m + (2 ^ 13 + 1) * n + 1) * d :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem c_le_searchWidth (c n m d : ℕ) : c ≤ searchWidth c n m d := by
  have := searchCore_ge c n m d; unfold searchWidth; omega

theorem two_le_searchWidth (c n m d : ℕ) : 2 ≤ searchWidth c n m d := by
  unfold searchWidth; omega

theorem edges_lt_searchWidth (c n m d : ℕ) : 8 * m + 1 < 2 ^ searchWidth c n m d := by
  have := searchCore_ge c n m d
  have h : 8 * m + 1 < searchWidth c n m d := by unfold searchWidth; omega
  exact h.trans Nat.lt_two_pow_self

theorem vertices_lt_searchWidth (c n m d : ℕ) : 2 * n < 2 ^ searchWidth c n m d := by
  have := searchCore_ge c n m d
  have h : 2 * n < searchWidth c n m d := by unfold searchWidth; omega
  exact h.trans Nat.lt_two_pow_self

theorem pow_mul_le (x d : ℕ) : x ^ d ≤ 2 ^ (x * d) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left (le_two_pow x) d

theorem weightBound_succ_le {m c : ℕ} (cost : Fin m → ℕ) (hc : ∀ e, cost e < 2 ^ c) :
    weightBound cost + 1 ≤ 2 ^ (m + 1 + c) := by
  unfold weightBound
  have h1 : ∑ e, cost e ≤ ∑ _e : Fin m, 2 ^ c :=
    Finset.sum_le_sum (fun e _ => (hc e).le)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h2 : m + 1 ≤ 2 ^ (m + 1) := le_two_pow _
  have h3 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  rw [pow_add]
  nlinarith

/-- The product bound used by the search and the recovery. -/
theorem fit_lt {r m d n c : ℕ} (hr : r ≤ 4 * m) (cost : Fin m → ℕ)
    (hc : ∀ e, cost e < 2 ^ c) :
    (3 * n + 1) * ExpandedParameters.fitBound r d cost < 2 ^ searchWidth c n m d := by
  unfold ExpandedParameters.fitBound entryBound nodeCount
  have a1 : (4 * m + 1) ^ d ≤ 2 ^ ((4 * m + 1) * d) := pow_mul_le _ _
  have a2 : 1 + (2 * r + 1) ^ 2 ≤ 2 ^ (16 * m + 4) := by
    have : 1 + (2 * r + 1) ^ 2 ≤ (8 * m + 2) ^ 2 := by nlinarith
    refine this.trans ?_
    have h := Nat.pow_le_pow_left (le_two_pow (8 * m + 2)) 2
    rw [← pow_mul] at h
    exact h.trans (le_of_eq (by ring_nf))
  have a3 : 2 * r + 2 * m + 2 ≤ 2 ^ (10 * m + 2) := le_trans (by omega) (le_two_pow _)
  have a5 := weightBound_succ_le cost hc
  have a6 : 3 * n + 1 < 2 ^ (3 * n + 1) := Nat.lt_two_pow_self
  set P := 2 * (4 * m + 1) ^ d * (1 + (2 * r + 1) ^ 2) * (2 * r + 2 * m + 2) with hP
  have hP2 : 2 ≤ P := by
    have : 1 ≤ (4 * m + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    have : 1 ≤ 1 + (2 * r + 1) ^ 2 := by omega
    have : 2 * 1 * 1 * 2 ≤ P := by
      rw [hP]; gcongr; omega
    omega
  have hPle : P ≤ 2 * 2 ^ ((4 * m + 1) * d) * 2 ^ (16 * m + 4) * 2 ^ (10 * m + 2) := by
    rw [hP]; gcongr
  have hP3 : P + 2 ≤ 2 ^ (2 + (4 * m + 1) * d + (16 * m + 4) + (10 * m + 2)) := by
    have e : 2 ^ (2 + (4 * m + 1) * d + (16 * m + 4) + (10 * m + 2)) =
        2 * (2 * 2 ^ ((4 * m + 1) * d) * 2 ^ (16 * m + 4) * 2 ^ (10 * m + 2)) := by
      simp only [pow_add]; ring
    omega
  have hG := searchCore_ge c n m d
  have hlt : (3 * n + 1) * ((P + 2) * (weightBound cost + 1)) <
      2 ^ (3 * n + 1) * (2 ^ (2 + (4 * m + 1) * d + (16 * m + 4) + (10 * m + 2)) *
        2 ^ (m + 1 + c)) := by
    have hpos : 0 < (P + 2) * (weightBound cost + 1) := by positivity
    calc (3 * n + 1) * ((P + 2) * (weightBound cost + 1))
        < 2 ^ (3 * n + 1) * ((P + 2) * (weightBound cost + 1)) :=
          Nat.mul_lt_mul_of_pos_right a6 hpos
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul hP3 a5)
  refine lt_of_lt_of_le hlt ?_
  rw [← pow_add, ← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  unfold searchWidth
  omega

/-! ## Upper bounds -/

theorem ratWidth_le (n m : ℕ) : ratWidth n m ≤ 2 ^ 20 * (n + m + 1) ^ 6 := by
  unfold ratWidth ratCore padW baseWidth
  set X := n + m + 1 with hX
  have hn : n + 1 ≤ X := by omega
  have hm : m + 1 ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  have step : ∀ w L : ℕ, L ≤ X → (w + 1) * L ≤ (w + 1) * X := fun w L hL =>
    Nat.mul_le_mul_left _ hL
  have b1 := step (2 ^ 13) (n + 1) hn
  have b2 := step ((2 ^ 13 + 1) * (n + 1)) (n + 1) hn
  calc 2 + ((((((2 ^ 13 + 1) * (n + 1) + 1) * (n + 1) + 1) * (n + 1) + 1) * (m + 1) + 1) *
        (m + 1) + 1) * (m + 1)
      ≤ 2 + ((((((2 ^ 13 + 1) * X + 1) * X + 1) * X + 1) * X + 1) * X + 1) * X := by gcongr
    _ ≤ 2 ^ 20 * X ^ 6 := by
      have h2 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) _
      have h3 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX1 (by norm_num)
      have h4 : X ^ 3 ≤ X ^ 4 := Nat.pow_le_pow_right hX1 (by norm_num)
      have h5 : X ^ 4 ≤ X ^ 5 := Nat.pow_le_pow_right hX1 (by norm_num)
      have h6 : X ^ 5 ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by norm_num)
      ring_nf
      nlinarith

theorem searchWidth_le (c n m d : ℕ) :
    searchWidth c n m d ≤ 2 ^ 15 * (d + 1) * (c + n + m + 1) := by
  unfold searchWidth searchCore shapeWidth padW baseWidth
  have : (2 ^ 13 + c + (2 ^ 13 + 1) * m + (2 ^ 13 + 1) * n + 1) ≤ 2 ^ 14 * (c + n + m + 1) := by
    omega
  have h := Nat.mul_le_mul_right (d + 1) this
  have : 2 ≤ 2 ^ 14 * (d + 1) * (c + n + m + 1) := by
    have : 1 ≤ (d + 1) * (c + n + m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  nlinarith

end WeightedMIS.HardWidths
