module

public import WeightedMIS.SparseKernel
public import WeightedMIS.EncodingCost

/-!
# Arithmetic growth in bounded kernel elimination

An elimination pivot is a nonzero integer of absolute value at most two.
Doubling a common denominator therefore preserves integral numerators. The
new numerator magnitude is at most six times the previous maximum, giving
an explicit growth recurrence independent of coordinate magnitudes.
-/

@[expose] public section

namespace WeightedMIS.KernelArithmetic

variable {E : Type*}

/-- Every permitted nonzero pivot divides two with a bounded quotient. -/
theorem pivot_divides_two (a : ℤ) (ha : |a| ≤ 2) (hne : a ≠ 0) :
    ∃ k : ℤ, k * a = 2 ∧ |k| ≤ 2 := by
  have hab := abs_le.mp ha
  have hcases : a = -2 ∨ a = -1 ∨ a = 1 ∨ a = 2 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact ⟨-1, by norm_num, by norm_num⟩
  · exact ⟨-2, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num⟩
  · exact ⟨1, by norm_num, by norm_num⟩

/-- One pivot elimination doubles a common denominator and multiplies a
uniform bound on integer numerators by at most six. -/
theorem elimination_scale_bound (x : E → ℚ) (g z : E → ℤ) (d : ℕ) (M : ℤ)
    (e : E) (hg : ∀ f, |g f| ≤ 2) (he : g e ≠ 0)
    (hz : ∀ f, (d : ℚ) * x f = (z f : ℚ)) (hM : ∀ f, |z f| ≤ M) :
    ∃ z' : E → ℤ,
      (∀ f, ((2 * d : ℕ) : ℚ) *
        (x f - (x e / (g e : ℚ)) * (g f : ℚ)) = (z' f : ℚ)) ∧
      ∀ f, |z' f| ≤ 6 * M := by
  obtain ⟨k, hk, hkb⟩ := pivot_divides_two (g e) (hg e) he
  have hge : (g e : ℚ) ≠ 0 := by exact_mod_cast he
  have hkq : (2 : ℚ) / (g e : ℚ) = (k : ℚ) := by
    apply (div_eq_iff hge).mpr
    exact_mod_cast hk.symm
  let z' : E → ℤ := fun f => 2 * z f - k * z e * g f
  refine ⟨z', ?_, ?_⟩
  · intro f
    calc
      ((2 * d : ℕ) : ℚ) * (x f - (x e / (g e : ℚ)) * (g f : ℚ)) =
          2 * ((d : ℚ) * x f) - ((2 : ℚ) / (g e : ℚ)) *
            ((d : ℚ) * x e) * (g f : ℚ) := by push_cast; ring
      _ = (z' f : ℚ) := by rw [hkq, hz f, hz e]; simp [z']
  · intro f
    have htri : |2 * z f - k * z e * g f| ≤ |2 * z f| + |k * z e * g f| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (2 * z f) (-(k * z e * g f))
    have hzpos := abs_nonneg (z e)
    have hgpos := abs_nonneg (g f)
    have hzfb := hM f
    have hzeb := hM e
    have hgb := hg f
    have hp : |k| * |z e| * |g f| ≤ 4 * M := by
      calc
        |k| * |z e| * |g f| ≤ 2 * |z e| * |g f| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkb hzpos) hgpos
        _ ≤ 2 * M * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hzeb (by norm_num)) hgb hgpos
            (by nlinarith)
        _ = 4 * M := by ring
    norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)] at htri
    change |2 * z f - k * z e * g f| ≤ 6 * M
    linarith

/-- A bounded integer row together with its elimination coordinate. -/
abbrev Pivot (E : Type*) := (E → ℤ) × E

/-- Exact rational coordinate elimination by a specified pivot. -/
def eliminate (x : E → ℚ) (p : Pivot E) : E → ℚ :=
  fun f => x f - (x p.2 / (p.1 p.2 : ℚ)) * (p.1 f : ℚ)

/-- Apply a finite sequence of coordinate eliminations. -/
def eliminateList (x : E → ℚ) : List (Pivot E) → E → ℚ
  | [] => x
  | p :: ps => eliminateList (eliminate x p) ps

/-- A pivot is nonzero and its row has the required coordinate bound. -/
def ValidPivot (p : Pivot E) : Prop :=
  (∀ f, |p.1 f| ≤ 2) ∧ p.1 p.2 ≠ 0

/-- After `k` eliminations, a common denominator grows by `2^k` and a
uniform numerator bound grows by at most `6^k`. -/
theorem elimination_chain_scale_bound (x : E → ℚ) (ps : List (Pivot E))
    (d : ℕ) (z : E → ℤ) (M : ℤ)
    (hp : ∀ p ∈ ps, ValidPivot p)
    (hz : ∀ f, (d : ℚ) * x f = (z f : ℚ)) (hM : ∀ f, |z f| ≤ M) :
    ∃ z' : E → ℤ,
      (∀ f, ((2 ^ ps.length * d : ℕ) : ℚ) * eliminateList x ps f = (z' f : ℚ)) ∧
      ∀ f, |z' f| ≤ (6 : ℤ) ^ ps.length * M := by
  induction ps generalizing x d z M with
  | nil => exact ⟨z, by simpa [eliminateList] using hz, by simpa using hM⟩
  | cons p ps ih =>
      have hcur := hp p List.mem_cons_self
      obtain ⟨z₁, hz₁, hM₁⟩ := elimination_scale_bound x p.1 z d M p.2 hcur.1 hcur.2 hz hM
      have htail : ∀ q ∈ ps, ValidPivot q := fun q hq => hp q (List.mem_cons_of_mem p hq)
      obtain ⟨z₂, hz₂, hM₂⟩ := ih (eliminate x p) (2 * d) z₁ (6 * M) htail hz₁ hM₁
      refine ⟨z₂, ?_, ?_⟩
      · intro f
        simpa only [eliminateList, List.length_cons, pow_succ, mul_assoc,
          mul_left_comm, mul_comm] using hz₂ f
      · intro f
        simpa only [List.length_cons, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hM₂ f

/-- The common denominator and integer numerators have bit lengths linear
in the number of elimination steps, in addition to their input widths. -/
theorem elimination_chain_bit_bound (x : E → ℚ) (ps : List (Pivot E))
    (d M : ℕ) (z : E → ℤ) (hp : ∀ p ∈ ps, ValidPivot p)
    (hz : ∀ f, (d : ℚ) * x f = (z f : ℚ)) (hM : ∀ f, |z f| ≤ (M : ℤ)) :
    ∃ z' : E → ℤ,
      (∀ f, ((2 ^ ps.length * d : ℕ) : ℚ) * eliminateList x ps f = (z' f : ℚ)) ∧
      (2 ^ ps.length * d).size ≤ 2 * ps.length + 1 + d.size ∧
      ∀ f, (z' f).natAbs.size ≤ 3 * ps.length + 1 + M.size := by
  obtain ⟨z', hz', hbound⟩ := elimination_chain_scale_bound x ps d z (M : ℤ) hp hz hM
  refine ⟨z', hz', ?_, ?_⟩
  · have hm := EncodingCost.size_mul_le (2 ^ ps.length) d
    have hp := EncodingCost.size_pow_le 2 ps.length
    have htwo : (2 : ℕ).size = 2 := by decide
    rw [htwo] at hp
    omega
  · intro f
    have hnat : (z' f).natAbs ≤ 6 ^ ps.length * M := by
      have h := hbound f
      rw [← Int.natCast_natAbs] at h
      exact_mod_cast h
    have hsize := Nat.size_le_size hnat
    have hm := EncodingCost.size_mul_le (6 ^ ps.length) M
    have hp := EncodingCost.size_pow_le 6 ps.length
    have hsix : (6 : ℕ).size = 3 := by decide
    rw [hsix] at hp
    omega

section Incidence

open Matrix SparseKernel

variable {V : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]

/-- Actual support-based kernel elimination reaches zero in at most the
original support size many bounded pivots. -/
theorem exists_kernel_elimination (left right : E → V) (x : E → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) :
    ∃ ps : List (Pivot E), ps.length ≤ (support x).card ∧
      (∀ p ∈ ps, ValidPivot p ∧ KernelBasis.IntegralKernel left right p.1) ∧
      eliminateList x ps = 0 := by
  classical
  by_cases hzero : x = 0
  · subst x
    exact ⟨[], by simp, by simp, rfl⟩
  · obtain ⟨g, hg, hb, hgne, hsup⟩ := support_generator left right x hx hzero
    obtain ⟨e, he⟩ : ∃ e, g e ≠ 0 := by
      by_contra! h
      exact hgne (funext h)
    have hge : (g e : ℚ) ≠ 0 := by exact_mod_cast he
    let r := eliminate x (g, e)
    have hrdef : r = x - (x e / (g e : ℚ)) • (fun f => (g f : ℚ)) := by
      ext f
      rfl
    have hr : r ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
      rw [hrdef]
      exact (LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin).sub_mem hx
        ((LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin).smul_mem _
          ((KernelBasis.integralKernel_iff left right g).mp hg))
    have hre : r e = 0 := by simp [r, eliminate, div_mul_cancel₀ _ hge]
    have hxe : x e ≠ 0 := fun h => he (hsup e h)
    have hsubset : support r ⊆ support x := by
      intro f hf
      simp only [mem_support] at hf ⊢
      intro hxf
      have hgf := hsup f hxf
      exact hf (by simp [r, eliminate, hxf, hgf])
    have hlt : (support r).card < (support x).card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
      intro heq
      have hmem : e ∈ support r := heq.symm ▸ (mem_support x e).mpr hxe
      exact (mem_support r e).mp hmem hre
    obtain ⟨ps, hlen, hp, hend⟩ := exists_kernel_elimination left right r hr
    refine ⟨(g, e) :: ps, by simp only [List.length_cons]; omega, ?_, hend⟩
    intro p hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact ⟨⟨hb, he⟩, hg⟩
    · exact hp p hp'
termination_by (support x).card

/-- A kernel-elimination sequence of at most the support size many steps
has uniformly bounded stored numerator and denominator widths at every prefix. -/
theorem kernel_elimination_bit_bound (left right : E → V) (x : E → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (d M : ℕ) (z : E → ℤ)
    (hz : ∀ f, (d : ℚ) * x f = (z f : ℚ)) (hM : ∀ f, |z f| ≤ (M : ℤ)) :
    ∃ ps : List (Pivot E), ps.length ≤ (support x).card ∧
      (∀ p ∈ ps, ValidPivot p ∧ KernelBasis.IntegralKernel left right p.1) ∧
      eliminateList x ps = 0 ∧
      ∀ pre : List (Pivot E), pre.IsPrefix ps → ∃ z' : E → ℤ,
        (∀ f, ((2 ^ pre.length * d : ℕ) : ℚ) * eliminateList x pre f = (z' f : ℚ)) ∧
        (2 ^ pre.length * d).size ≤ 2 * (support x).card + 1 + d.size ∧
        ∀ f, (z' f).natAbs.size ≤ 3 * (support x).card + 1 + M.size := by
  obtain ⟨ps, hlen, hp, hend⟩ := exists_kernel_elimination left right x hx
  refine ⟨ps, hlen, hp, hend, ?_⟩
  intro pre hpre
  have hvalid : ∀ p ∈ pre, ValidPivot p := fun p hm => (hp p (hpre.subset hm)).1
  obtain ⟨z', hz', hd', hM'⟩ := elimination_chain_bit_bound x pre d M z hvalid hz hM
  have hplen := hpre.length_le
  refine ⟨z', hz', by omega, ?_⟩
  intro f
  have h := hM' f
  omega

end Incidence

end WeightedMIS.KernelArithmetic
