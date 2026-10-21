module

public import WeightedMIS.DeterministicKernel
public import WeightedMIS.RationalWidth

/-!
# Arithmetic bounds for deterministic support elimination

The pivot trace follows the executable support decomposition exactly. Every
pivot is an integral kernel row bounded by two, so the existing common-scale
recurrence bounds all actual residual states and coefficients.
-/

@[expose] public section

namespace WeightedMIS.DeterministicKernelWidth

open Matrix DeterministicKernel KernelArithmetic RationalWidth SparseKernel

variable {n m : ℕ}

/-- The pivot trace of the deterministic support decomposition. -/
def pivots (left right : Fin m → Fin n) : ℕ → (Fin m → ℚ) → List (Pivot (Fin m))
  | 0, _ => []
  | fuel + 1, x =>
      let g := materializeInt (generator left right x)
      match pivot g with
      | none => []
      | some e => (g, e) :: pivots left right fuel (materializeRat (eliminate x (g, e)))

/-- Rational coefficients recovered from a pivot trace. -/
def terms (x : Fin m → ℚ) : List (Pivot (Fin m)) → List (Term (Fin m))
  | [] => []
  | p :: ps => (x p.2 / (p.1 p.2 : ℚ), p.1) :: terms (eliminate x p) ps

theorem decompose_eq_terms (left right : Fin m → Fin n) (fuel : ℕ) (x : Fin m → ℚ) :
    decompose left right fuel x = terms x (pivots left right fuel x) := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
      simp only [decompose, pivots]
      split
      · next he => simp only [he, terms]
      · next e he => simp only [he, terms, materializeRat_eq, ih]

theorem pivots_length_le (left right : Fin m → Fin n) (fuel : ℕ) (x : Fin m → ℚ) :
    (pivots left right fuel x).length ≤ fuel := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
      simp only [pivots]
      split
      · simp
      · simpa only [List.length_cons, Nat.succ_le_succ_iff] using ih _

theorem pivots_valid (left right : Fin m → Fin n) (fuel : ℕ) (x : Fin m → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) :
    ∀ p ∈ pivots left right fuel x,
      ValidPivot p ∧ KernelBasis.IntegralKernel left right p.1 := by
  induction fuel generalizing x with
  | zero => simp [pivots]
  | succ fuel ih =>
      by_cases hzero : x = 0
      · subst x
        simp [pivots]
      · have hgen := generator_spec left right x hx hzero
        let g := materializeInt (generator left right x)
        have hg : KernelBasis.IntegralKernel left right g ∧ ∀ e, |g e| ≤ 2 := by
          simpa only [g, materializeInt_eq] using And.intro hgen.1 hgen.2.1
        change ∀ p ∈ (match pivot g with
          | none => []
          | some e => (g, e) :: pivots left right fuel (materializeRat (eliminate x (g, e)))), _
        split
        · simp
        · next e he =>
            have hvalid : ValidPivot (g, e) := ⟨hg.2, pivot_ne_zero g e he⟩
            have hr : materializeRat (eliminate x (g, e)) ∈
                LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
              rw [materializeRat_eq]
              change x - (x e / (g e : ℚ)) • (fun f => (g f : ℚ)) ∈ _
              exact (LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin).sub_mem hx
                ((LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin).smul_mem _
                  ((KernelBasis.integralKernel_iff left right g).mp hg.1))
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨hvalid, hg.1⟩
            · exact ih _ hr p hp

/-- Every actual intermediate residual has bounded common-scale arithmetic. -/
theorem pivots_prefix_scale (left right : Fin m → Fin n) (fuel : ℕ) (x : Fin m → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (d M : ℕ) (z : Fin m → ℤ)
    (hz : ∀ f, (d : ℚ) * x f = (z f : ℚ)) (hM : ∀ f, |z f| ≤ (M : ℤ))
    (pre : List (Pivot (Fin m))) (hpre : pre.IsPrefix (pivots left right fuel x)) :
    ∃ z' : Fin m → ℤ,
      (∀ f, ((2 ^ pre.length * d : ℕ) : ℚ) * eliminateList x pre f = (z' f : ℚ)) ∧
      (2 ^ pre.length * d).size ≤ 2 * fuel + 1 + d.size ∧
      ∀ f, (z' f).natAbs.size ≤ 3 * fuel + 1 + M.size := by
  have hvalid : ∀ p ∈ pre, ValidPivot p :=
    fun p hp => (pivots_valid left right fuel x hx p (hpre.subset hp)).1
  obtain ⟨z', hz', hd', hM'⟩ := elimination_chain_bit_bound x pre d M z hvalid hz hM
  have hlen := hpre.length_le.trans (pivots_length_le left right fuel x)
  refine ⟨z', hz', by omega, ?_⟩
  intro f
  have h := hM' f
  omega

/-- Normalizing a common-scale integer representation only decreases widths. -/
theorem fits_of_scale (x : ℚ) (d : ℕ) (hd : d ≠ 0) (z : ℤ)
    (hz : (d : ℚ) * x = (z : ℚ)) (B : ℕ)
    (hnum : z.natAbs.size ≤ B) (hden : d.size ≤ B) : Fits x B := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have heq : x = (z : ℚ) / (d : ℤ) := by
    apply (eq_div_iff (by exact_mod_cast hd : ((d : ℤ) : ℚ) ≠ 0)).mpr
    simpa only [Int.cast_natCast, mul_comm] using hz
  rw [heq]
  exact ⟨(Nat.size_le_size (DeterminantSize.ratio_num_le z d (by exact_mod_cast hd))).trans hnum,
    (Nat.size_le_size (DeterminantSize.ratio_den_le z d (by exact_mod_cast hd))).trans
      (by simpa using hden)⟩

theorem pivots_prefix_fits (left right : Fin m → Fin n) (fuel : ℕ) (x : Fin m → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (d M : ℕ) (hd : d ≠ 0) (z : Fin m → ℤ)
    (hz : ∀ f, (d : ℚ) * x f = (z f : ℚ)) (hM : ∀ f, |z f| ≤ (M : ℤ))
    (pre : List (Pivot (Fin m))) (hpre : pre.IsPrefix (pivots left right fuel x))
    (f : Fin m) :
    Fits (eliminateList x pre f) (3 * fuel + 1 + M.size + d.size) := by
  obtain ⟨z', hz', hd', hM'⟩ := pivots_prefix_scale left right fuel x hx d M z hz hM pre hpre
  have hden : 2 ^ pre.length * d ≠ 0 := by positivity
  apply fits_of_scale _ _ hden (z' f) (hz' f)
  · have h := hM' f
    omega
  · omega

/-- Clearing denominators of a finite rational vector increases width only
linearly in the number of coordinates. -/
theorem common_scale_of_fits (x : Fin m → ℚ) (W : ℕ) (hx : ∀ e, Fits (x e) W) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 2 ^ (m * W) ∧ ∃ z : Fin m → ℤ,
      (∀ e, (d : ℚ) * x e = (z e : ℚ)) ∧
      ∀ e, |z e| ≤ ((2 ^ ((m + 1) * W) : ℕ) : ℤ) := by
  let d := ∏ e, (x e).den
  have hd : 0 < d := Finset.prod_pos (fun e _ => (x e).den_pos)
  have hdiv (e : Fin m) : (x e).den ∣ d :=
    Finset.dvd_prod_of_mem (fun e => (x e).den) (Finset.mem_univ e)
  have hdb : d ≤ 2 ^ (m * W) := by
    calc
      d ≤ ∏ _e : Fin m, 2 ^ W := Finset.prod_le_prod
        (fun e _ => ((fits_iff _ _).mp (hx e)).2.le)
      _ = 2 ^ (m * W) := by simp [← pow_mul, Nat.mul_comm]
  let z : Fin m → ℤ := fun e => ((d / (x e).den : ℕ) : ℤ) * (x e).num
  refine ⟨d, hd, hdb, z, ?_, ?_⟩
  · intro e
    have hmul : (x e).den * (d / (x e).den) = d := Nat.mul_div_cancel' (hdiv e)
    have hm : ((x e).den : ℚ) * ((d / (x e).den : ℕ) : ℚ) = (d : ℚ) := by
      exact_mod_cast hmul
    calc
      (d : ℚ) * x e = ((d / (x e).den : ℕ) : ℚ) * (((x e).den : ℚ) * x e) := by
        rw [← hm]
        ring
      _ = ((d / (x e).den : ℕ) : ℚ) * (x e).num := by rw [Rat.den_mul_eq_num]
      _ = (z e : ℚ) := by simp only [z, Int.cast_mul, Int.cast_natCast]
  · intro e
    have hnum := ((fits_iff _ _).mp (hx e)).1.le
    have hz : (z e).natAbs ≤ 2 ^ ((m + 1) * W) := by
      calc
        (z e).natAbs = (d / (x e).den) * (x e).num.natAbs := by
          simp only [z, Int.natAbs_mul, Int.natAbs_natCast]
        _ ≤ d * (x e).num.natAbs := Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
        _ ≤ 2 ^ (m * W) * 2 ^ W := Nat.mul_le_mul hdb hnum
        _ = 2 ^ ((m + 1) * W) := by rw [← pow_add]; congr 1; ring
    rw [← Int.natCast_natAbs]
    exact_mod_cast hz

/-- All residuals of the actual support-decomposition routine have a common
polynomial normalized width, with no initial denominator certificate required. -/
theorem pivots_prefix_fits_of_input (left right : Fin m → Fin n) (fuel : ℕ)
    (x : Fin m → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (W : ℕ) (hW : ∀ e, Fits (x e) W)
    (pre : List (Pivot (Fin m))) (hpre : pre.IsPrefix (pivots left right fuel x))
    (f : Fin m) :
    Fits (eliminateList x pre f) (3 * fuel + (2 * m + 1) * W + 3) := by
  obtain ⟨d, hd, hdb, z, hz, hM⟩ := common_scale_of_fits x W hW
  have h := pivots_prefix_fits left right fuel x hx d (2 ^ ((m + 1) * W))
    hd.ne' z hz hM pre hpre f
  apply fits_mono h
  have hds : d.size ≤ m * W + 1 := by
    apply Nat.size_le.mpr
    have hp : 0 < 2 ^ (m * W) := by positivity
    rw [pow_succ]
    omega
  have hMs : (2 ^ ((m + 1) * W)).size ≤ (m + 1) * W + 1 := by
    apply Nat.size_le.mpr
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  nlinarith

/-- The initial rational vectors are computed from the actual integer
incidence matrix, whose entries are at most two. -/
theorem initial_fits (left right : Fin m → Fin n) (x : Fin m → ℚ)
    (hx : x ∈ initial left right) (e : Fin m) :
    Fits (x e) ((n + m + 2) * m + m ^ 2 + 1) := by
  let A : Matrix (Fin n) (Fin m) ℤ := fun v f => KernelBasis.entry left right f v
  have hA : ∀ i j, (A i j).natAbs ≤ 2 ^ 1 := by
    intro i j
    simp only [A, KernelBasis.entry]
    split_ifs <;> norm_num
  have hcast : EliminationCertificate.rationalMatrix A =
      (Incidence.unsigned left right)ᵀ := by
    ext i j
    simp [EliminationCertificate.rationalMatrix, A, KernelBasis.entry,
      Incidence.unsigned]
  apply EliminationCertificate.kernelGenerators_coordinate_size A 1 hA x ?_ e
  rw [hcast]
  simpa only [initial_eq, ComputedKernel.rationalGenerators] using hx

theorem initial_kernel (left right : Fin m → Fin n) (x : Fin m → ℚ)
    (hx : x ∈ initial left right) :
    x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  have hs := ComputedKernel.rationalGenerators_span left right
  rw [← hs]
  apply Submodule.subset_span
  simpa only [initial_eq, Set.mem_ofPred_eq] using hx

/-- Uniform polynomial width throughout every actual support-elimination
sequence used to produce the bounded candidate family. -/
theorem candidate_residual_fits (left right : Fin m → Fin n) (x : Fin m → ℚ)
    (hx : x ∈ initial left right) (pre : List (Pivot (Fin m)))
    (hpre : pre.IsPrefix (pivots left right m x)) (f : Fin m) :
    Fits (eliminateList x pre f)
      (3 * m + (2 * m + 1) * ((n + m + 2) * m + m ^ 2 + 1) + 3) :=
  pivots_prefix_fits_of_input left right m x (initial_kernel left right x hx)
    _ (initial_fits left right x hx) pre hpre f

theorem terms_mem (x : Fin m → ℚ) (ps : List (Pivot (Fin m))) (t : Term (Fin m))
    (ht : t ∈ terms x ps) :
    ∃ pre p post, ps = pre ++ p :: post ∧
      t = (eliminateList x pre p.2 / (p.1 p.2 : ℚ), p.1) := by
  induction ps generalizing x with
  | nil => simp [terms] at ht
  | cons p ps ih =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨[], p, ps, rfl, rfl⟩
      · obtain ⟨pre, q, post, heq, ht⟩ := ih (eliminate x p) ht
        exact ⟨p :: pre, q, post, by simp [heq], ht⟩

/-- Every returned decomposition coefficient also has polynomial width. -/
theorem decompose_coefficient_fits (left right : Fin m → Fin n) (fuel : ℕ)
    (x : Fin m → ℚ)
    (hx : x ∈ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (W : ℕ) (hW : ∀ e, Fits (x e) W) (t : Term (Fin m))
    (ht : t ∈ decompose left right fuel x) :
    Fits t.1 (3 * fuel + (2 * m + 1) * W + 5) := by
  rw [decompose_eq_terms] at ht
  obtain ⟨pre, p, post, heq, rfl⟩ := terms_mem x _ t ht
  have hpre : pre.IsPrefix (pivots left right fuel x) := ⟨p :: post, heq.symm⟩
  have hp : p ∈ pivots left right fuel x := by rw [heq]; simp
  have hvalid := (pivots_valid left right fuel x hx p hp).1
  have hnum := pivots_prefix_fits_of_input left right fuel x hx W hW pre hpre p.2
  have hpabs : (p.1 p.2).natAbs ≤ 2 ^ 1 := by
    have h := hvalid.1 p.2
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hden := fits_int (p.1 p.2) 1 hpabs
  convert fits_div hnum hden using 1

end WeightedMIS.DeterministicKernelWidth
