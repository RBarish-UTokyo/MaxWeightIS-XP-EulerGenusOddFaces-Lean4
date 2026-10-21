module

public import WeightedMIS.RationalElimination
public import WeightedMIS.DeterminantSize

/-!
# Canonical-coordinate certificates for rational elimination

Every surviving generator keeps one free coordinate equal to one and all
other free coordinates equal to zero. This invariant identifies the computed
vectors as unique solutions of an integer Gram system and supplies determinant
representations whose sizes depend only on the original equations.
-/

@[expose] public section

namespace WeightedMIS.EliminationCertificate

open Matrix RationalElimination

variable {m : ℕ}

/-- Inactive generators vanish; active coordinates form the identity matrix. -/
def Canonical (s : Finset (Fin m)) (g : Fin m → Fin m → ℚ) : Prop :=
  (∀ i, i ∉ s → g i = 0) ∧
  ∀ i j, j ∈ s → g i j = if i = j then 1 else 0

theorem canonical_coordinateVectors :
    Canonical Finset.univ (fun i : Fin m => Pi.single i (1 : ℚ)) := by
  constructor
  · simp
  · intro i j _
    simp [Pi.single_apply, eq_comm]

theorem canonical_project (s : Finset (Fin m)) (g : Fin m → Fin m → ℚ)
    (hg : Canonical s g) (c : (Fin m → ℚ) →ₗ[ℚ] ℚ) (k : Fin m)
    (hk : c (g k) ≠ 0) :
    Canonical (s.erase k) (fun i => project c (g k) (g i)) := by
  have hks : k ∈ s := by
    by_contra h
    exact hk (by rw [hg.1 k h, map_zero])
  constructor
  · intro i hi
    dsimp only
    by_cases hik : i = k
    · subst i
      rw [project_apply, div_self hk]
      simp
    · have his : i ∉ s := fun h => hi (Finset.mem_erase.mpr ⟨hik, h⟩)
      rw [hg.1 i his, map_zero]
  · intro i j hj
    dsimp only
    obtain ⟨hjk, hjs⟩ := Finset.mem_erase.mp hj
    rw [project_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hg.2 i j hjs, hg.2 k j hjs, ite_eq_right (Ne.symm hjk)]
    simp

theorem canonical_cut (s : Finset (Fin m)) (g : Fin m → Fin m → ℚ)
    (hg : Canonical s g) (c : (Fin m → ℚ) →ₗ[ℚ] ℚ) :
    ∃ t h, cut c (List.ofFn g) = List.ofFn h ∧ Canonical t h := by
  unfold cut
  split
  · exact ⟨s, g, rfl, hg⟩
  · next p hp =>
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp (List.mem_of_find?_eq_some hp)
      refine ⟨s.erase k, fun i => project c (g k) (g i), ?_, ?_⟩
      · simp [Function.comp_def]
      · apply canonical_project s g hg c k
        simpa using List.find?_some hp

theorem canonical_eliminateRows (cs : List ((Fin m → ℚ) →ₗ[ℚ] ℚ))
    (s : Finset (Fin m)) (g : Fin m → Fin m → ℚ) (hg : Canonical s g) :
    ∃ t h, eliminateRows cs (List.ofFn g) = List.ofFn h ∧ Canonical t h := by
  induction cs generalizing s g with
  | nil => exact ⟨s, g, rfl, hg⟩
  | cons c cs ih =>
      obtain ⟨t, h, heq, hh⟩ := canonical_cut s g hg c
      simpa only [eliminateRows, heq] using ih t h hh

/-- Values at surviving free coordinates reconstruct the entire current span. -/
theorem canonical_reconstruct (s : Finset (Fin m)) (g : Fin m → Fin m → ℚ)
    (hg : Canonical s g) (x : Fin m → ℚ) (hx : x ∈ listSpan (List.ofFn g)) :
    x = ∑ i ∈ s, x i • g i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      by_cases hjs : j ∈ s
      · have heq : (∑ i ∈ s, g j i • g i) =
            ∑ i ∈ s, (if j = i then (1 : ℚ) else 0) • g i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hg.2 j i hi]
        rw [heq]
        simp [ite_smul, Finset.sum_ite_eq, hjs]
      · rw [hg.1 j hjs]
        simp
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [show (∑ i ∈ s, (x + y) i • g i) =
        (∑ i ∈ s, x i • g i) + ∑ i ∈ s, y i • g i by
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]]
      rw [← ihx, ← ihy]
  | smul a x hx ih =>
      rw [show (∑ i ∈ s, (a • x) i • g i) = a • ∑ i ∈ s, x i • g i by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]]
      rw [← ih]

/-- Add equations recording all surviving free coordinates. -/
def augmented {n : ℕ} {R : Type*} [Zero R] [One R]
    (A : Matrix (Fin n) (Fin m) R) (s : Finset (Fin m)) :
    Matrix (Fin n ⊕ Fin m) (Fin m) R :=
  fun r => match r with
  | .inl i => A i
  | .inr i => if i ∈ s then Pi.single i 1 else 0

theorem augmented_mulVec_inl {n : ℕ} (A : Matrix (Fin n) (Fin m) ℚ)
    (s : Finset (Fin m)) (x : Fin m → ℚ) (i : Fin n) :
    (augmented A s *ᵥ x) (.inl i) = (A *ᵥ x) i := rfl

theorem augmented_mulVec_inr {n : ℕ} (A : Matrix (Fin n) (Fin m) ℚ)
    (s : Finset (Fin m)) (x : Fin m → ℚ) (i : Fin m) :
    (augmented A s *ᵥ x) (.inr i) = if i ∈ s then x i else 0 := by
  by_cases hi : i ∈ s <;> simp [mulVec, dotProduct, augmented, hi, Pi.single_apply]

theorem augmented_injective {n : ℕ} (A : Matrix (Fin n) (Fin m) ℚ)
    (s : Finset (Fin m)) (g : Fin m → Fin m → ℚ) (hg : Canonical s g)
    (hspan : listSpan (List.ofFn g) = LinearMap.ker A.mulVecLin) :
    Function.Injective (augmented A s).mulVec := by
  have hz : ∀ x, augmented A s *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hAx : A *ᵥ x = 0 := by
      ext i
      exact congrFun hx (.inl i)
    have hxs : ∀ i ∈ s, x i = 0 := by
      intro i hi
      have heq := congrFun hx (.inr i)
      simpa only [augmented_mulVec_inr, hi, ite_true, Pi.zero_apply] using heq
    have hxspan : x ∈ listSpan (List.ofFn g) := by
      rw [hspan]
      exact hAx
    rw [canonical_reconstruct s g hg x hxspan]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hxs i hi, zero_smul]
  intro x y hxy
  apply sub_eq_zero.mp
  apply hz
  rw [mulVec_sub, hxy, sub_self]

/-- The Gram certificate is nonsingular without selecting an invertible minor. -/
theorem gram_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin m) ℚ)
    (s : Finset (Fin m)) (g : Fin m → Fin m → ℚ) (hg : Canonical s g)
    (hspan : listSpan (List.ofFn g) = LinearMap.ker A.mulVecLin) :
    IsUnit ((augmented A s)ᵀ * augmented A s) := by
  have hp := Matrix.PosDef.conjTranspose_mul_self (augmented A s)
    (augmented_injective A s g hg hspan)
  simpa only [conjTranspose_eq_transpose_of_trivial] using hp.isUnit

theorem gram_mul_generator {n : ℕ} (A : Matrix (Fin n) (Fin m) ℚ)
    (s : Finset (Fin m)) (g : Fin m → Fin m → ℚ) (hg : Canonical s g)
    (hspan : listSpan (List.ofFn g) = LinearMap.ker A.mulVecLin)
    (i : Fin m) (hi : i ∈ s) :
    ((augmented A s)ᵀ * augmented A s) *ᵥ g i = Pi.single i 1 := by
  have hgi : A *ᵥ g i = 0 := by
    have hm : g i ∈ listSpan (List.ofFn g) :=
      Submodule.subset_span (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rw [hspan] at hm
    exact hm
  rw [← mulVec_mulVec]
  ext j
  simp only [mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type]
  have hleft : (∑ x : Fin n, augmented A s (.inl x) j *
      ∑ k, augmented A s (.inl x) k * g i k) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    change A x j * (A *ᵥ g i) x = 0
    rw [hgi, Pi.zero_apply, mul_zero]
  rw [hleft, zero_add]
  have hright : (∑ x : Fin m, augmented A s (.inr x) j *
      ∑ k, augmented A s (.inr x) k * g i k) =
      ∑ x : Fin m, (if x ∈ s then (Pi.single x 1 : Fin m → ℚ) j else 0) *
        (if x ∈ s then g i x else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    change augmented A s (.inr x) j * (augmented A s *ᵥ g i) (.inr x) = _
    rw [augmented_mulVec_inr]
    by_cases hx : x ∈ s <;> simp [augmented, hx]
  rw [hright]
  simp only [Pi.single_apply]
  by_cases hjs : j ∈ s
  · simpa [hjs, eq_comm] using hg.2 i j hjs
  · simp [hjs, show i ≠ j by intro h; exact hjs (h ▸ hi), eq_comm]

/-- Cast an integer matrix to a rational matrix. -/
def rationalMatrix {n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ) :
    Matrix (Fin n) (Fin m) ℚ := fun i j => A i j

/-- Integer Gram matrix of the equations and their surviving free coordinates. -/
def integerGram {n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ) (s : Finset (Fin m)) :
    Matrix (Fin m) (Fin m) ℤ := (augmented A s)ᵀ * augmented A s

theorem rational_augmented {n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ)
    (s : Finset (Fin m)) :
    (fun i j => ((augmented A s i j : ℤ) : ℚ)) = augmented (rationalMatrix A) s := by
  ext i j
  cases i with
  | inl i => rfl
  | inr i =>
      by_cases hi : i ∈ s <;> simp [augmented, hi, Pi.single_apply]

theorem rational_integerGram {n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ)
    (s : Finset (Fin m)) :
    rationalMatrix (integerGram A s) =
      (augmented (rationalMatrix A) s)ᵀ * augmented (rationalMatrix A) s := by
  ext i j
  simp only [rationalMatrix, integerGram, mul_apply, transpose_apply,
    Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hki := congrFun (congrFun (rational_augmented A s) k) i
  have hkj := congrFun (congrFun (rational_augmented A s) k) j
  rw [hki, hkj]

theorem rational_det (A : Matrix (Fin m) (Fin m) ℤ) :
    (A.det : ℚ) = (rationalMatrix A).det :=
  (Int.castRingHom ℚ).map_det A

theorem rational_updateCol_single (A : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) :
    rationalMatrix (A.updateCol j (Pi.single i 1)) =
      (rationalMatrix A).updateCol j (Pi.single i 1) := by
  ext k l
  by_cases hl : l = j
  · subst l
    simp [rationalMatrix, Pi.single_apply]
  · simp [rationalMatrix, Matrix.updateCol_ne hl]

theorem cramer_solution (H : Matrix (Fin m) (Fin m) ℤ) (hH : H.det ≠ 0)
    (x : Fin m → ℚ) (i : Fin m)
    (hx : rationalMatrix H *ᵥ x = Pi.single i 1) (j : Fin m) :
    x j = ((H.updateCol j (Pi.single i 1)).det : ℚ) / H.det := by
  have hd : (H.det : ℚ) ≠ 0 := by exact_mod_cast hH
  apply (eq_div_iff hd).mpr
  have heq : (rationalMatrix H).cramer ((rationalMatrix H) *ᵥ x) =
      (rationalMatrix H).det • x := by
    rw [cramer_eq_adjugate_mulVec, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  rw [hx] at heq
  have hj := congrFun heq j
  rw [cramer_apply, ← rational_updateCol_single, ← rational_det, ← rational_det] at hj
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hj.symm

/-- Every output coordinate of the actual elimination routine is an integer
Gram determinant ratio, or zero for a discarded generator. -/
theorem kernelGenerators_certificate {n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ) :
    ∃ s g,
      kernelGenerators (rationalMatrix A) = List.ofFn g ∧
      Canonical s g ∧
      (integerGram A s).det ≠ 0 ∧
      ∀ i j, g i j = if i ∈ s then
        (((integerGram A s).updateCol j (Pi.single i 1)).det : ℚ) /
          (integerGram A s).det else 0 := by
  obtain ⟨s, g, heq, hg⟩ := canonical_eliminateRows
    (List.ofFn fun i => rowMap (rationalMatrix A i))
    Finset.univ (fun i => Pi.single i 1) canonical_coordinateVectors
  change kernelGenerators (rationalMatrix A) = List.ofFn g at heq
  have hspan : listSpan (List.ofFn g) = LinearMap.ker (rationalMatrix A).mulVecLin := by
    rw [← heq, kernelGenerators_span]
  have hunit := gram_isUnit (rationalMatrix A) s g hg hspan
  rw [← rational_integerGram] at hunit
  have hdet : (integerGram A s).det ≠ 0 := by
    have hq := (isUnit_iff_isUnit_det _).mp hunit
    rw [← rational_det, isUnit_iff_ne_zero] at hq
    exact_mod_cast hq
  refine ⟨s, g, heq, hg, hdet, ?_⟩
  intro i j
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi]
    apply cramer_solution _ hdet _ i
    rw [rational_integerGram]
    exact gram_mul_generator _ s g hg hspan i hi
  · simp only [ite_eq_right hi, hg.1 i hi, Pi.zero_apply]

theorem augmented_natAbs_le_pow {n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ)
    (B : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ B) (s : Finset (Fin m)) :
    ∀ i j, (augmented A s i j).natAbs ≤ 2 ^ B := by
  intro i j
  cases i with
  | inl i => exact hA i j
  | inr i =>
      by_cases hi : i ∈ s
      · by_cases hij : i = j
        · subst j
          simpa [augmented, hi] using (Nat.one_le_two_pow : 1 ≤ 2 ^ B)
        · simp [augmented, hi, Ne.symm hij]
      · simp [augmented, hi]

/-- The Gram entries have bit length bounded by the input length and dimensions. -/
theorem integerGram_natAbs_le_pow {n : ℕ} (A : Matrix (Fin n) (Fin m) ℤ)
    (B : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ B) (s : Finset (Fin m)) :
    ∀ i j, (integerGram A s i j).natAbs ≤ 2 ^ (n + m + 2 * B) := by
  intro i j
  change (∑ k, augmented A s k i * augmented A s k j).natAbs ≤ _
  calc
    _ ≤ ∑ k : Fin n ⊕ Fin m, (augmented A s k i * augmented A s k j).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _k : Fin n ⊕ Fin m, 2 ^ B * 2 ^ B := by
      apply Finset.sum_le_sum
      intro k _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (augmented_natAbs_le_pow A B hA s k i)
        (augmented_natAbs_le_pow A B hA s k j)
    _ = (n + m) * (2 ^ B * 2 ^ B) := by simp
    _ ≤ 2 ^ (n + m) * (2 ^ B * 2 ^ B) :=
      Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ = 2 ^ (n + m + 2 * B) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega

/-- Uniform polynomial binary length for every coordinate actually produced
by rational elimination on an integer matrix. -/
theorem kernelGenerators_coordinate_size {n : ℕ}
    (A : Matrix (Fin n) (Fin m) ℤ) (B : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ B)
    (x : Fin m → ℚ) (hx : x ∈ kernelGenerators (rationalMatrix A)) (j : Fin m) :
    (x j).num.natAbs.size ≤ (n + m + 2 * B) * m + m ^ 2 + 1 ∧
    (x j).den.size ≤ (n + m + 2 * B) * m + m ^ 2 + 1 := by
  obtain ⟨s, g, heq, _hg, hdet, hcoord⟩ := kernelGenerators_certificate A
  rw [heq] at hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  rw [hcoord]
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi]
    simpa only [Fintype.card_fin] using
      DeterminantSize.cramer_unit_size_le (integerGram A s) (n + m + 2 * B)
        (integerGram_natAbs_le_pow A B hA s) hdet j i
  · simp only [ite_eq_right hi, Rat.num_zero, Int.natAbs_zero, Nat.size_zero,
      Rat.den_zero, Nat.size_one]
    omega

/-- View an input list of integer equations as a finite matrix. -/
def rowsMatrix (rows : List (Fin m → ℤ)) : Matrix (Fin rows.length) (Fin m) ℤ :=
  fun i => rows[i.val]

theorem rowsMatrix_generators (rows : List (Fin m → ℤ)) :
    kernelGenerators (rationalMatrix (rowsMatrix rows)) =
      eliminateRows (rows.map (fun r => rowMap (fun j => (r j : ℚ))))
        (coordinateVectors m) := by
  unfold kernelGenerators
  congr 1
  conv_rhs => rw [← List.ofFn_get rows, List.map_ofFn]
  rfl

/-- The bound applies after any list of processed equations, independently of
which equations were redundant and which pivot coordinates were selected. -/
theorem eliminateRows_coordinate_size (rows : List (Fin m → ℤ)) (B : ℕ)
    (hrows : ∀ r ∈ rows, ∀ j, (r j).natAbs ≤ 2 ^ B)
    (x : Fin m → ℚ)
    (hx : x ∈ eliminateRows (rows.map (fun r => rowMap (fun j => (r j : ℚ))))
      (coordinateVectors m)) (j : Fin m) :
    (x j).num.natAbs.size ≤ (rows.length + m + 2 * B) * m + m ^ 2 + 1 ∧
    (x j).den.size ≤ (rows.length + m + 2 * B) * m + m ^ 2 + 1 := by
  apply kernelGenerators_coordinate_size (rowsMatrix rows) B ?_ x ?_ j
  · intro i j
    exact hrows _ (List.getElem_mem i.isLt) j
  · rwa [rowsMatrix_generators]

/-- All intermediate row prefixes have the same polynomial coordinate bound. -/
theorem prefix_coordinate_size (rows : List (Fin m → ℤ)) (B : ℕ)
    (hrows : ∀ r ∈ rows, ∀ j, (r j).natAbs ≤ 2 ^ B) (k : ℕ)
    (x : Fin m → ℚ)
    (hx : x ∈ eliminateRows ((rows.take k).map (fun r => rowMap (fun j => (r j : ℚ))))
      (coordinateVectors m)) (j : Fin m) :
    (x j).num.natAbs.size ≤ (rows.length + m + 2 * B) * m + m ^ 2 + 1 ∧
    (x j).den.size ≤ (rows.length + m + 2 * B) * m + m ^ 2 + 1 := by
  have h := eliminateRows_coordinate_size (rows.take k) B
    (fun r hr => hrows r (List.mem_of_mem_take hr)) x hx j
  have hlen : (rows.take k).length ≤ rows.length := by simp
  have hmul := Nat.mul_le_mul_right m (Nat.add_le_add_right (Nat.add_le_add_right hlen m) (2 * B))
  constructor <;> omega

end WeightedMIS.EliminationCertificate
