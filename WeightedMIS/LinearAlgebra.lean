module

public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic

/-!
# Kernel equations for rational edge slacks

This file proves the linear-algebra implication in Lemma 8 of the
manuscript. The ordinary row-span equality is an explicit premise: the
construction of the even-face matrix and bounded extra rows, and their rank
properties, are not established here. No connectivity or rank assumption is
needed for existence of a rational solution. Integer recovery requires the
separate parity and connectivity argument.
-/

public section

namespace WeightedMIS.LinearAlgebra

open Matrix

variable {V E R S : Type*} [Fintype V] [Fintype E]

/-- An ordinary finite matrix has `b` in its image exactly when `b` annihilates
its left kernel. This is algebraic duality over the rationals. -/
theorem exists_mulVec_eq_iff (A : Matrix E V ℚ) (b : E → ℚ) :
    (∃ x : V → ℚ, A *ᵥ x = b) ↔
      ∀ g : E → ℚ, Aᵀ *ᵥ g = 0 → g ⬝ᵥ b = 0 := by
  classical
  constructor
  · rintro ⟨x, rfl⟩ g hg
    rw [dotProduct_mulVec, ← mulVec_transpose, hg, zero_dotProduct]
  · intro h
    have hb : b ∈ LinearMap.range A.mulVecLin := by
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
        (LinearMap.range A.mulVecLin) b).mp
      intro φ hφ
      let g : E → ℚ := (dotProductEquiv ℚ E).symm φ
      have hφg : dotProductEquiv ℚ E g = φ :=
        (dotProductEquiv ℚ E).apply_symm_apply φ
      have hg : Aᵀ *ᵥ g = 0 := by
        apply dotProduct_eq_zero
        intro x
        rw [mulVec_transpose, ← dotProduct_mulVec]
        change (dotProductEquiv ℚ E g) (A *ᵥ x) = 0
        rw [hφg]
        exact (Submodule.mem_dualAnnihilator φ).mp hφ _ ⟨x, rfl⟩
      have hgb := h g hg
      change (dotProductEquiv ℚ E g) b = 0 at hgb
      rwa [hφg] at hgb
    exact hb

/-- If the rows of `B` and `W` span the left kernel of `A`, their homogeneous
equations characterize the rational image of `A`. The span hypothesis is
explicit and is not an axiom or an encoded algorithmic conclusion. -/
theorem kernel_equations_iff_image
    (A : Matrix E V ℚ) (B : Matrix R E ℚ) (W : Matrix S E ℚ)
    (hspan : Submodule.span ℚ (Set.range B ∪ Set.range W) =
      LinearMap.ker Aᵀ.mulVecLin)
    (y : E → ℚ) :
    B *ᵥ y = 0 ∧ W *ᵥ y = 0 ↔ ∃ x : V → ℚ, A *ᵥ x = y := by
  classical
  rw [exists_mulVec_eq_iff]
  constructor
  · rintro ⟨hB, hW⟩
    have hrows : Submodule.span ℚ (Set.range B ∪ Set.range W) ≤
        LinearMap.ker (dotProductEquiv ℚ E y) := by
      apply Submodule.span_le.mpr
      intro g hg
      rcases hg with hg | hg
      · obtain ⟨i, rfl⟩ := hg
        change y ⬝ᵥ B i = 0
        rw [dotProduct_comm]
        exact congrFun hB i
      · obtain ⟨i, rfl⟩ := hg
        change y ⬝ᵥ W i = 0
        rw [dotProduct_comm]
        exact congrFun hW i
    intro g hg
    have hmem : g ∈ Submodule.span ℚ (Set.range B ∪ Set.range W) := by
      rw [hspan]
      exact hg
    have hz := hrows hmem
    change y ⬝ᵥ g = 0 at hz
    rwa [dotProduct_comm] at hz
  · intro h
    constructor
    · ext i
      apply h
      have hi : B i ∈ Submodule.span ℚ (Set.range B ∪ Set.range W) :=
        Submodule.subset_span (Or.inl ⟨i, rfl⟩)
      rw [hspan] at hi
      exact hi
    · ext i
      apply h
      have hi : W i ∈ Submodule.span ℚ (Set.range B ∪ Set.range W) :=
        Submodule.subset_span (Or.inr ⟨i, rfl⟩)
      rw [hspan] at hi
      exact hi

omit [Fintype E] in
/-- The unsigned incidence identity `A * 1 = 2 * 1` puts the constant edge
vector in the rational image; the constant vertex vector `1/2` is a witness. -/
theorem one_in_image (A : Matrix E V ℚ)
    (hA : A *ᵥ (1 : V → ℚ) = (2 : ℚ) • (1 : E → ℚ)) :
    ∃ x : V → ℚ, A *ᵥ x = (1 : E → ℚ) := by
  refine ⟨(1 / 2 : ℚ) • (1 : V → ℚ), ?_⟩
  rw [mulVec_smul, hA, smul_smul]
  norm_num

/-- Rational feasibility part of manuscript Lemma 8. The even-face and extra
kernel equations are equivalent to an actual solution of `A*x = 1-y`.
Constructing matrices with the stated span remains a separate obligation. -/
theorem kernel_equations_iff_slack
    (A : Matrix E V ℚ) (B : Matrix R E ℚ) (W : Matrix S E ℚ)
    (hspan : Submodule.span ℚ (Set.range B ∪ Set.range W) =
      LinearMap.ker Aᵀ.mulVecLin)
    (hA : A *ᵥ (1 : V → ℚ) = (2 : ℚ) • (1 : E → ℚ))
    (y : E → ℚ) :
    B *ᵥ y = 0 ∧ W *ᵥ y = 0 ↔
      ∃ x : V → ℚ, A *ᵥ x = (1 : E → ℚ) - y := by
  have hones := (kernel_equations_iff_image A B W hspan (1 : E → ℚ)).mpr
    (one_in_image A hA)
  rw [← kernel_equations_iff_image A B W hspan]
  simp only [mulVec_sub, hones.1, hones.2, zero_sub, neg_eq_zero]

end WeightedMIS.LinearAlgebra
