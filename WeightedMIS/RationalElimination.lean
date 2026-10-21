module

public import Mathlib

/-!
# Deterministic rational kernel generators

Constraints are processed in their input order. For each constraint, the first
current generator on which it is nonzero is the pivot; all current generators
are projected along that pivot into the new kernel. The generator list keeps
its original length. This is an executable rational elimination routine with
an exact span invariant. Arithmetic operation and bit costs are separate.
-/

@[expose] public section

namespace WeightedMIS.RationalElimination

open Matrix

section Module

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- The linear span of the members of a list. -/
def listSpan (vs : List M) : Submodule ℚ M := Submodule.span ℚ {v | v ∈ vs}

/-- Projection along a selected pivot into the kernel of a linear constraint. -/
def project (c : M →ₗ[ℚ] ℚ) (p : M) : M →ₗ[ℚ] M :=
  LinearMap.id - (c p)⁻¹ • c.smulRight p

theorem project_apply (c : M →ₗ[ℚ] ℚ) (p v : M) :
    project c p v = v - (c v / c p) • p := by
  simp [project, div_eq_mul_inv, mul_comm, smul_smul]

/-- Deterministically process one linear equation. -/
def cut (c : M →ₗ[ℚ] ℚ) (vs : List M) : List M :=
  match vs.find? (fun v => decide (c v ≠ 0)) with
  | none => vs
  | some p => vs.map (project c p)

theorem cut_length (c : M →ₗ[ℚ] ℚ) (vs : List M) : (cut c vs).length = vs.length := by
  unfold cut
  split <;> simp

theorem listSpan_map (f : M →ₗ[ℚ] M) (vs : List M) :
    listSpan (vs.map f) = (listSpan vs).map f := by
  unfold listSpan
  rw [Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_image]

/-- Projection computes the intersection with the new equation exactly. -/
theorem listSpan_cut (c : M →ₗ[ℚ] ℚ) (vs : List M) :
    listSpan (cut c vs) = listSpan vs ⊓ LinearMap.ker c := by
  classical
  unfold cut
  split
  next hnone =>
    have hzero : ∀ v ∈ vs, c v = 0 := by simpa using List.find?_eq_none.mp hnone
    have hle : listSpan vs ≤ LinearMap.ker c :=
      Submodule.span_le.mpr (fun v hv => hzero v hv)
    exact (inf_eq_left.mpr hle).symm
  next p hp =>
    have hp_mem : p ∈ vs := List.mem_of_find?_eq_some hp
    have hp_ne : c p ≠ 0 := by simpa using List.find?_some hp
    rw [listSpan_map]
    apply le_antisymm
    · rintro y ⟨v, hv, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [project_apply]
        exact (listSpan vs).sub_mem hv ((listSpan vs).smul_mem _ (Submodule.subset_span hp_mem))
      · change c (project c p v) = 0
        rw [project_apply, map_sub, map_smul]
        simp [div_mul_cancel₀ _ hp_ne]
    · intro v hv
      refine ⟨v, hv.1, ?_⟩
      rw [project_apply, show c v = 0 from hv.2]
      simp

/-- The simultaneous kernel of a list of linear equations. -/
def constraintKernel : List (M →ₗ[ℚ] ℚ) → Submodule ℚ M
  | [] => ⊤
  | c :: cs => LinearMap.ker c ⊓ constraintKernel cs

theorem mem_constraintKernel (cs : List (M →ₗ[ℚ] ℚ)) (v : M) :
    v ∈ constraintKernel cs ↔ ∀ c ∈ cs, c v = 0 := by
  induction cs with
  | nil => simp [constraintKernel]
  | cons c cs ih => simp [constraintKernel, ih]

/-- Process all equations using exact rational arithmetic and first-pivot search. -/
def eliminateRows : List (M →ₗ[ℚ] ℚ) → List M → List M
  | [], vs => vs
  | c :: cs, vs => eliminateRows cs (cut c vs)

theorem eliminateRows_length (cs : List (M →ₗ[ℚ] ℚ)) (vs : List M) :
    (eliminateRows cs vs).length = vs.length := by
  induction cs generalizing vs with
  | nil => rfl
  | cons c cs ih => simp [eliminateRows, ih, cut_length]

/-- The exact loop invariant: the output spans precisely the original span
intersected with every equation processed. -/
theorem listSpan_eliminateRows (cs : List (M →ₗ[ℚ] ℚ)) (vs : List M) :
    listSpan (eliminateRows cs vs) = listSpan vs ⊓ constraintKernel cs := by
  induction cs generalizing vs with
  | nil => simp [eliminateRows, constraintKernel]
  | cons c cs ih =>
      rw [eliminateRows, ih, listSpan_cut, constraintKernel, inf_assoc]

end Module

/-- A row vector viewed as its dot-product linear functional. -/
def rowMap {m : ℕ} (v : Fin m → ℚ) : (Fin m → ℚ) →ₗ[ℚ] ℚ :=
  dotProductBilin ℚ ℚ v

@[simp] theorem rowMap_apply {m : ℕ} (v x : Fin m → ℚ) :
    rowMap v x = dotProduct v x := rfl

/-- The coordinate vectors in their canonical numeric order. -/
def coordinateVectors (m : ℕ) : List (Fin m → ℚ) :=
  List.ofFn fun i => Pi.single i 1

theorem coordinateVectors_span (m : ℕ) : listSpan (coordinateVectors m) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  have heq : x = ∑ i : Fin m, x i • Pi.single i (1 : ℚ) := by
    ext j
    simp [Pi.single_apply]
  rw [heq]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- A deterministic list of `m` rational vectors spanning the nullspace of
an `n` by `m` matrix; zero vectors are retained. -/
def kernelGenerators {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℚ) : List (Fin m → ℚ) :=
  eliminateRows (List.ofFn fun i => rowMap (A i)) (coordinateVectors m)

theorem kernelGenerators_length {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℚ) :
    (kernelGenerators A).length = m := by
  simp [kernelGenerators, eliminateRows_length, coordinateVectors]

/-- Correctness for arbitrary input matrices, without a supplied echelon
certificate, rank assumption, or preexisting nullspace basis. -/
theorem kernelGenerators_span {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℚ) :
    listSpan (kernelGenerators A) = LinearMap.ker A.mulVecLin := by
  rw [kernelGenerators, listSpan_eliminateRows, coordinateVectors_span, top_inf_eq]
  ext x
  rw [mem_constraintKernel]
  constructor
  · intro h
    apply LinearMap.mem_ker.mpr
    ext i
    exact h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact congrFun h i

end WeightedMIS.RationalElimination
