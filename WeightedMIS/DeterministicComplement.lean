module

public import WeightedMIS.RationalElimination
public import WeightedMIS.StoredElimination

/-!
# Deterministic selection of a row-space complement

Membership in a rational row span is tested using the computed nullspace
of those rows. Scanning candidate rows and retaining precisely those outside
the current span gives a deterministic complement. Every retained row is an
original candidate, so its integral coefficients and bounds are preserved.
-/

@[expose] public section

namespace WeightedMIS.DeterministicComplement

open Matrix RationalElimination

variable {m : ℕ}

/-- The standard dot-product bilinear form. -/
def dotForm : LinearMap.BilinForm ℚ (Fin m → ℚ) := dotProductBilin ℚ ℚ

theorem dotForm_nondegenerate : (dotForm (m := m)).Nondegenerate := by
  constructor
  · intro x hx
    ext i
    have h := hx (Pi.single i 1)
    simpa [dotForm, dotProductBilin, dotProduct, Pi.single_apply] using h
  · intro x hx
    ext i
    have h := hx (Pi.single i 1)
    simpa [dotForm, dotProductBilin, dotProduct, Pi.single_apply] using h

theorem dotForm_refl : (dotForm (m := m)).IsRefl := by
  intro x y h
  change dotProduct x y = 0 at h
  change dotProduct y x = 0
  simpa only [dotProduct_comm] using h

/-- Orthogonality to all rows is equivalent to orthogonality to their span. -/
theorem orthogonal_listSpan (rows : List (Fin m → ℚ)) :
    dotForm.orthogonal (listSpan rows) = constraintKernel (rows.map rowMap) := by
  ext x
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_constraintKernel]
  constructor
  · intro h c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    exact h v (Submodule.subset_span hv)
  · intro h v hv
    have hle : listSpan rows ≤ LinearMap.ker (rowMap x) := by
      apply Submodule.span_le.mpr
      intro r hr
      have hz := h (rowMap r) (List.mem_map.mpr ⟨r, hr, rfl⟩)
      change dotProduct x r = 0
      simpa only [rowMap_apply, dotProduct_comm] using hz
    have hz := hle hv
    change dotProduct v x = 0
    simpa only [LinearMap.mem_ker, rowMap_apply, dotProduct_comm] using hz

/-- Deterministically computed generators of the row annihilator. -/
def annihilatorGenerators (rows : List (Fin m → ℚ)) : List (Fin m → ℚ) :=
  (StoredElimination.eliminateRows (rows.map StoredElimination.encode)
    (StoredElimination.coordinateVectors m)).map StoredElimination.decode

theorem annihilatorGenerators_eq (rows : List (Fin m → ℚ)) :
    annihilatorGenerators rows = eliminateRows (rows.map rowMap) (coordinateVectors m) := by
  rw [annihilatorGenerators, StoredElimination.decode_eliminateRows,
    StoredElimination.decode_coordinateVectors]
  simp [List.map_map, Function.comp_def]

theorem annihilatorGenerators_span (rows : List (Fin m → ℚ)) :
    listSpan (annihilatorGenerators rows) = dotForm.orthogonal (listSpan rows) := by
  rw [annihilatorGenerators_eq, listSpan_eliminateRows, coordinateVectors_span, top_inf_eq,
    orthogonal_listSpan]

/-- Membership in the original span is decided by the computed annihilator. -/
theorem mem_listSpan_iff (rows : List (Fin m → ℚ)) (x : Fin m → ℚ) :
    x ∈ listSpan rows ↔ ∀ y ∈ annihilatorGenerators rows, dotProduct x y = 0 := by
  have hdouble := LinearMap.BilinForm.orthogonal_orthogonal
    dotForm_nondegenerate dotForm_refl (listSpan rows)
  rw [← hdouble, ← annihilatorGenerators_span, orthogonal_listSpan, mem_constraintKernel]
  constructor
  · intro h y hy
    have hz := h (rowMap y) (List.mem_map.mpr ⟨y, hy, rfl⟩)
    simpa only [rowMap_apply, dotProduct_comm] using hz
  · intro h c hc
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
    simpa only [rowMap_apply, dotProduct_comm] using h y hy

/-- An executable test for a vector outside the current row span. -/
def outside (rows : List (Fin m → ℚ)) (x : Fin m → ℚ) : Bool :=
  (annihilatorGenerators rows).any fun y => decide (dotProduct x y ≠ 0)

theorem outside_iff (rows : List (Fin m → ℚ)) (x : Fin m → ℚ) :
    outside rows x = true ↔ x ∉ listSpan rows := by
  rw [mem_listSpan_iff]
  simp [outside, List.any_eq_true, not_forall]

/-- Scan candidates in input order and keep every row that increases the span. -/
def select (rows : List (Fin m → ℚ)) : List (Fin m → ℚ) → List (Fin m → ℚ)
  | [] => []
  | v :: vs => if outside rows v then v :: select (v :: rows) vs else select rows vs

theorem select_sublist (rows candidates : List (Fin m → ℚ)) :
    (select rows candidates).Sublist candidates := by
  induction candidates generalizing rows with
  | nil => exact List.Sublist.refl _
  | cons v vs ih =>
      simp only [select]
      split
      · exact (ih (v :: rows)).cons_cons v
      · exact (ih rows).cons v

@[simp] theorem listSpan_nil : listSpan ([] : List (Fin m → ℚ)) = ⊥ := by
  simp [listSpan]

theorem listSpan_append (a b : List (Fin m → ℚ)) :
    listSpan (a ++ b) = listSpan a ⊔ listSpan b := by
  unfold listSpan
  rw [← Submodule.span_union]
  congr 1
  ext x
  simp

theorem listSpan_cons (v : Fin m → ℚ) (vs : List (Fin m → ℚ)) :
    listSpan (v :: vs) = listSpan vs ⊔ Submodule.span ℚ {v} := by
  unfold listSpan
  rw [← Submodule.span_union]
  congr 1
  ext x
  simp

theorem listSpan_append_cons_of_mem (rows : List (Fin m → ℚ)) (v : Fin m → ℚ)
    (vs : List (Fin m → ℚ)) (hv : v ∈ listSpan rows) :
    listSpan (rows ++ v :: vs) = listSpan (rows ++ vs) := by
  have hle : Submodule.span ℚ {v} ≤ listSpan rows :=
    Submodule.span_le.mpr (by intro x hx; simpa using Set.mem_singleton_iff.mp hx ▸ hv)
  simp only [listSpan_append, listSpan_cons, ← sup_assoc]
  exact sup_eq_left.mpr (hle.trans le_sup_left)

/-- The selected rows extend the initial span to the complete candidate span. -/
theorem select_span (rows candidates : List (Fin m → ℚ)) :
    listSpan rows ⊔ listSpan (select rows candidates) = listSpan (rows ++ candidates) := by
  induction candidates generalizing rows with
  | nil => simp [select]
  | cons v vs ih =>
      by_cases h : outside rows v = true
      · simp only [select, h, ↓reduceIte, listSpan_cons]
        have hi := ih (v :: rows)
        rw [listSpan_cons, listSpan_append, listSpan_cons] at hi
        rw [listSpan_append, listSpan_cons]
        simpa only [sup_assoc, sup_left_comm, sup_comm] using hi
      · have hv : v ∈ listSpan rows := by simpa only [outside_iff, not_not] using h
        simp only [select, h, Bool.false_eq_true, ↓reduceIte]
        rw [ih, listSpan_append_cons_of_mem rows v vs hv]

/-- The number retained equals the dimension gained by adjoining all candidates. -/
theorem select_length_add_finrank (rows candidates : List (Fin m → ℚ)) :
    (select rows candidates).length + Module.finrank ℚ (listSpan rows) =
      Module.finrank ℚ (listSpan (rows ++ candidates)) := by
  induction candidates generalizing rows with
  | nil =>
      simp only [select, List.length_nil, zero_add]
      exact congrArg (fun vs : List (Fin m → ℚ) => Module.finrank ℚ (listSpan vs))
        (List.append_nil rows).symm
  | cons v vs ih =>
      by_cases h : outside rows v = true
      · have hv : v ∉ listSpan rows := (outside_iff rows v).mp h
        have hd : Module.finrank ℚ (listSpan (v :: rows)) =
            Module.finrank ℚ (listSpan rows) + 1 := by
          rw [listSpan_cons]
          exact Submodule.finrank_sup_span_singleton hv
        have hi := ih (v :: rows)
        have heq : listSpan ((v :: rows) ++ vs) = listSpan (rows ++ v :: vs) := by
          simp only [listSpan_append, listSpan_cons, sup_assoc, sup_left_comm, sup_comm]
        rw [heq, hd] at hi
        simp only [select, h, ↓reduceIte, List.length_cons]
        omega
      · have hv : v ∈ listSpan rows := by simpa only [outside_iff, not_not] using h
        simp only [select, h, Bool.false_eq_true, ↓reduceIte]
        rw [listSpan_append_cons_of_mem rows v vs hv]
        exact ih rows

theorem select_length (rows candidates : List (Fin m → ℚ)) :
    (select rows candidates).length =
      Module.finrank ℚ (listSpan (rows ++ candidates)) - Module.finrank ℚ (listSpan rows) := by
  have h := select_length_add_finrank rows candidates
  omega

end WeightedMIS.DeterministicComplement
