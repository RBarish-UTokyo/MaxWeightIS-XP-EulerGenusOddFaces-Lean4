module

public import WeightedMIS.EnumeratedEmbedding
public import WeightedMIS.ComputedColumns

/-!
# Explicit stored even-face matrices and signed columns

The deterministic boundary output is filtered in its computed order. Its even
rows are stored as finite integer lists, and signed columns are produced by
the supplied-list conversion. Proof-level equivalences certify the rows against
the actual face matrix and derive the two-stub bound from the actual side pairing.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.Ribbon

open SidePairing FiniteCycleEnumeration

variable {V E : Type*} [Fintype E] [DecidableEq E] {left right : E → V}
    (R : Ribbon left right) (order : List (Flag E))

/-- Keep exactly the computed faces of even actual boundary length. -/
def evenRootIndices : List (R.EnumeratedIndex order) :=
  (List.finRange (R.enumeratedRoots order).length).filter
    (fun i => decide (Even (R.enumeratedFace order i).boundary.length))

@[simp] theorem mem_evenRootIndices (i : R.EnumeratedIndex order) :
    i ∈ R.evenRootIndices order ↔ Even (R.enumeratedFace order i).boundary.length := by
  simp [evenRootIndices]

theorem evenRootIndices_nodup : (R.evenRootIndices order).Nodup :=
  (List.nodup_finRange _).filter _

/-- Actual finite row indices of the explicitly stored even-face matrix. -/
abbrev EvenRowIndex := Fin (R.evenRootIndices order).length

/-- The actual even face at a stored row index. -/
def evenRowFace (r : R.EvenRowIndex order) : Faces.EvenFaces (R.enumeratedFace order) :=
  ⟨(R.evenRootIndices order).get r,
    (R.mem_evenRootIndices order _).mp (List.get_mem _ _)⟩

theorem evenRowFace_injective : Function.Injective (R.evenRowFace order) := by
  intro r s h
  exact (List.nodup_iff_injective_get.mp (R.evenRootIndices_nodup order))
    (congrArg Subtype.val h)

theorem evenRowFace_surjective : Function.Surjective (R.evenRowFace order) := by
  rintro ⟨i, hi⟩
  obtain ⟨r, hr⟩ := List.get_of_mem ((R.mem_evenRootIndices order i).mpr hi)
  exact ⟨r, Subtype.ext hr⟩

/-- Stored row numbers correspond exactly to genuine even facial rows. -/
noncomputable def evenRowEquiv : R.EvenRowIndex order ≃ Faces.EvenFaces (R.enumeratedFace order) :=
  Equiv.ofBijective (R.evenRowFace order)
    ⟨R.evenRowFace_injective order, R.evenRowFace_surjective order⟩

/-- Compute an integer row directly from its actual boundary walk. -/
def computedIntegerMatrix : Matrix (R.EvenRowIndex order) E ℤ := fun r e =>
  (R.enumeratedFace order ((R.evenRootIndices order).get r)).boundary.row e

/-- The stored row is exactly its certified actual even-face row. -/
theorem computedIntegerMatrix_eq (r : R.EvenRowIndex order) (e : E) :
    R.computedIntegerMatrix order r e =
      Faces.integerMatrix (R.enumeratedFace order) (R.evenRowEquiv order r) e := rfl

/-- The actual two-side theorem bounds every computed column by two signed
stubs, including repeated facial incidences and magnitude-two entries. -/
theorem computedIntegerMatrix_column_bound (horder : ∀ x : Flag E, x ∈ order) (e : E) :
    (∑ r : R.EvenRowIndex order, (R.computedIntegerMatrix order r e).natAbs) ≤ 2 := by
  classical
  have h := Faces.column_natAbs_sum_le_two (R.enumeratedFace order)
    (R.enumeratedSidePairing order horder).twoSides e
  have heq := Fintype.sum_equiv (R.evenRowEquiv order)
    (fun r => (R.computedIntegerMatrix order r e).natAbs)
    (fun f => (Faces.integerMatrix (R.enumeratedFace order) f e).natAbs)
    (fun r => rfl)
  rwa [heq]

/-- Deterministic signed columns indexed by the actually emitted even rows. -/
def computedColumn (e : E) : Walks.Column (R.EvenRowIndex order) :=
  ComputedColumns.indexedColumn (fun r => R.computedIntegerMatrix order r e)

/-- Every computed signed column expands to the actual stored matrix column. -/
theorem computedColumn_spec (horder : ∀ x : Flag E, x ∈ order)
    (e : E) (r : R.EvenRowIndex order) :
    Walks.columnVector (R.computedColumn order e) r = R.computedIntegerMatrix order r e :=
  ComputedColumns.indexedColumn_spec _ (R.computedIntegerMatrix_column_bound order horder e) r

/-- The signed-stub output for each original edge has at most two positions. -/
theorem computedColumn_stub_length (horder : ∀ x : Flag E, x ∈ order) (e : E) :
    (ColumnEncoding.signedCopies (List.finRange (R.evenRootIndices order).length)
      (fun r => R.computedIntegerMatrix order r e)).length ≤ 2 :=
  ComputedColumns.emitted_length _ (R.computedIntegerMatrix_column_bound order horder e)

/-- Filtering does not enlarge the computed face-index list. -/
theorem evenRow_count_le : (R.evenRootIndices order).length ≤ order.length := by
  have hf := List.length_filter_le
    (fun i => decide (Even (R.enumeratedFace order i).boundary.length))
    (List.finRange (R.enumeratedRoots order).length)
  simp only [List.length_finRange] at hf
  exact hf.trans (R.enumeratedRoots_length_le order)

end WeightedMIS.EmbeddingFaces.Ribbon

namespace WeightedMIS.EmbeddingFaces.Ribbon

variable {V : Type*} {m : ℕ} {left right : Fin m → V} (R : Ribbon left right)

/-- A fully explicit list-of-lists integer matrix in the canonical flag order. -/
def storedEvenMatrix : List (List ℤ) :=
  (List.finRange (R.evenRootIndices (Flag.canonicalOrder m)).length).map fun r =>
    (List.finRange m).map fun e => R.computedIntegerMatrix (Flag.canonicalOrder m) r e

@[simp] theorem storedEvenMatrix_rows :
    R.storedEvenMatrix.length = (R.evenRootIndices (Flag.canonicalOrder m)).length := by
  simp [storedEvenMatrix]

/-- Every stored row has exactly one entry for each original edge label. -/
theorem storedEvenMatrix_row_length (row : List ℤ) (hr : row ∈ R.storedEvenMatrix) :
    row.length = m := by
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hr
  simp

/-- The fully stored matrix has a quadratic number of integer positions. -/
theorem storedEvenMatrix_cells_le :
    (R.storedEvenMatrix.map List.length).sum ≤ 4 * m * m := by
  have hsum : ∀ rows : List (List ℤ), (∀ row ∈ rows, row.length = m) →
      (rows.map List.length).sum = rows.length * m := by
    intro rows
    induction rows with
    | nil => intro _; simp
    | cons row rows ih =>
      intro hrows
      have hh := hrows row List.mem_cons_self
      have ht := ih (fun r hr => hrows r (List.mem_cons_of_mem row hr))
      simp only [List.map_cons, List.sum_cons, List.length_cons, hh, ht]
      nlinarith
  have hrow := hsum R.storedEvenMatrix R.storedEvenMatrix_row_length
  rw [hrow, R.storedEvenMatrix_rows]
  have h := R.evenRow_count_le (Flag.canonicalOrder m)
  rw [Flag.canonicalOrder_length] at h
  exact Nat.mul_le_mul_right m h

/-- The complete deterministic signed-column list, in original edge order. -/
def storedColumns : List (Walks.Column (R.EvenRowIndex (Flag.canonicalOrder m))) :=
  (List.finRange m).map (R.computedColumn (Flag.canonicalOrder m))

@[simp] theorem storedColumns_length : R.storedColumns.length = m := by simp [storedColumns]

end WeightedMIS.EmbeddingFaces.Ribbon
