module

public import WeightedMIS.FaceRowSemantics

/-!
# Signed columns from stored rows

Columns are accumulated from the last row to the first: each row prepends to
the stub list of every column the copies of its signed stub. Starting from
empty lists this yields exactly `signedCopies` of every column in increasing
row order, and reading the first two stubs gives the computed signed columns.
On signed words the copies are determined by the sign bit and the magnitude.
-/

@[expose] public section

namespace WeightedMIS.FaceColumnSemantics

open WeightedMIS.EmbeddingFaces WeightedMIS.Walks WeightedMIS.ColumnEncoding
open WeightedMIS.RegisterPotentialStep WeightedMIS.EfficientSearch

section Generic

variable {Row : Type*}

/-- The copies of one signed integer entry. -/
def copiesZ (i : Row) (z : ℤ) : List (Stub Row) := List.replicate z.natAbs (i, decide (0 ≤ z))

/-- Integer-level accumulation of column stub lists. -/
def colsZ (init : List (List (Stub Row))) : List Row → List (List ℤ) → List (List (Stub Row))
  | i :: is, z :: zs => List.zipWith (fun v acc => copiesZ i v ++ acc) z (colsZ init is zs)
  | _, _ => init

theorem zipWith_map_finRange {α β γ : Type*} {m : ℕ} (f : α → β → γ) (z : List α)
    (hz : z.length = m) (G : Fin m → β) :
    List.zipWith f z ((List.finRange m).map G) =
      (List.finRange m).map (fun e => f (z[e.val]'(by omega)) (G e)) := by
  apply List.ext_getElem
  · simp [hz]
  · intro n h1 h2
    simp

/-- The accumulated stub lists are the per-column flat maps over the rows. -/
theorem colsZ_eq {m : ℕ} (is : List Row) (zs : List (List ℤ)) (hlen : is.length = zs.length)
    (hrow : ∀ z ∈ zs, z.length = m) :
    colsZ (List.replicate m []) is zs =
      (List.finRange m).map (fun e => (is.zip zs).flatMap
        (fun iz => copiesZ iz.1 (iz.2.getD e.val 0))) := by
  induction is generalizing zs with
  | nil =>
    cases zs with
    | nil =>
      show List.replicate m [] = _
      apply List.ext_getElem <;> simp
    | cons z zs => simp at hlen
  | cons i is ih =>
    cases zs with
    | nil => simp at hlen
    | cons z zs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hz : z.length = m := hrow z List.mem_cons_self
      rw [colsZ, ih zs hlen (fun z' hz' => hrow z' (List.mem_cons_of_mem z hz')),
        zipWith_map_finRange _ z hz]
      apply List.map_congr_left
      intro e _
      simp only [List.zip_cons_cons, List.flatMap_cons]
      congr 2
      rw [List.getD_eq_getElem]

end Generic

theorem zip_map_flatMap {α β γ : Type*} (l : List α) (f : α → β) (g : α × β → List γ) :
    (l.zip (l.map f)).flatMap g = l.flatMap (fun a => g (a, f a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Stored integer rows give the signed copies of every column. -/
theorem colsZ_matrix {r m : ℕ} (M : Fin r → Fin m → ℤ) :
    colsZ (List.replicate m []) (List.finRange r)
        ((List.finRange r).map (fun i => (List.finRange m).map (fun e => M i e))) =
      (List.finRange m).map (fun e => signedCopies (List.finRange r) (fun i => M i e)) := by
  rw [colsZ_eq _ _ (by simp) (by intro z hz; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz; simp)]
  apply List.map_congr_left
  intro e _
  rw [zip_map_flatMap, signedCopies]
  apply List.flatMap_congr
  intro i _
  simp [copiesZ, List.getD_eq_getElem?_getD]

/-! ## Signed words -/

section Words

variable {Row : Type*} {b : ℕ}

/-- The copies of one stored signed word: magnitude many stubs of the opposite sign bit. -/
def stubsW (i : Row) (w : Word b) : List (Stub Row) := List.replicate w.2.value (i, !w.1)

theorem stubsW_eq (i : Row) (w : Word b) (z : ℤ) (hw : value w = z) : stubsW i w = copiesZ i z := by
  subst hw
  rcases w with ⟨s, a⟩
  unfold stubsW copiesZ
  rw [value_natAbs]
  by_cases ha : a.value = 0
  · simp [ha]
  · congr 2
    cases s
    · simp [value, BinaryRational.signed]
    · simp [value, BinaryRational.signed]; omega

/-- Word-level accumulation of column stub lists. -/
def colsW (init : List (List (Stub Row))) : List Row → List (List (Word b)) → List (List (Stub Row))
  | i :: is, row :: rows => List.zipWith (fun w acc => stubsW i w ++ acc) row (colsW init is rows)
  | _, _ => init

theorem colsW_eq (init : List (List (Stub Row))) (is : List Row) (rows : List (List (Word b)))
    (zs : List (List ℤ)) (hr : List.Forall₂ (List.Forall₂ (fun w z => value w = z)) rows zs) :
    colsW init is rows = colsZ init is zs := by
  induction hr generalizing is with
  | nil => cases is <;> rfl
  | @cons row z rows zs hrow _ ih =>
    cases is with
    | nil => rfl
    | cons i is =>
      simp only [colsW, colsZ, ih is]
      clear ih
      generalize colsZ init is zs = acc
      induction hrow generalizing acc with
      | nil => rfl
      | @cons w v ws vs hw _ ih2 =>
        cases acc with
        | nil => rfl
        | cons a acc => simp [List.zipWith_cons_cons, stubsW_eq i w v hw, ih2]

theorem forall₂_row_bound (row : List (Word b)) (z : List ℤ)
    (hr : List.Forall₂ (fun w z => value w = z) row z) :
    (∀ v ∈ z, v.natAbs ≤ 2) → ∀ w ∈ row, w.2.value ≤ 2 := by
  induction hr with
  | nil => simp
  | @cons w v ws vs hwv _ ih =>
    intro hz w' hw'
    rcases List.mem_cons.mp hw' with rfl | hw'
    · rw [← value_natAbs, hwv]; exact hz v List.mem_cons_self
    · exact ih (fun v' hv' => hz v' (List.mem_cons_of_mem v hv')) w' hw'

theorem forall₂_bound (rows : List (List (Word b))) (zs : List (List ℤ))
    (hr : List.Forall₂ (List.Forall₂ (fun w z => value w = z)) rows zs) :
    (∀ z ∈ zs, ∀ v ∈ z, v.natAbs ≤ 2) → ∀ row ∈ rows, ∀ w ∈ row, w.2.value ≤ 2 := by
  induction hr with
  | nil => simp
  | @cons row z rows zs hrow _ ih =>
    intro hz row' hrow'
    rcases List.mem_cons.mp hrow' with rfl | hrow'
    · exact forall₂_row_bound _ z hrow (hz z List.mem_cons_self)
    · exact ih (fun z' hz' => hz z' (List.mem_cons_of_mem z hz')) row' hrow'

end Words

/-! ## The computed columns -/

variable {V : Type*} {m : ℕ} {left right : Fin m → V} (R : Ribbon left right)

/-- Entries of the stored even-face matrix have absolute value at most two. -/
theorem storedEvenMatrix_bound : ∀ z ∈ R.storedEvenMatrix, ∀ v ∈ z, v.natAbs ≤ 2 := by
  intro z hz v hv
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hv
  have h := R.computedIntegerMatrix_column_bound (Flag.canonicalOrder m) Flag.mem_canonicalOrder e
  exact le_trans (Finset.single_le_sum (f := fun r => (R.computedIntegerMatrix
    (Flag.canonicalOrder m) r e).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) h

/-- Word rows denoting the stored matrix give exactly the computed columns. -/
theorem colsW_columns (rows : List (List (Word b)))
    (hr : List.Forall₂ (List.Forall₂ (fun w z => value w = z)) rows R.storedEvenMatrix) :
    (colsW (List.replicate m []) (List.finRange (R.evenRootIndices (Flag.canonicalOrder m)).length)
        rows).map fromStubs = (List.finRange m).map (R.computedColumn (Flag.canonicalOrder m)) := by
  have h := colsZ_matrix (R.computedIntegerMatrix (Flag.canonicalOrder m))
  rw [colsW_eq _ _ rows _ hr, Ribbon.storedEvenMatrix]
  erw [h]
  rw [List.map_map]
  rfl

end WeightedMIS.FaceColumnSemantics
