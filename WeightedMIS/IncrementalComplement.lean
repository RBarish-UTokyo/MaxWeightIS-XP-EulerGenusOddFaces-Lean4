module

public import WeightedMIS.RationalWordRows

/-!
# Incremental complement selection

`ComputedKernel.selectInteger` recomputes the annihilator of the current row
list for every candidate. The incremental form keeps one annihilator list `A`
whose span is the orthogonal complement of the current row span. A candidate
`v` is accepted exactly when some member of `A` has nonzero dot product with
`v`, which is the pivot search of `RationalElimination.cut`; on acceptance
the list is updated by that cut. Both selections agree whenever the initial
list has the right span, in particular for the elimination of the initial
rows from the coordinate vectors.

After accepting the candidates `acc` (in input order) the annihilator list is
literally `eliminateRows ((ints ++ acc).map rowFunctional) (coordinateVectors m)`,
so the determinant bound `EliminationCertificate.eliminateRows_coordinate_size`
bounds all intermediate coordinates. The word-level selection `selectW`
refines the incremental selection under one explicit width inequality.
-/

@[expose] public section

namespace WeightedMIS.IncrementalComplement

open Matrix RationalElimination DeterministicComplement ComputedKernel RationalWordRows
open BinaryRational RationalWidth

variable {m : ℕ}

/-! ## Rational incremental selection -/

/-- The pivot test of `cut`: some stored vector has nonzero dot product. -/
def admits (A : List (Fin m → ℚ)) (x : Fin m → ℚ) : Bool :=
  (A.find? fun y => decide (rowMap x y ≠ 0)).isSome

/-- Scan integral candidates, keeping an annihilator list instead of the rows. -/
def selectInc : List (Fin m → ℚ) → List (Fin m → ℤ) → List (Fin m → ℤ)
  | _, [] => []
  | A, v :: vs =>
      if admits A (rationalRow v) then v :: selectInc (cut (rowMap (rationalRow v)) A) vs
      else selectInc A vs

theorem mem_listSpan_iff_of_span {A rows : List (Fin m → ℚ)}
    (hA : listSpan A = dotForm.orthogonal (listSpan rows)) (x : Fin m → ℚ) :
    x ∈ listSpan rows ↔ ∀ y ∈ A, dotProduct x y = 0 := by
  have hdouble := LinearMap.BilinForm.orthogonal_orthogonal
    dotForm_nondegenerate dotForm_refl (listSpan rows)
  rw [← hdouble, ← hA, orthogonal_listSpan, mem_constraintKernel]
  constructor
  · intro h y hy
    have hz := h (rowMap y) (List.mem_map.mpr ⟨y, hy, rfl⟩)
    simpa only [rowMap_apply, dotProduct_comm] using hz
  · intro h c hc
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
    simpa only [rowMap_apply, dotProduct_comm] using h y hy

theorem admits_eq_outside {A rows : List (Fin m → ℚ)}
    (hA : listSpan A = dotForm.orthogonal (listSpan rows)) (x : Fin m → ℚ) :
    admits A x = outside rows x := by
  apply Bool.eq_iff_iff.mpr
  rw [outside_iff, mem_listSpan_iff_of_span hA, admits, List.find?_isSome]
  simp only [rowMap_apply, not_forall, exists_prop]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, of_decide_eq_true h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, decide_eq_true h⟩

theorem span_cut {A rows : List (Fin m → ℚ)}
    (hA : listSpan A = dotForm.orthogonal (listSpan rows)) (x : Fin m → ℚ) :
    listSpan (cut (rowMap x) A) = dotForm.orthogonal (listSpan (x :: rows)) := by
  rw [listSpan_cut, hA, orthogonal_listSpan, orthogonal_listSpan, List.map_cons,
    constraintKernel, inf_comm]

/-- The incremental and the recomputing selections agree. -/
theorem selectInc_eq (A rows : List (Fin m → ℚ))
    (hA : listSpan A = dotForm.orthogonal (listSpan rows)) (cands : List (Fin m → ℤ)) :
    selectInc A cands = selectInteger rows cands := by
  induction cands generalizing A rows with
  | nil => rfl
  | cons v vs ih =>
      simp only [selectInc, selectInteger, admits_eq_outside hA]
      split
      · rw [ih _ _ (span_cut hA _)]
      · exact ih A rows hA

/-- The elimination of the rows from the coordinate vectors spans the annihilator. -/
theorem initial_span (rows : List (Fin m → ℚ)) :
    listSpan (eliminateRows (rows.map rowMap) (coordinateVectors m)) =
      dotForm.orthogonal (listSpan rows) := by
  rw [← annihilatorGenerators_eq]
  exact annihilatorGenerators_span rows

theorem selectInteger_eq_inc (rows : List (Fin m → ℚ)) (cands : List (Fin m → ℤ)) :
    selectInteger rows cands =
      selectInc (eliminateRows (rows.map rowMap) (coordinateVectors m)) cands :=
  (selectInc_eq _ rows (initial_span rows) cands).symm

theorem complement_eq_inc {n : ℕ} (left right : Fin m → Fin n) (rows : List (Fin m → ℚ)) :
    DeterministicKernel.complement left right rows =
      selectInc (eliminateRows (rows.map rowMap) (coordinateVectors m))
        (DeterministicKernel.candidates left right) :=
  selectInteger_eq_inc rows _

/-! ## Annihilators of integer row lists -/

/-- The annihilator list after processing the integer rows `ints ++ acc`. -/
def annihilator (ints acc : List (Fin m → ℤ)) : List (Fin m → ℚ) :=
  eliminateRows ((ints ++ acc).map rowFunctional) (coordinateVectors m)

theorem rowFunctional_eq (r : Fin m → ℤ) : rowFunctional r = rowMap (rationalRow r) := rfl

theorem map_rowFunctional (rs : List (Fin m → ℤ)) :
    rs.map rowFunctional = (rs.map rationalRow).map rowMap := by
  simp only [List.map_map]
  rfl

theorem annihilator_nil (ints : List (Fin m → ℤ)) :
    annihilator ints [] = eliminateRows ((ints.map rationalRow).map rowMap) (coordinateVectors m) := by
  rw [annihilator, List.append_nil, map_rowFunctional]

theorem annihilator_snoc (ints acc : List (Fin m → ℤ)) (v : Fin m → ℤ) :
    cut (rowMap (rationalRow v)) (annihilator ints acc) = annihilator ints (acc ++ [v]) := by
  simp only [annihilator, List.map_append, eliminateRows_append, List.map_cons, List.map_nil]
  rfl

/-- Accepted candidates never outnumber the dimension. -/
theorem selectInc_length_le (ints : List (Fin m → ℤ)) (cands : List (Fin m → ℤ)) :
    (selectInc (annihilator ints []) cands).length ≤ m := by
  rw [annihilator_nil, ← selectInteger_eq_inc]
  have h := select_length_add_finrank (ints.map rationalRow) (cands.map rationalRow)
  rw [← rational_selectInteger, List.length_map] at h
  have hle := Submodule.finrank_le (listSpan ((ints.map rationalRow) ++ cands.map rationalRow))
  rw [Module.finrank_fin_fun] at hle
  omega

/-! ## Word-level selection -/

variable {N : ℕ}

/-- Word-level incremental selection: pivot search, and the cut on acceptance. -/
def selectW (zero : Word N) : List (List (Word N)) → List (List (Word N)) →
    List (List (Word N))
  | _, [] => []
  | A, c :: cs =>
      if (A.find? (nonzeroW zero c)).isSome then c :: selectW zero (cutW zero c A) cs
      else selectW zero A cs

/-- Uniform working width for rows and candidates with entries of magnitude at most two. -/
def selectWidth (L m : ℕ) : ℕ := projectWidth 2 (elimWidth (L + m) m 1) m

theorem annihilator_fits (ints acc : List (Fin m → ℤ))
    (hints : ∀ r ∈ ints, ∀ j, (r j).natAbs ≤ 2) (hacc : ∀ r ∈ acc, ∀ j, (r j).natAbs ≤ 2)
    (hlen : acc.length ≤ m) :
    ∀ w ∈ annihilator ints acc, ∀ j, Fits (w j) (elimWidth (ints.length + m) m 1) := by
  intro w hw j
  have hb : ∀ r ∈ ints ++ acc, ∀ j, (r j).natAbs ≤ 2 ^ 1 := by
    intro r hr j
    rcases List.mem_append.mp hr with hr | hr
    · simpa using hints r hr j
    · simpa using hacc r hr j
  have h := EliminationCertificate.eliminateRows_coordinate_size (ints ++ acc) 1 hb w hw j
  have hl : (ints ++ acc).length ≤ ints.length + m := by simp; omega
  have hmul := Nat.mul_le_mul_right m
    (Nat.add_le_add_right (Nat.add_le_add_right hl m) (2 * 1))
  unfold elimWidth
  constructor <;> omega

theorem rationalRow_fits (v : Fin m → ℤ) (hv : ∀ j, (v j).natAbs ≤ 2) (j : Fin m) :
    Fits (rationalRow v j) 2 :=
  fits_int (v j) 1 (by simpa using hv j)

theorem selectW_prefix (ints : List (Fin m → ℤ)) (hints : ∀ r ∈ ints, ∀ j, (r j).natAbs ≤ 2)
    (zero : Word N) (hz : Rep zero 0) (hN : selectWidth ints.length m ≤ N) :
    ∀ (cands : List (Fin m → ℤ)), (∀ g ∈ cands, ∀ j, (g j).natAbs ≤ 2) →
    ∀ (cw : List (List (Word N))), List.Forall₂ RowRep cw (cands.map rationalRow) →
    ∀ (acc : List (Fin m → ℤ)), (∀ r ∈ acc, ∀ j, (r j).natAbs ≤ 2) →
    acc.length + (selectInc (annihilator ints acc) cands).length ≤ m →
    ∀ (aw : List (List (Word N))), List.Forall₂ RowRep aw (annihilator ints acc) →
      List.Forall₂ RowRep (selectW zero aw cw)
        ((selectInc (annihilator ints acc) cands).map rationalRow) := by
  intro cands
  induction cands with
  | nil =>
    intro _ cw hcw _ _ _ aw _
    cases hcw
    exact .nil
  | cons v vs ih =>
    intro hc cw hcw acc hacc hlen aw haw
    cases hcw with
    | @cons c x cs _ hcv hcs =>
    have hvb := hc v List.mem_cons_self
    have hvs : ∀ g ∈ vs, ∀ j, (g j).natAbs ≤ 2 := fun g hg => hc g (List.mem_cons_of_mem v hg)
    have hacclen : acc.length ≤ m := by
      have : acc.length ≤ acc.length + (selectInc (annihilator ints acc) (v :: vs)).length :=
        Nat.le_add_right _ _
      omega
    have hfits := annihilator_fits ints acc hints hacc hacclen
    have hpw : projectWidth 2 (elimWidth (ints.length + m) m 1) m ≤ N := hN
    have hdotN : (2 + elimWidth (ints.length + m) m 1 + 1) * (m + 1) + 2 ≤ N := by
      unfold projectWidth at hpw; omega
    -- the word test agrees with the rational pivot test
    have htest : (aw.find? (nonzeroW zero c)).isSome = admits (annihilator ints acc) (rationalRow v) := by
      have hrel := find?_rel haw (nonzeroW zero c) (fun w => decide (rowMap (rationalRow v) w ≠ 0))
        (fun a w _ hw hr => nonzeroW_eq zero hz hcv hr 2 _ (rationalRow_fits v hvb)
          (hfits w hw) hdotN)
      unfold admits
      rcases h1 : aw.find? (nonzeroW zero c) with _ | a <;>
        rcases h2 : (annihilator ints acc).find? (fun w => decide (rowMap (rationalRow v) w ≠ 0))
          with _ | y <;> rw [h1, h2] at hrel <;> cases hrel <;> rfl
    by_cases hadm : admits (annihilator ints acc) (rationalRow v) = true
    · have hsel : selectInc (annihilator ints acc) (v :: vs) =
          v :: selectInc (annihilator ints (acc ++ [v])) vs := by
        simp only [selectInc, hadm, ↓reduceIte, annihilator_snoc]
      have hw : selectW zero aw (c :: cs) = c :: selectW zero (cutW zero c aw) cs := by
        simp only [selectW, htest, hadm, ↓reduceIte]
      rw [hsel, hw, List.map_cons]
      refine .cons hcv (ih hvs cs hcs (acc ++ [v]) ?_ ?_ _ ?_)
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hacc r hr
        · rw [List.mem_singleton.mp hr]; exact hvb
      · rw [hsel] at hlen
        simp only [List.length_cons, List.length_append, List.length_nil] at hlen ⊢
        omega
      · rw [← annihilator_snoc]
        exact cutW_correct zero hz hcv 2 _ (rationalRow_fits v hvb) haw hfits hpw
    · have hadm' : admits (annihilator ints acc) (rationalRow v) = false := by simpa using hadm
      have hsel : selectInc (annihilator ints acc) (v :: vs) =
          selectInc (annihilator ints acc) vs := by
        simp only [selectInc, hadm', Bool.false_eq_true, ↓reduceIte]
      have hw : selectW zero aw (c :: cs) = selectW zero aw cs := by
        rw [selectW, htest, hadm']
        rfl
      rw [hsel, hw]
      exact ih hvs cs hcs acc hacc (by rw [hsel] at hlen; exact hlen) aw haw

/-- The word-level selection, started from the word-level elimination of the
integer rows, computes `selectInteger` on the rational rows exactly. -/
theorem selectW_correct (ints : List (Fin m → ℤ)) (hints : ∀ r ∈ ints, ∀ j, (r j).natAbs ≤ 2)
    (cands : List (Fin m → ℤ)) (hc : ∀ g ∈ cands, ∀ j, (g j).natAbs ≤ 2)
    (zero : Word N) (hz : Rep zero 0) (hN : selectWidth ints.length m ≤ N)
    (cw : List (List (Word N))) (hcw : List.Forall₂ RowRep cw (cands.map rationalRow))
    (aw : List (List (Word N)))
    (haw : List.Forall₂ RowRep aw
      (eliminateRows ((ints.map rationalRow).map rowMap) (coordinateVectors m))) :
    List.Forall₂ RowRep (selectW zero aw cw)
      ((selectInteger (ints.map rationalRow) cands).map rationalRow) := by
  rw [selectInteger_eq_inc, ← annihilator_nil]
  rw [← annihilator_nil] at haw
  exact selectW_prefix ints hints zero hz hN cands hc cw hcw [] (by simp)
    (by simpa using selectInc_length_le ints cands) aw haw

/-- The initial annihilator words: elimination of the rows from the coordinate vectors. -/
theorem initialW_correct (ints : List (Fin m → ℤ)) (hints : ∀ r ∈ ints, ∀ j, (r j).natAbs ≤ 2)
    (zero one : Word N) (hz : Rep zero 0) (ho : Rep one 1)
    (hN : selectWidth ints.length m ≤ N)
    (rw : List (List (Word N))) (hrw : List.Forall₂ RowRep rw (ints.map rationalRow)) :
    List.Forall₂ RowRep (eliminateRowsW zero rw (coordinateVectorsW zero one m))
      (eliminateRows ((ints.map rationalRow).map rowMap) (coordinateVectors m)) := by
  rw [← map_rowFunctional]
  refine eliminateRowsW_correct ints 1 (fun r hr j => by simpa using hints r hr j) zero one
    hz ho ?_ rw hrw
  refine le_trans ?_ hN
  unfold selectWidth projectWidth elimWidth
  have h : (ints.length + m + 2 * 1) * m ≤ (ints.length + m + m + 2 * 1) * m :=
    Nat.mul_le_mul_right m (by omega)
  have h2 : (1 + 1 + ((ints.length + m + 2 * 1) * m + m ^ 2 + 1) + 1) * (m + 1) ≤
      (2 + ((ints.length + m + m + 2 * 1) * m + m ^ 2 + 1) + 1) * (m + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : (1 + 1 + ((ints.length + m + 2 * 1) * m + m ^ 2 + 1) + 1) * m ≤
      (2 + ((ints.length + m + m + 2 * 1) * m + m ^ 2 + 1) + 1) * m :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- The selection from integer face rows is the deterministic kernel complement. -/
theorem selectW_complement {n : ℕ} (left right : Fin m → Fin n)
    (ints : List (Fin m → ℤ)) (hints : ∀ r ∈ ints, ∀ j, (r j).natAbs ≤ 2)
    (zero one : Word N) (hz : Rep zero 0) (ho : Rep one 1)
    (hN : selectWidth ints.length m ≤ N)
    (rw : List (List (Word N))) (hrw : List.Forall₂ RowRep rw (ints.map rationalRow))
    (cw : List (List (Word N)))
    (hcw : List.Forall₂ RowRep cw ((DeterministicKernel.candidates left right).map rationalRow)) :
    List.Forall₂ RowRep
      (selectW zero (eliminateRowsW zero rw (coordinateVectorsW zero one m)) cw)
      ((DeterministicKernel.complement left right (ints.map rationalRow)).map rationalRow) :=
  selectW_correct ints hints _ (fun g hg j => by
      have h := ((DeterministicKernel.candidates_spec left right).2.1 g hg).2 j
      rw [Int.abs_eq_natAbs] at h
      omega)
    zero hz hN cw hcw _ (initialW_correct ints hints zero one hz ho hN rw hrw)

/-- The selection width is cubic. -/
theorem selectWidth_le (L m : ℕ) : selectWidth L m ≤ 64 * (L + m + 3) ^ 3 := by
  unfold selectWidth projectWidth elimWidth
  set s := L + m + 3 with hs
  have hm : m ≤ s := by omega
  have h1 : (L + m + m + 2 * 1) * m ≤ 2 * (s * s) := by
    have : L + m + m + 2 * 1 ≤ 2 * s := by omega
    calc _ ≤ (2 * s) * s := Nat.mul_le_mul this hm
      _ = 2 * (s * s) := by ring
  have h2 : m ^ 2 ≤ s * s := by rw [pow_two]; exact Nat.mul_le_mul hm hm
  have h9 : 9 ≤ s * s := Nat.mul_le_mul (show 3 ≤ s by omega) (show 3 ≤ s by omega)
  have hA : 2 + ((L + m + m + 2 * 1) * m + m ^ 2 + 1) + 1 ≤ 4 * (s * s) := by omega
  have hB : (2 + ((L + m + m + 2 * 1) * m + m ^ 2 + 1) + 1) * (m + 1) ≤ 4 * (s * s) * s :=
    Nat.mul_le_mul hA (by omega)
  have hC : (2 + ((L + m + m + 2 * 1) * m + m ^ 2 + 1) + 1) * m ≤ 4 * (s * s) * s :=
    Nat.mul_le_mul hA hm
  have hs3 : s ^ 3 = s * s * s := by ring
  have hss : s * s ≤ s * s * s := Nat.le_mul_of_pos_right _ (by omega)
  rw [hs3]
  nlinarith

end WeightedMIS.IncrementalComplement
