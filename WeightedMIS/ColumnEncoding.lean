module

public import WeightedMIS.Walks

/-!
# From short integer columns to signed stubs

An integer column with sum of absolute values at most two is converted to the
concrete zero-, one-, or two-stub representation. Multiplicity is preserved;
coefficients +2 and -2 produce two stubs in the same row.
-/

@[expose] public section

namespace WeightedMIS.ColumnEncoding

open WeightedMIS.Walks

/-- Emit one signed stub per unit of absolute value, in a supplied row order. -/
def signedCopies {Row : Type*} (rows : List Row) (x : Row → ℤ) : List (Stub Row) :=
  rows.flatMap (fun r => List.replicate (x r).natAbs (r, decide (0 ≤ x r)))

/-- Read the first two stubs. Under the proved length bound this reads the
entire list, including zero and one-stub cases. -/
def fromStubs {Row : Type*} : List (Stub Row) → Column Row
  | [] => .zero
  | [a] => .one a
  | a :: b :: _ => .two a b

theorem sign_natAbs (z : ℤ) : (z.natAbs : ℤ) * signValue (decide (0 ≤ z)) = z := by
  by_cases h : 0 ≤ z
  · simp [signValue, h, abs_of_nonneg h]
  · have hn : z < 0 := by omega
    simp [signValue, h, abs_of_neg hn]

theorem signedCopies_length {Row : Type*} (rows : List Row) (x : Row → ℤ) :
    (signedCopies rows x).length = (rows.map (fun r => (x r).natAbs)).sum := by
  simp [signedCopies, List.length_flatMap]

theorem copies_row_sum {Row : Type*} [DecidableEq Row] (x : Row → ℤ) (a r : Row) :
    ((List.replicate (x a).natAbs (a, decide (0 ≤ x a))).map
      (fun s => potential (some s) r)).sum = if r = a then x a else 0 := by
  by_cases h : r = a
  · subst r
    simp only [List.map_replicate, List.sum_replicate, potential, nsmul_eq_mul]
    exact sign_natAbs (x a)
  · simp [potential, h]

theorem signedCopies_row_sum {Row : Type*} [DecidableEq Row]
    (rows : List Row) (x : Row → ℤ) (r : Row) :
    ((signedCopies rows x).map (fun s => potential (some s) r)).sum =
      (rows.map (fun a => if r = a then x a else 0)).sum := by
  induction rows with
  | nil => simp [signedCopies]
  | cons a rows ih =>
      simp only [signedCopies, List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons] at ih ⊢
      rw [copies_row_sum, ih]

theorem fromStubs_vector {Row : Type*} [DecidableEq Row] (l : List (Stub Row))
    (hlen : l.length ≤ 2) (r : Row) :
    columnVector (fromStubs l) r = (l.map (fun s => potential (some s) r)).sum := by
  cases l with
  | nil => simp [fromStubs, columnVector]
  | cons a l =>
      cases l with
      | nil => simp [fromStubs, columnVector]
      | cons b l =>
          cases l with
          | nil => simp [fromStubs, columnVector]
          | cons c l => simp only [List.length_cons] at hlen; omega

/-- The complete row enumeration yields the intended integer column. -/
noncomputable def columnOfVector {Row : Type*} [Fintype Row] (x : Row → ℤ) : Column Row :=
  fromStubs (signedCopies Finset.univ.toList x)

/-- Exact matrix-to-stub conversion for every integer column of ℓ₁-norm ≤2. -/
theorem columnOfVector_spec {Row : Type*} [Fintype Row] [DecidableEq Row]
    (x : Row → ℤ) (hx : (∑ r, (x r).natAbs) ≤ 2) (r : Row) :
    columnVector (columnOfVector x) r = x r := by
  have hlen : (signedCopies Finset.univ.toList x).length ≤ 2 := by
    rw [signedCopies_length, ← List.sum_toFinset _ (Finset.nodup_toList _)]
    simpa using hx
  rw [columnOfVector, fromStubs_vector _ hlen, signedCopies_row_sum,
    ← List.sum_toFinset _ (Finset.nodup_toList _)]
  simp

/-- Matrix-wide bridge, preserving every integer coefficient exactly. -/
theorem exists_columns {Row Edge : Type*} [Fintype Row] [DecidableEq Row]
    (B : Row → Edge → ℤ) (hB : ∀ e, (∑ r, (B r e).natAbs) ≤ 2) :
    ∃ C : Edge → Column Row, ∀ e r, columnVector (C e) r = B r e := by
  exact ⟨fun e => columnOfVector (fun r => B r e),
    fun e r => columnOfVector_spec (fun r => B r e) (hB e) r⟩

end WeightedMIS.ColumnEncoding
