module

public import WeightedMIS.ColumnEncoding

/-!
# Deterministic signed-stub column conversion

A supplied duplicate-free row list is scanned in its given order. This avoids
choosing an ordering of a finite type. The standard indexed version uses
`List.finRange` and can be applied directly to an explicitly stored matrix.
-/

@[expose] public section

namespace WeightedMIS.ComputedColumns

open ColumnEncoding Walks

/-- Concrete column conversion in the supplied row order. -/
def column {Row : Type*} (rows : List Row) (x : Row → ℤ) : Column Row :=
  fromStubs (signedCopies rows x)

theorem column_spec {Row : Type*} [Fintype Row] [DecidableEq Row]
    (rows : List Row) (hn : rows.Nodup) (hc : ∀ r, r ∈ rows)
    (x : Row → ℤ) (hx : (∑ r, (x r).natAbs) ≤ 2) (r : Row) :
    columnVector (column rows x) r = x r := by
  have hu : rows.toFinset = Finset.univ := by ext r; simp [hc]
  have hl : (signedCopies rows x).length ≤ 2 := by
    rw [signedCopies_length, ← List.sum_toFinset _ hn, hu]
    exact hx
  rw [column, fromStubs_vector _ hl, signedCopies_row_sum, ← List.sum_toFinset _ hn, hu]
  simp

/-- Finite indexed matrices have a canonical executable row order. -/
def indexedColumn {r : ℕ} (x : Fin r → ℤ) : Column (Fin r) := column (List.finRange r) x

theorem indexedColumn_spec {r : ℕ} (x : Fin r → ℤ)
    (hx : (∑ i, (x i).natAbs) ≤ 2) (i : Fin r) :
    columnVector (indexedColumn x) i = x i :=
  column_spec _ (List.nodup_finRange r) (fun j => List.mem_finRange j) x hx i

/-- The scan emits at most two stubs; multiplicity two is preserved exactly. -/
theorem emitted_length {r : ℕ} (x : Fin r → ℤ) (hx : (∑ i, (x i).natAbs) ≤ 2) :
    (signedCopies (List.finRange r) x).length ≤ 2 := by
  rw [signedCopies_length, ← List.sum_toFinset _ (List.nodup_finRange r)]
  simpa using hx

end WeightedMIS.ComputedColumns
