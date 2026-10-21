module

public import WeightedMIS.SparseKernel
public import WeightedMIS.DeterministicComplement
public import WeightedMIS.StoredElimination

/-!
# Computed nullspaces and bounded kernel complements

The rational generating family is obtained by the verified elimination routine
on the actual incidence matrix. Support elimination produces at most `m²`
bounded integral candidates. Deterministic span selection keeps exactly the
codimension many original candidates and preserves all coefficient bounds.
-/

@[expose] public section

namespace WeightedMIS.ComputedKernel

open Matrix RationalElimination

variable {n m : ℕ}

/-- Coordinatewise rational embedding of an integral row. -/
def rationalRow (z : Fin m → ℤ) : Fin m → ℚ := fun e => (z e : ℚ)

/-- Nullspace generators computed from the actual unsigned incidence matrix. -/
def rationalGenerators (left right : Fin m → Fin n) : List (Fin m → ℚ) :=
  RationalElimination.kernelGenerators (Incidence.unsigned left right)ᵀ

theorem rationalGenerators_length (left right : Fin m → Fin n) :
    (rationalGenerators left right).length = m :=
  RationalElimination.kernelGenerators_length _

theorem rationalGenerators_span (left right : Fin m → Fin n) :
    listSpan (rationalGenerators left right) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin :=
  RationalElimination.kernelGenerators_span _

/-- Actual incidence nullspace computation followed by support elimination
requires at most quadratically many bounded integral candidates. -/
theorem bounded_candidates (left right : Fin m → Fin n) :
    ∃ gs : List (Fin m → ℤ), gs.length ≤ m * m ∧
      (∀ g ∈ gs, KernelBasis.IntegralKernel left right g ∧ ∀ e, |g e| ≤ 2) ∧
      listSpan (gs.map rationalRow) =
        LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  let vs := rationalGenerators left right
  have hrange : Set.range vs.get = {x | x ∈ vs} := by
    ext x
    simp [List.mem_iff_get, eq_comm]
  have hspan : Submodule.span ℚ (Set.range vs.get) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
    rw [hrange]
    exact rationalGenerators_span left right
  obtain ⟨gs, hlen, hb, hgs⟩ := SparseKernel.sparse_spanning_family left right vs.get hspan
  refine ⟨gs, ?_, hb, ?_⟩
  · simpa [vs, rationalGenerators_length] using hlen
  · have hset : {x | x ∈ gs.map rationalRow} = SparseKernel.generators gs := by
      ext x
      constructor
      · intro hx
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
        exact ⟨g, hg, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact List.mem_map.mpr ⟨g, hg, rfl⟩
    rw [listSpan, hset]
    exact hgs

/-- Greedy complement selection retaining integral candidate rows verbatim. -/
def selectInteger (rows : List (Fin m → ℚ)) : List (Fin m → ℤ) → List (Fin m → ℤ)
  | [] => []
  | v :: vs =>
      if DeterministicComplement.outside rows (rationalRow v) then
        v :: selectInteger (rationalRow v :: rows) vs
      else selectInteger rows vs

theorem rational_selectInteger (rows : List (Fin m → ℚ)) (gs : List (Fin m → ℤ)) :
    (selectInteger rows gs).map rationalRow =
      DeterministicComplement.select rows (gs.map rationalRow) := by
  induction gs generalizing rows with
  | nil => rfl
  | cons v vs ih =>
      simp only [selectInteger, List.map_cons, DeterministicComplement.select]
      split <;> simp_all

theorem selectInteger_sublist (rows : List (Fin m → ℚ)) (gs : List (Fin m → ℤ)) :
    (selectInteger rows gs).Sublist gs := by
  induction gs generalizing rows with
  | nil => exact List.Sublist.refl _
  | cons v vs ih =>
      simp only [selectInteger]
      split
      · exact (ih (rationalRow v :: rows)).cons_cons v
      · exact (ih rows).cons v

/-- The bounded candidate family and its deterministically selected complement
for a connected nonbipartite graph and any actual kernel-row list. -/
theorem bounded_complement_selected (left right : Fin m → Fin n)
    (hconn : Incidence.Connected left right) (hnot : ¬ Incidence.Bipartite left right)
    (rows : List (Fin m → ℚ))
    (hrows : listSpan rows ≤ LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin) :
    ∃ gs : List (Fin m → ℤ), gs.length ≤ m * m ∧
      let W := selectInteger rows gs
      (∀ w ∈ W, KernelBasis.IntegralKernel left right w ∧ ∀ e, |w e| ≤ 2) ∧
      W.length = m - n - Module.finrank ℚ (listSpan rows) ∧
      listSpan rows ⊔ listSpan (W.map rationalRow) =
        LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  obtain ⟨gs, hlen, hb, hgs⟩ := bounded_candidates left right
  have hall : listSpan (rows ++ gs.map rationalRow) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
    rw [DeterministicComplement.listSpan_append, hgs, sup_eq_right.mpr hrows]
  have hlenW := DeterministicComplement.select_length rows (gs.map rationalRow)
  have hspanW := DeterministicComplement.select_span rows (gs.map rationalRow)
  rw [← rational_selectInteger, List.length_map, hall,
    Incidence.left_kernel_finrank left right hconn hnot] at hlenW
  rw [← rational_selectInteger, hall] at hspanW
  refine ⟨gs, hlen, ?_, by simpa using hlenW, hspanW⟩
  intro w hw
  exact hb w ((selectInteger_sublist rows gs).subset hw)

end WeightedMIS.ComputedKernel
