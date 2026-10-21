module

public import WeightedMIS.DeletionParameters
public import WeightedMIS.EmbeddedReduction

/-!
# The search reduction on actual capped residual subgraphs

The dimension of the actual residual signature space is bounded by the
original embedding parameters. The actual search and weighted independent-set
recovery then apply to every connected nonbipartite all-half residual.
-/

@[expose] public section

namespace WeightedMIS.EmbeddedReduction

open EmbeddingFaces

attribute [local instance] Classical.propDecidable

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    {left right : E → V} (M : CellularEmbedding left right F)
    (keep : E → Prop) [DecidablePred keep] (hne : Nonempty {e : E // keep e})
    (hc : Incidence.Connected left right)
    (hcH : Incidence.Connected (Ribbon.activeLeft (left := left) (right := right) keep)
      (Ribbon.activeRight keep))
    (hnbH : ¬Incidence.Bipartite (Ribbon.activeLeft (left := left) (right := right) keep)
      (Ribbon.activeRight keep))

include hc hcH hnbH

/-- The actual capped residual dimension is controlled by the original genus
and original odd-facial-walk count. -/
theorem deleted_coordinateCount_le :
    coordinateCount (M.cappedDeletion keep hne) ≤ Parameters.exponent M.eulerGenus (oddFaceCount M) := by
  have hm := M.cappedDeletion_parameter_mono keep hne hc hcH
  exact Parameters.parameter_transfer M.eulerGenus (oddFaceCount M)
    (M.cappedDeletion keep hne).eulerGenus (oddFaceCount (M.cappedDeletion keep hne))
    (coordinateCount (M.cappedDeletion keep hne)) hm.1 hm.2
    (coordinateCount_even _ hcH hnbH) (fun hk => (coordinateCount_odd _ hcH hnbH hk).le)

/-- An original coherent orientation supplies the sharper residual dimension
bound through the constructed inherited orientation. -/
theorem deleted_coordinateCount_le_orientable (O : M.sides.Orientation) :
    coordinateCount (M.cappedDeletion keep hne) ≤
      Parameters.orientableExponent M.eulerGenus (oddFaceCount M) := by
  have hm := M.cappedDeletion_parameter_mono keep hne hc hcH
  have hd := coordinateCount_orientable (M.cappedDeletion keep hne)
    (M.cappedDeletionOrientation keep hne O) hcH hnbH
  exact Parameters.orientable_parameter_transfer M.eulerGenus (oddFaceCount M)
    (M.cappedDeletion keep hne).eulerGenus (oddFaceCount (M.cappedDeletion keep hne))
    (coordinateCount (M.cappedDeletion keep hne)) hm.2 hd.le

/-- The original parameter exponent controls the actual search recovery on a
connected nonbipartite all-half residual constructed by edge deletion. -/
theorem deleted_embedded_half_reduction
    (w : Ribbon.ActiveVertex (left := left) (right := right) keep → ℚ)
    (ho : Persistence.Optimal
      (EdgeTransport.Adj (Ribbon.activeLeft (left := left) (right := right) keep)
        (Ribbon.activeRight keep)) w (fun _ => 1 / 2)) :
    coordinateCount (M.cappedDeletion keep hne) ≤ Parameters.exponent M.eulerGenus (oddFaceCount M) ∧
      Recovery (M.cappedDeletion keep hne) w :=
  ⟨deleted_coordinateCount_le M keep hne hc hcH hnbH,
    exists_recovery _ hcH hnbH w ho⟩

/-- The same actual residual search satisfies the original orientable exponent. -/
theorem deleted_orientable_embedded_half_reduction (O : M.sides.Orientation)
    (w : Ribbon.ActiveVertex (left := left) (right := right) keep → ℚ)
    (ho : Persistence.Optimal
      (EdgeTransport.Adj (Ribbon.activeLeft (left := left) (right := right) keep)
        (Ribbon.activeRight keep)) w (fun _ => 1 / 2)) :
    coordinateCount (M.cappedDeletion keep hne) ≤
      Parameters.orientableExponent M.eulerGenus (oddFaceCount M) ∧
      Recovery (M.cappedDeletion keep hne) w :=
  ⟨deleted_coordinateCount_le_orientable M keep hne hc hcH hnbH O,
    exists_recovery _ hcH hnbH w ho⟩

end WeightedMIS.EmbeddedReduction
