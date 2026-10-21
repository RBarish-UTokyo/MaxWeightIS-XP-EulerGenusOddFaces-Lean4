module

public import WeightedMIS.DrawingParameters
public import WeightedMIS.EmbeddedReduction

/-!
# Embedded search parameters for arbitrary retained drawings

The witness cellular decomposition supplies the ambient surface genus. The
odd parameter is that of the actual drawing's complementary regions, not the
number of faces in the auxiliary decomposition.
-/

@[expose] public section

namespace WeightedMIS.EmbeddedReduction

open EmbeddingFaces

attribute [local instance] Classical.propDecidable

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    {left right : E → V} (M : CellularEmbedding left right F)
    (g h : E → Prop) [DecidablePred g] [DecidablePred h]
    (hne : Nonempty {e : E // h e}) (hsub : ∀ e, h e → g e)
    (hc : Incidence.Connected left right)
    (hcH : Incidence.Connected (Ribbon.activeLeft (left := left) (right := right) h)
      (Ribbon.activeRight h))
    (hnbH : ¬Incidence.Bipartite (Ribbon.activeLeft (left := left) (right := right) h)
      (Ribbon.activeRight h))

include hsub hc hcH hnbH

/-- Every hard connected subproblem obeys the original drawing's exponent. -/
theorem drawing_coordinateCount_le :
    coordinateCount (M.cappedDeletion h hne) ≤
      Parameters.exponent M.eulerGenus (M.sides.oddRegionCount g) := by
  have hm := M.drawing_parameter_mono g h hne hsub hc hcH
  exact Parameters.parameter_transfer M.eulerGenus (M.sides.oddRegionCount g)
    (M.cappedDeletion h hne).eulerGenus (oddFaceCount (M.cappedDeletion h hne))
    (coordinateCount (M.cappedDeletion h hne)) hm.1 hm.2
    (coordinateCount_even _ hcH hnbH) (fun hk => (coordinateCount_odd _ hcH hnbH hk).le)

/-- Coherent ambient orientation gives the sharper original-drawing exponent. -/
theorem drawing_coordinateCount_le_orientable (O : M.sides.Orientation) :
    coordinateCount (M.cappedDeletion h hne) ≤
      Parameters.orientableExponent M.eulerGenus (M.sides.oddRegionCount g) := by
  have hm := M.drawing_parameter_mono g h hne hsub hc hcH
  have hd := coordinateCount_orientable (M.cappedDeletion h hne)
    (M.cappedDeletionOrientation h hne O) hcH hnbH
  exact Parameters.orientable_parameter_transfer M.eulerGenus (M.sides.oddRegionCount g)
    (M.cappedDeletion h hne).eulerGenus (oddFaceCount (M.cappedDeletion h hne))
    (coordinateCount (M.cappedDeletion h hne)) hm.2 hd.le

end WeightedMIS.EmbeddedReduction
