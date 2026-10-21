module

public import WeightedMIS.RibbonFaces
public import WeightedMIS.RibbonLinks

/-!
# Constructing a cellular combinatorial embedding from a ribbon

The facial walks and their edge-side pairing are obtained by tracing. The
connected vertex links are transferred through the proved equality of corner
matchings. No facial incidence, rank, or Euler-genus conclusion is a field of
the input corner system.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.Ribbon

open SidePairing

variable {V E : Type*} [Fintype E] {left right : E → V} (R : Ribbon left right)

/-- The generated facial data have exactly the supplied connected vertex
links. -/
theorem sidePairing_vertexLinks (hlinks : R.VertexLinks) : R.sidePairing.VertexLinks := by
  intro x y hxy
  apply Relation.ReflTransGen.mono ?_ x y (hlinks x y hxy)
  intro a b hab
  cases hab with
  | across =>
      rcases a with ⟨e, s, t⟩
      exact SidePairing.LinkStep.across e s t
  | corner =>
      have h := R.sidePairing.linkStep_corner a
      rwa [R.sidePairing_corner] at h

/-- The concrete cellular map obtained from a nonempty ribbon with connected
vertex links and no unused vertex labels. -/
noncomputable def toCellularEmbedding (hlinks : R.VertexLinks)
    (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v) (hnonempty : Nonempty E) :
    CellularEmbedding left right R.FaceIndex where
  faces := R.faces
  sides := R.sidePairing
  face_present := by
    obtain ⟨e⟩ := hnonempty
    exact ⟨R.faceOf ⟨e, false, false⟩⟩
  face_nonempty := R.faces_positive
  vertex_present := hvertices
  vertex_links := R.sidePairing_vertexLinks hlinks

end WeightedMIS.EmbeddingFaces.Ribbon

namespace WeightedMIS.EmbeddingFaces.SidePairing

variable {V E F : Type*} {left right : E → V} {faces : F → Faces.Face left right}
    (P : SidePairing faces)

/-- Forget the chosen facial orientations while keeping every actual corner. -/
def toRibbon : Ribbon left right where
  corner := P.corner
  involutive := P.corner_corner
  ne_self := P.corner_ne_self
  vertex := P.corner_vertex

/-- The original local surface condition supplies the corresponding ribbon
condition without a new assumption. -/
theorem toRibbon_vertexLinks (hlinks : P.VertexLinks) : P.toRibbon.VertexLinks := by
  intro x y hxy
  apply Relation.ReflTransGen.mono ?_ x y (hlinks x y hxy)
  intro a b hab
  cases hab with
  | across e s t => exact .across _
  | corner d =>
      have h := Ribbon.LinkStep.corner (R := P.toRibbon) (P.endFlag d)
      change P.toRibbon.LinkStep (P.endFlag d) (P.corner (P.endFlag d)) at h
      rwa [P.corner_endFlag] at h
  | cornerRev d =>
      have h := Ribbon.LinkStep.corner (R := P.toRibbon) (P.startFlag (faceNext d))
      change P.toRibbon.LinkStep (P.startFlag (faceNext d)) (P.corner (P.startFlag (faceNext d))) at h
      simpa only [P.corner_startFlag, facePrev, Equiv.symm_apply_apply] using h

end WeightedMIS.EmbeddingFaces.SidePairing
