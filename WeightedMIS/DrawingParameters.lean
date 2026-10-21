module

public import WeightedMIS.DrawingRegions

/-!
# Parameters of connected subgraphs of arbitrary drawings

The ambient cellular decomposition is a geometric witness, and its extra cells
do not enter the odd-region parameter. Original complementary regions are
actual deleted-dual components. Their refinement under further deletion and
the actual capped-region cell correspondences prove both parameter bounds.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.CellularEmbedding

open Incidence
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    {left right : E → V} (M : CellularEmbedding left right F)
    (g h : E → Prop) [DecidablePred g] [DecidablePred h]
    (hne : Nonempty {e : E // h e})

/-- The per-component genus-plus-odd bound holds for an arbitrary retained
original drawing, including disconnected and noncellular drawings. The odd
parameter counts total boundary parity in each actual original region. -/
theorem drawing_parameter_mono (hsub : ∀ e, h e → g e)
    (hc : Connected left right)
    (hcH : Connected (Ribbon.activeLeft (left := left) (right := right) h)
      (Ribbon.activeRight h)) :
    (M.cappedDeletion h hne).eulerGenus ≤ M.eulerGenus ∧
      (M.cappedDeletion h hne).eulerGenus +
          Fintype.card {f // Odd ((M.cappedDeletion h hne).faces f).boundary.length} ≤
        M.eulerGenus + M.sides.oddRegionCount g := by
  classical
  let H := M.cappedDeletion h hne
  let P := M.sides
  let D := P.deletedDual h
  let caps := P.complementaryComponentCapEquiv h M.vertex_links M.vertex_present
    (P.dual_vertex_present M.face_nonempty)
  let boundary := SidePairing.retainedBoundary h (fun s => H.sides.face s.1 s.2)
  let face := fun s : E × Bool => P.originalFaceRegion g (P.face s.1 s.2)
  let region := P.regionRefinement g h hsub
  have hmeet : Function.Surjective (ComplementEuler.boundaryRegion caps) :=
    P.complementaryCap_regions_surjective h M.vertex_links M.vertex_present
      (P.dual_vertex_present M.face_nonempty) (M.dual_connected hc) hne
  have paired : ∀ e, boundary (e, false) = none ↔ boundary (e, true) = none := by
    intro e
    by_cases he : h e <;> simp [boundary, SidePairing.retainedBoundary, he]
  have deleted : ∀ e, boundary (e, false) = none →
      region (face (e, false)) = region (face (e, true)) := by
    intro e hb
    have he : ¬h e := by
      intro he
      simp [boundary, SidePairing.retainedBoundary, he] at hb
    exact P.deleted_same_region h e he
  have retained : ∀ s f, boundary s = some f →
      ComplementEuler.boundaryRegion caps f = region (face s) := by
    intro s f hs
    have he := SidePairing.retainedBoundary_keep h (fun s => H.sides.face s.1 s.2) hs
    have hf : H.sides.face ⟨s.1, he⟩ s.2 = f := by
      simpa only [boundary, SidePairing.retainedBoundary, dite_eq_left he, Option.some.injEq] using hs
    subst f
    change ComplementEuler.boundaryRegion caps
      ((P.toRibbon.activeRestrict h).sidePairing.face ⟨s.1, he⟩ s.2) = _
    rw [(P.toRibbon.activeRestrict h).sidePairing_face]
    exact P.complementaryCap_region h M.vertex_links M.vertex_present
      (P.dual_vertex_present M.face_nonempty) ⟨⟨s.1, he⟩, s.2, false⟩
  have gluing := ComplementEuler.gluing_identity M hc H hcH
    (fun q => D.cappedComponent (P.deletedDual_vertexLinks h) q)
    (Ribbon.retainedOmittedVertexPartition (left := left) (right := right) h)
    (P.retainedDeletedEdgePartition h) (P.originalFacePartition h) caps hmeet
  have result := RegionParity.genus_bookkeeping_from_sides face region boundary
    (ComplementEuler.boundaryRegion caps) paired deleted retained
    (ComplementEuler.boundary_fiber_pos (ComplementEuler.boundaryRegion caps) hmeet)
    M.eulerGenus H.eulerGenus (fun q => (D.cappedComponent (P.deletedDual_vertexLinks h) q).genus) gluing
  have positions (f) : {s : E × Bool // boundary s = some f} ≃ Fin (H.faces f).boundary.length := by
    apply (SidePairing.retainedBoundaryFiber h (fun s => H.sides.face s.1 s.2) f).trans
    apply Fintype.equivFinOfCardEq
    rw [Fintype.card_subtype]
    have hh := H.sides.face_fiber_size f
    unfold RegionParity.fiberSize at hh
    convert hh using 1
    congr 1
    ext s
    simp
  have lengths (f) : RegionParity.boundarySize boundary f = (H.faces f).boundary.length := by
    have he := Fintype.card_congr (positions f)
    rw [Fintype.card_subtype, Fintype.card_fin] at he
    unfold RegionParity.boundarySize RegionParity.fiberSize
    convert he using 1
    congr 1
    ext s
    simp
  rw [M.sides.oddRegionCount_eq g]
  simp only [lengths] at result
  convert result using 1 <;> simp only [Fintype.card_subtype]
  all_goals rfl

end WeightedMIS.EmbeddingFaces.CellularEmbedding
