module

public import WeightedMIS.CapRegions
public import WeightedMIS.RibbonOrientation

/-!
# Genus and odd-face bounds for actual capped edge deletion

The retained embedding is constructed from the original corner permutation.
The complementary dual components, all four cell partitions, cap correspondence,
and side incidence are constructed and checked. The resulting genus and
odd-facial-walk bounds use no rank, parity, or Euler gluing assumptions.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open SidePairing Incidence

attribute [local instance] Classical.propDecidable

namespace SidePairing

variable {E B : Type*} (keep : E → Prop) [DecidablePred keep]
    (face : {e : E // keep e} × Bool → B)

/-- Retained sides carry their actual boundary label; deleted sides have none. -/
def retainedBoundary (s : E × Bool) : Option B :=
  if he : keep s.1 then some (face (⟨s.1, he⟩, s.2)) else none

theorem retainedBoundary_keep {s : E × Bool} {b : B}
    (h : retainedBoundary keep face s = some b) : keep s.1 := by
  by_contra hn
  simp [retainedBoundary, hn] at h

/-- Forgetting a retained edge's subtype proof bijects its actual boundary fibers. -/
def retainedBoundaryFiber (b : B) :
    {s : E × Bool // retainedBoundary keep face s = some b} ≃
      {s : {e : E // keep e} × Bool // face s = b} where
  toFun s := ⟨(⟨s.val.1, retainedBoundary_keep keep face s.property⟩, s.val.2), by
    have h := s.property
    simpa only [retainedBoundary, dite_eq_left (retainedBoundary_keep keep face s.property),
      Option.some.injEq] using h⟩
  invFun s := ⟨(s.val.1.val, s.val.2), by
    simp only [retainedBoundary, dite_eq_left s.val.1.property]
    exact congrArg some s.property⟩
  left_inv := by intro s; apply Subtype.ext; rfl
  right_inv := by intro s; apply Subtype.ext; rfl

end SidePairing

namespace CellularEmbedding

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    {left right : E → V} (M : CellularEmbedding left right F)
    (keep : E → Prop) [DecidablePred keep]
    (hne : Nonempty {e : E // keep e})

/-- The actual capped cellular map on the vertices incident to retained edges. -/
noncomputable def cappedDeletion :
    CellularEmbedding (Ribbon.activeLeft (left := left) (right := right) keep)
      (Ribbon.activeRight keep) (M.sides.toRibbon.activeRestrict keep).FaceIndex :=
  M.sides.toRibbon.cappedRestriction keep (M.sides.toRibbon_vertexLinks M.vertex_links) hne

/-- A coherent original orientation is inherited by the actually constructed
capped map, not assumed as an additional residual condition. -/
noncomputable def cappedDeletionOrientation (O : M.sides.Orientation) :
    (M.cappedDeletion keep hne).sides.Orientation :=
  O.toFlagOrientation.cappedRestriction keep (M.sides.toRibbon_vertexLinks M.vertex_links) hne

/-- Capping a connected retained edge subgraph cannot increase Euler genus;
any increase in odd facial walks is paid for by the genus lost. -/
theorem cappedDeletion_parameter_mono
    (hc : Connected left right)
    (hcH : Connected (Ribbon.activeLeft (left := left) (right := right) keep)
      (Ribbon.activeRight keep)) :
    (M.cappedDeletion keep hne).eulerGenus ≤ M.eulerGenus ∧
      (M.cappedDeletion keep hne).eulerGenus +
          Fintype.card {f // Odd ((M.cappedDeletion keep hne).faces f).boundary.length} ≤
        M.eulerGenus + Fintype.card {f // Odd (M.faces f).boundary.length} := by
  classical
  let H := M.cappedDeletion keep hne
  let P := M.sides
  let D := P.deletedDual keep
  let caps := P.complementaryComponentCapEquiv keep M.vertex_links M.vertex_present
    (P.dual_vertex_present M.face_nonempty)
  let boundary := SidePairing.retainedBoundary keep (fun s => H.sides.face s.1 s.2)
  have hmeet : Function.Surjective (ComplementEuler.boundaryRegion caps) :=
    P.complementaryCap_regions_surjective keep M.vertex_links M.vertex_present
      (P.dual_vertex_present M.face_nonempty) (M.dual_connected hc) hne
  have paired : ∀ e, boundary (e, false) = none ↔ boundary (e, true) = none := by
    intro e
    by_cases he : keep e <;> simp [boundary, SidePairing.retainedBoundary, he]
  have deleted : ∀ e, boundary (e, false) = none →
      (P.originalFacePartition keep (P.face e false)).1 =
        (P.originalFacePartition keep (P.face e true)).1 := by
    intro e hb
    have he : ¬keep e := by
      intro he
      simp [boundary, SidePairing.retainedBoundary, he] at hb
    exact P.deleted_same_region keep e he
  have retained : ∀ s f, boundary s = some f →
      ComplementEuler.boundaryRegion caps f =
        (P.originalFacePartition keep (P.face s.1 s.2)).1 := by
    intro s f hs
    have he := SidePairing.retainedBoundary_keep keep (fun s => H.sides.face s.1 s.2) hs
    have hf : H.sides.face ⟨s.1, he⟩ s.2 = f := by
      simpa only [boundary, SidePairing.retainedBoundary, dite_eq_left he, Option.some.injEq] using hs
    subst f
    change ComplementEuler.boundaryRegion caps
      ((P.toRibbon.activeRestrict keep).sidePairing.face ⟨s.1, he⟩ s.2) = _
    rw [(P.toRibbon.activeRestrict keep).sidePairing_face]
    exact P.complementaryCap_region keep M.vertex_links M.vertex_present
      (P.dual_vertex_present M.face_nonempty) ⟨⟨s.1, he⟩, s.2, false⟩
  have positions : ∀ f, {s : E × Bool // boundary s = some f} ≃ Fin (H.faces f).boundary.length := by
    intro f
    apply (SidePairing.retainedBoundaryFiber keep (fun s => H.sides.face s.1 s.2) f).trans
    apply Fintype.equivFinOfCardEq
    rw [Fintype.card_subtype]
    have h := H.sides.face_fiber_size f
    unfold RegionParity.fiberSize at h
    convert h using 1
    congr 1
    ext s
    simp
  exact ComplementEuler.parameter_mono_from_cells M hc H hcH
    (fun q => D.cappedComponent (P.deletedDual_vertexLinks keep) q)
    (Ribbon.retainedOmittedVertexPartition (left := left) (right := right) keep)
    (P.retainedDeletedEdgePartition keep) (P.originalFacePartition keep) caps hmeet
    boundary paired deleted retained positions

end CellularEmbedding
end WeightedMIS.EmbeddingFaces
