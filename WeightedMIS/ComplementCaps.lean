module

public import WeightedMIS.PureSmoothing
public import WeightedMIS.RibbonComponentFaces

/-!
# Actual cap correspondence for complementary edge restrictions

Exchanging primal side and endpoint coordinates identifies the common
smoothing of retained primal edges with that of deleted dual edges. The
resulting equivalence includes isolated dual vertex disks and removed primal
vertex disks, so every cap is represented by an actual boundary component.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open SidePairing

namespace Flag

variable {E : Type*} (keep : E → Prop) [DecidablePred keep]

/-- Complementing retained edges and exchanging side/endpoint coordinates
produces the same common-circle relabelling. -/
theorem deletionToggle_complement_swap (x : Flag E) :
    deletionToggle (fun e => ¬keep e) (swapSideEndpoint x) = deletionToggle keep x := by
  by_cases h : keep x.edge <;>
    simp [deletionToggle, swapSideEndpoint, h]

end Flag

namespace SidePairing

variable {V E F : Type*} [Fintype E] {left right : E → V}
    {faces : F → Faces.Face left right} (P : SidePairing faces)
    (keep : E → Prop) [DecidablePred keep]

/-- The primal and complementary dual common-circle corner matchings agree
pointwise after their actual local coordinate exchanges. -/
theorem complementary_smoothing_corner (x : Flag E) :
    (P.dualRibbon.sidePairing.smoothingRibbon (fun e => ¬keep e)).corner x =
      (P.toRibbon.sidePairing.smoothingRibbon keep).corner x := by
  simp only [smoothingRibbon, Equiv.trans_apply, Ribbon.sidePairing_corner,
    dualRibbon, dualCorner_apply, toRibbon]
  rw [Flag.deletionToggle_complement_swap]
  have h : Flag.swapSideEndpoint (Flag.deletionToggle (fun e => ¬keep e) x) =
      Flag.deletionToggle keep x := by
    by_cases hx : keep x.edge <;>
      simp [Flag.deletionToggle, Flag.swapSideEndpoint, hx]
  rw [h]

/-- The two common-circle ribbons are the same constructed permutation
system. Their vertex labels are deliberately just a single bookkeeping label. -/
theorem complementary_smoothing_eq :
    P.dualRibbon.sidePairing.smoothingRibbon (fun e => ¬keep e) =
      P.toRibbon.sidePairing.smoothingRibbon keep := by
  cases hd : P.dualRibbon.sidePairing.smoothingRibbon (fun e => ¬keep e) with
  | mk cd id nd vd =>
      cases hp : P.toRibbon.sidePairing.smoothingRibbon keep with
      | mk cp ip np vp =>
          have hc : cd = cp := by
            apply Equiv.ext
            intro x
            have h := P.complementary_smoothing_corner keep x
            rw [hd, hp] at h
            exact h
          subst cp
          rfl

/-- Relabelling the common circles between the complementary primal and dual
traces. -/
noncomputable def complementarySmoothingEquiv :
    (P.dualRibbon.sidePairing.smoothingRibbon (fun e => ¬keep e)).FaceIndex ≃
      (P.toRibbon.sidePairing.smoothingRibbon keep).FaceIndex :=
  Equiv.cast (congrArg Ribbon.FaceIndex (P.complementary_smoothing_eq keep))

/-- Common-circle relabelling keeps the actual flag naming the circle. -/
@[simp] theorem complementarySmoothingEquiv_faceOf (x : Flag E) :
    P.complementarySmoothingEquiv keep
      ((P.dualRibbon.sidePairing.smoothingRibbon (fun e => ¬keep e)).faceOf x) =
      (P.toRibbon.sidePairing.smoothingRibbon keep).faceOf x := by
  have hcast : ∀ (R S : Ribbon (fun _ : E => ()) (fun _ : E => ())) (h : R = S),
      Equiv.cast (congrArg Ribbon.FaceIndex h) (R.faceOf x) = S.faceOf x := by
    intro R S h
    cases h
    rfl
  exact hcast _ _ (P.complementary_smoothing_eq keep)

/-- Exchanging primal side and endpoint identifies the actual common circle
of an original flag with its complementary dual circle. -/
@[simp] theorem complementarySmoothingEquiv_commonFace (x : Flag E) :
    P.complementarySmoothingEquiv keep
      (P.dualRibbon.commonFace (fun e => ¬keep e) (Flag.swapSideEndpoint x)) =
      P.toRibbon.commonFace keep x := by
  rw [Ribbon.commonFace, P.complementarySmoothingEquiv_faceOf,
    Flag.deletionToggle_complement_swap]
  rfl

/-- The actual deleted-dual boundary circles and its isolated vertex disks
are exactly the retained-primal boundary circles and omitted vertex disks. -/
noncomputable def complementaryCapEquiv
    (hlinks : P.VertexLinks)
    (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v)
    (hfaces : ∀ f, ∃ x : Flag E, x.vertex (fun e => P.face e false) (fun e => P.face e true) = f) :
    (P.dualRibbon.restrict (fun e => ¬keep e)).FaceIndex ⊕
        Incidence.IsolatedVertex (fun e : {e : E // ¬keep e} => P.face e.val false)
          (fun e => P.face e.val true) ≃
      (P.toRibbon.restrict keep).FaceIndex ⊕
        Incidence.IsolatedVertex (fun e : {e : E // keep e} => left e.val) (fun e => right e.val) :=
  ((P.dualRibbon.commonFacePartition (fun e => ¬keep e) P.dual_vertexLinks hfaces).symm.trans
    (P.complementarySmoothingEquiv keep)).trans
      (P.toRibbon.commonFacePartition keep (P.toRibbon_vertexLinks hlinks) hvertices)

/-- Componentwise capping of the actual deleted dual ribbon gives the same
cap correspondence, including every edge-free complementary region. -/
noncomputable def complementaryComponentCapEquiv [Fintype F]
    (hlinks : P.VertexLinks)
    (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v)
    (hfaces : ∀ f, ∃ x : Flag E, x.vertex (fun e => P.face e false) (fun e => P.face e true) = f) :
    (Σ q : Incidence.Component (fun e : {e : E // ¬keep e} => P.face e.val false)
      (fun e => P.face e.val true), (P.dualRibbon.restrict (fun e => ¬keep e)).CappedFace q) ≃
      (P.toRibbon.restrict keep).FaceIndex ⊕
        Incidence.IsolatedVertex (fun e : {e : E // keep e} => left e.val) (fun e => right e.val) :=
  (P.dualRibbon.restrict (fun e => ¬keep e)).cappedFacePartition.trans
    (P.complementaryCapEquiv keep hlinks hvertices hfaces)

end SidePairing
end WeightedMIS.EmbeddingFaces
