module

public import WeightedMIS.ComplementCaps
public import WeightedMIS.RibbonComponentEuler
public import WeightedMIS.ComponentBoundary

/-!
# Incident regions of the actual complementary cap circles

The component label of a capped deleted-dual circle is recovered from any
actual flag on that circle. This identifies the regions used in parity and
Euler counting with those constructed by edge deletion.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open SidePairing Incidence

attribute [local instance] Classical.propDecidable

namespace Ribbon

variable {V E : Type*} [Fintype E] {left right : E → V} (R : Ribbon left right)

/-- The actual endpoint-graph component containing a facial circle. -/
noncomputable def faceComponent (f : R.FaceIndex) : Component left right :=
  componentOf left right (left (R.faceRoot f).edge)

@[simp] theorem faceComponent_faceOf (x : Flag E) :
    R.faceComponent (R.faceOf x) = componentOf left right (left x.edge) :=
  (R.sameFace_component (R.root_related x)).symm

/-- A component facial circle carries precisely its own component label. -/
theorem faceComponent_componentFaceMap (q : Component left right) (f : (R.componentRibbon q).FaceIndex) :
    R.faceComponent (R.componentFaceMap q f) = q := by
  induction f using Quotient.inductionOn with
  | h x =>
      change R.faceComponent (R.componentFaceMap q ((R.componentRibbon q).faceOf x)) = q
      rw [R.componentFaceMap_faceOf, R.faceComponent_faceOf]
      exact x.edge.property

/-- The graph component of a circle or of an isolated vertex disk. -/
noncomputable def capComponent : R.FaceIndex ⊕ IsolatedVertex left right → Component left right
  | .inl f => R.faceComponent f
  | .inr v => componentOf left right v.val

/-- The explicit capped-face partition preserves its actual graph-component index. -/
theorem capComponent_partition (q : Component left right) (f : R.CappedFace q) :
    R.capComponent (R.cappedFacePartition ⟨q, f⟩) = q := by
  unfold cappedFacePartition
  simp only [Equiv.trans_apply, Equiv.sigmaCongrRight_apply]
  generalize R.cappedFaceEquiv q f = y
  cases y with
  | inl g =>
      change R.faceComponent (R.componentFaceMap q g) = q
      exact R.faceComponent_componentFaceMap q g
  | inr h =>
      change componentOf left right (Quotient.out q) = q
      exact Quotient.out_eq q

/-- Equivalently, the inverse partition reads the actual component from the cap. -/
theorem cappedFacePartition_symm_fst (f : R.FaceIndex ⊕ IsolatedVertex left right) :
    (R.cappedFacePartition.symm f).1 = R.capComponent f := by
  have h := R.capComponent_partition (R.cappedFacePartition.symm f).1
    (R.cappedFacePartition.symm f).2
  have heta : (⟨(R.cappedFacePartition.symm f).1, (R.cappedFacePartition.symm f).2⟩ :
      (q : Component left right) × R.CappedFace q) = R.cappedFacePartition.symm f := by
    cases R.cappedFacePartition.symm f
    rfl
  rw [heta, Equiv.apply_symm_apply] at h
  exact h.symm

variable (keep : E → Prop) [DecidablePred keep]

/-- Component of an original vertex in the actually retained endpoint graph. -/
def retainedComponent (v : V) :
    Component (fun e : {e : E // keep e} => left e.val) (fun e => right e.val) :=
  componentOf _ _ v

omit [Fintype E] [DecidablePred keep] in
theorem retainedComponent_along (x : Flag E) (hx : keep x.edge) :
    retainedComponent (left := left) (right := right) keep ((along x).vertex left right) = retainedComponent (left := left) (right := right) keep (x.vertex left right) := by
  have h := componentOf_endpoints (fun e : {e : E // keep e} => left e.val)
    (fun e => right e.val) ⟨x.edge, hx⟩
  cases he : x.endpoint
  · simpa only [retainedComponent, along, Equiv.coe_fn_mk, Flag.vertex, he,
      Bool.not_false, Bool.false_eq_true, ite_true, ite_false] using h.symm
  · simpa only [retainedComponent, along, Equiv.coe_fn_mk, Flag.vertex, he,
      Bool.not_true, Bool.false_eq_true, ite_true, ite_false] using h

omit [Fintype E] in
theorem retainedComponent_switch (x : Flag E) :
    retainedComponent (left := left) (right := right) keep ((Flag.deletionSwitch keep x).vertex left right) =
      retainedComponent (left := left) (right := right) keep (x.vertex left right) := by
  rw [Flag.deletionSwitch_apply]
  split
  · exact retainedComponent_along keep x ‹keep x.edge›
  · rfl

theorem retainedComponent_smoothing (x : Flag E) :
    retainedComponent (left := left) (right := right) keep ((R.sidePairing.smoothing keep x).vertex left right) =
      retainedComponent (left := left) (right := right) keep (x.vertex left right) := by
  change retainedComponent (left := left) (right := right) keep ((R.sidePairing.corner (Flag.deletionSwitch keep x)).vertex left right) = _
  rw [R.sidePairing_corner, R.vertex, retainedComponent_switch]

theorem retainedComponent_iterate (n : ℕ) (x : Flag E) :
    retainedComponent (left := left) (right := right) keep (((R.sidePairing.smoothing keep : Flag E → Flag E)^[n] x).vertex left right) =
      retainedComponent (left := left) (right := right) keep (x.vertex left right) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', R.retainedComponent_smoothing, ih]

/-- A common smoothing circle lies in one actual retained graph component. -/
theorem commonFace_component {x y : Flag E} (h : R.commonFace keep x = R.commonFace keep y) :
    retainedComponent (left := left) (right := right) keep (x.vertex left right) = retainedComponent (left := left) (right := right) keep (y.vertex left right) := by
  have hcycle : ∀ z, (R.sidePairing.smoothing keep).SameCycle x z →
      retainedComponent (left := left) (right := right) keep (z.vertex left right) = retainedComponent (left := left) (right := right) keep (x.vertex left right) := by
    intro z hz
    obtain ⟨n, hn⟩ := hz.exists_nat_pow_eq
    have heq : (R.sidePairing.smoothing keep : Flag E → Flag E)^[n] x = z := by
      simpa only [Equiv.Perm.coe_pow] using hn
    rw [← heq]
    exact R.retainedComponent_iterate keep n x
  rcases (R.commonFace_eq_iff keep x y).mp h with h | h
  · exact (hcycle y h).symm
  · have hh := hcycle (Flag.deletionSwitch keep y) h
    rw [retainedComponent_switch] at hh
    exact hh.symm

/-- The retained-graph component label carried by a common smoothing circle. -/
noncomputable def commonComponent (f : (R.sidePairing.smoothingRibbon keep).FaceIndex) :
    Component (fun e : {e : E // keep e} => left e.val) (fun e => right e.val) :=
  retainedComponent (left := left) (right := right) keep ((R.commonRoot keep f).vertex left right)

@[simp] theorem commonComponent_commonFace (x : Flag E) :
    R.commonComponent keep (R.commonFace keep x) = retainedComponent (left := left) (right := right) keep (x.vertex left right) :=
  R.commonFace_component keep (R.commonFace_root keep (R.commonFace keep x))

/-- A traced retained circle has the same component before and after mapping
into the common smoothing system. -/
theorem faceComponent_smoothingFaceMap (f : (R.restrict keep).FaceIndex) :
    (R.restrict keep).faceComponent f = R.commonComponent keep (R.smoothingFaceMap keep f) := by
  induction f using Quotient.inductionOn with
  | h x =>
      change (R.restrict keep).faceComponent ((R.restrict keep).faceOf x) =
        R.commonComponent keep (R.smoothingFaceMap keep ((R.restrict keep).faceOf x))
      rw [(R.restrict keep).faceComponent_faceOf, R.smoothingFaceMap_faceOf]
      have hh : (R.sidePairing.smoothingRibbon keep).faceOf (smoothingFlag keep x) =
          R.commonFace keep (smoothingFlag keep x) := by
        simp only [commonFace, Flag.deletionToggle, Equiv.coe_fn_mk, smoothingFlag,
          Flag.retainedEquiv, x.edge.property, ite_true]
      rw [hh, R.commonComponent_commonFace]
      exact (flag_vertex_component (left := fun e : {e : E // keep e} => left e.val)
        (right := fun e => right e.val) x).symm

/-- The circle/disk partition preserves the actual retained graph component. -/
theorem capComponent_commonFacePartition (hlinks : R.VertexLinks)
    (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v)
    (f : (R.sidePairing.smoothingRibbon keep).FaceIndex) :
    (R.restrict keep).capComponent (R.commonFacePartition keep hlinks hvertices f) =
      R.commonComponent keep f := by
  classical
  unfold commonFacePartition
  simp only [Equiv.trans_apply]
  by_cases hm : R.MeetsRetained keep f
  · rw [Equiv.sumCompl_symm_apply_of_pos hm]
    change (R.restrict keep).faceComponent ((R.smoothingFaceEquiv keep).symm ⟨f, hm⟩) = _
    rw [R.faceComponent_smoothingFaceMap]
    have h := congrArg Subtype.val ((R.smoothingFaceEquiv keep).apply_symm_apply ⟨f, hm⟩)
    exact congrArg (R.commonComponent keep) h
  · rw [Equiv.sumCompl_symm_apply_of_neg hm]
    rfl

end Ribbon
namespace SidePairing

variable {V E F : Type*} [Fintype E] [Fintype F] {left right : E → V}
    {faces : F → Faces.Face left right} (P : SidePairing faces)
    (keep : E → Prop) [DecidablePred keep]
    (hlinks : P.VertexLinks)
    (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v)
    (hfaces : ∀ f, ∃ x : Flag E, x.vertex (fun e => P.face e false) (fun e => P.face e true) = f)

/-- The actual complementary cap correspondence sends a retained boundary
side to the deleted-dual component of its original incident face. -/
theorem complementaryCap_region (x : Flag {e : E // keep e}) :
    ComplementEuler.boundaryRegion
      (P.complementaryComponentCapEquiv keep hlinks hvertices hfaces)
      ((P.toRibbon.restrict keep).faceOf x) =
        P.originalFaceRegion keep (P.flagFace (Ribbon.smoothingFlag keep x)) := by
  let y := Ribbon.smoothingFlag keep x
  have hp := P.toRibbon.commonFacePartition_retained keep
    (P.toRibbon_vertexLinks hlinks) hvertices x
  have hpinv :
      (P.toRibbon.commonFacePartition keep (P.toRibbon_vertexLinks hlinks) hvertices).symm
        (Sum.inl ((P.toRibbon.restrict keep).faceOf x)) = P.toRibbon.commonFace keep y := by
    exact (Equiv.symm_apply_eq _).mpr hp.symm
  have hd : (P.complementarySmoothingEquiv keep).symm (P.toRibbon.commonFace keep y) =
      P.dualRibbon.commonFace (fun e => ¬keep e) (Flag.swapSideEndpoint y) := by
    apply (P.complementarySmoothingEquiv keep).injective
    rw [Equiv.apply_symm_apply, P.complementarySmoothingEquiv_commonFace]
  unfold ComplementEuler.boundaryRegion complementaryComponentCapEquiv complementaryCapEquiv
  simp only [Equiv.symm_trans_apply, Equiv.symm_symm]
  rw [(P.dualRibbon.restrict (fun e => ¬keep e)).cappedFacePartition_symm_fst]
  rw [P.dualRibbon.capComponent_commonFacePartition, hpinv, hd,
    P.dualRibbon.commonComponent_commonFace, P.swap_vertex]
  rfl

/-- Every actual complementary region has a retained boundary circle when
at least one edge survives and the original full side dual is connected. -/
theorem complementaryCap_regions_surjective
    (hdual : Incidence.Connected (fun e => P.face e false) (fun e => P.face e true))
    (hne : Nonempty {e : E // keep e}) :
    Function.Surjective (ComplementEuler.boundaryRegion
      (P.complementaryComponentCapEquiv keep hlinks hvertices hfaces)) := by
  intro q
  obtain ⟨e, he, hside | hside⟩ := Incidence.every_deleted_component_meets
    (fun e => P.face e false) (fun e => P.face e true) keep hdual hne q
  · refine ⟨(P.toRibbon.restrict keep).faceOf ⟨⟨e, he⟩, false, false⟩, ?_⟩
    rw [P.complementaryCap_region]
    exact hside
  · refine ⟨(P.toRibbon.restrict keep).faceOf ⟨⟨e, he⟩, true, false⟩, ?_⟩
    rw [P.complementaryCap_region]
    exact hside

end SidePairing
end WeightedMIS.EmbeddingFaces
