module

public import WeightedMIS.EmbeddingDual
public import WeightedMIS.RibbonCellular
public import WeightedMIS.ComplementEuler

/-!
# Recovering the original facial labels from actual ribbon circles

Tracing the corner matching of a polygon-side pairing reproduces exactly its
original nonempty faces. The equivalence is induced by actual incident face
labels, rather than by a cardinality or rank assumption.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open SidePairing

namespace Ribbon

variable {V E : Type*} [Fintype E] {left right : E → V} (R : Ribbon left right)

@[simp] theorem faceOf_corner (x : Flag E) : R.faceOf (R.corner x) = R.faceOf x := by
  have h : R.rotation.SameCycle (along x) (R.corner x) := by
    have hh : R.rotation.SameCycle (along x) (R.rotation (along x)) := ⟨1, by simp⟩
    simpa only [rotation, Equiv.trans_apply, along_along] using hh
  have hh := R.faceOf_eq_of_sameCycle h
  simpa only [R.faceOf_along] using hh.symm

/-- The face containing a traced occurrence is its original circle label. -/
@[simp] theorem faceOf_positionFlag (d : Occurrence R.faces) :
    R.faceOf (R.positionFlag d) = d.1 := by
  have h := R.faceOf_eq_of_sameCycle (R.root_sameCycle_orbitFlag (R.occurrenceEquiv d))
  change R.faceOf (R.faceRoot d.1) = R.faceOf (R.positionFlag d) at h
  rw [R.faceOf_root] at h
  exact h.symm

/-- Reconstructing polygon sides preserves actual flag-to-circle incidence. -/
@[simp] theorem sidePairing_flagFace (x : Flag E) : R.sidePairing.flagFace x = R.faceOf x := by
  obtain ⟨⟨d, t⟩, rfl⟩ := R.sidePairing.flagEquiv.surjective x
  cases t
  · rw [R.sidePairing.flagEquiv_false, R.sidePairing.flagFace_startFlag,
      R.sidePairing_startFlag, R.faceOf_positionFlag]
  · rw [R.sidePairing.flagEquiv_true, R.sidePairing.flagFace_endFlag,
      R.sidePairing_endFlag, R.faceOf_along, R.faceOf_positionFlag]

/-- The generated face of an edge side is its actual ribbon circle. -/
theorem sidePairing_face (e : E) (b : Bool) :
    R.sidePairing.face e b = R.faceOf ⟨e, b, false⟩ :=
  R.sidePairing_flagFace ⟨e, b, false⟩

end Ribbon

namespace SidePairing

variable {V E F : Type*} [Fintype E] {left right : E → V}
    {faces : F → Faces.Face left right} (P : SidePairing faces)

omit [Fintype E] in
@[simp] theorem flagFace_along (x : Flag E) : P.flagFace (along x) = P.flagFace x := rfl

omit [Fintype E] in
@[simp] theorem flagFace_rotation (x : Flag E) :
    P.flagFace (P.toRibbon.rotation x) = P.flagFace x := by
  exact (P.corner_flagFace (along x)).trans (P.flagFace_along x)

omit [Fintype E] in
theorem flagFace_iterate (n : ℕ) (x : Flag E) :
    P.flagFace ((P.toRibbon.rotation : Flag E → Flag E)^[n] x) = P.flagFace x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', P.flagFace_rotation, ih]

theorem flagFace_sameCycle {x y : Flag E} (h : P.toRibbon.rotation.SameCycle x y) :
    P.flagFace x = P.flagFace y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have heq : (P.toRibbon.rotation : Flag E → Flag E)^[n] x = y := by
    simpa only [Equiv.Perm.coe_pow] using hn
  rw [← heq, P.flagFace_iterate]

theorem flagFace_sameFace {x y : Flag E} (h : P.toRibbon.SameFace x y) :
    P.flagFace x = P.flagFace y := by
  rcases h with h | h
  · exact P.flagFace_sameCycle h
  · have hh := P.flagFace_sameCycle h
    simpa only [P.flagFace_along] using hh

/-- The actual original facial walk connects all flags with that face label. -/
theorem faceOf_eq_of_flagFace {x y : Flag E} (h : P.flagFace x = P.flagFace y) :
    P.toRibbon.faceOf x = P.toRibbon.faceOf y := by
  have hp := P.dual_link_same_face x y h
  have hmap : ∀ a b : Flag E, P.dualRibbon.LinkStep a b →
      P.toRibbon.faceOf (Flag.swapSideEndpoint a) =
        P.toRibbon.faceOf (Flag.swapSideEndpoint b) := by
    intro a b hab
    cases hab with
    | across => simp only [Flag.swapSideEndpoint_across, P.toRibbon.faceOf_along]
    | corner =>
        change P.toRibbon.faceOf (Flag.swapSideEndpoint a) =
          P.toRibbon.faceOf (Flag.swapSideEndpoint (P.dualCorner a))
        simp only [P.dualCorner_apply, Flag.swapSideEndpoint_twice]
        exact (P.toRibbon.faceOf_corner _).symm
  have hclosure : ∀ {a b : Flag E}, Relation.ReflTransGen P.dualRibbon.LinkStep a b →
      P.toRibbon.faceOf (Flag.swapSideEndpoint a) = P.toRibbon.faceOf (Flag.swapSideEndpoint b) := by
    intro a b hp
    induction hp with
    | refl => rfl
    | tail _ hs ih => exact ih.trans (hmap _ _ hs)
  have hh := hclosure hp
  simpa only [Flag.swapSideEndpoint_twice] using hh

/-- Two actual ribbon circles coincide exactly when they carry the same
original facial label. -/
theorem toRibbon_sameFace_iff (x y : Flag E) :
    P.toRibbon.SameFace x y ↔ P.flagFace x = P.flagFace y :=
  ⟨P.flagFace_sameFace, fun h => Quotient.exact (P.faceOf_eq_of_flagFace h)⟩

/-- Forget the boundary representative and recover its original facial label. -/
def originalFaceMap : P.toRibbon.FaceIndex → F :=
  Quotient.lift P.flagFace (fun _ _ h => P.flagFace_sameFace h)

@[simp] theorem originalFaceMap_faceOf (x : Flag E) :
    P.originalFaceMap (P.toRibbon.faceOf x) = P.flagFace x := rfl

theorem originalFaceMap_injective : Function.Injective P.originalFaceMap := by
  intro f g
  induction f using Quotient.inductionOn with
  | h x =>
      induction g using Quotient.inductionOn with
      | h y => exact P.faceOf_eq_of_flagFace

theorem originalFaceMap_surjective (hfaces : ∀ f, 0 < (faces f).boundary.length) :
    Function.Surjective P.originalFaceMap := by
  intro f
  refine ⟨P.toRibbon.faceOf (P.startFlag ⟨f, 0, hfaces f⟩), ?_⟩
  exact P.flagFace_startFlag _

/-- Tracing an original polygon-side embedding recovers exactly its nonempty
facial labels, with their actual flag incidence. -/
noncomputable def originalFaceEquiv (hfaces : ∀ f, 0 < (faces f).boundary.length) :
    P.toRibbon.FaceIndex ≃ F :=
  Equiv.ofBijective P.originalFaceMap
    ⟨P.originalFaceMap_injective, P.originalFaceMap_surjective hfaces⟩

@[simp] theorem originalFaceEquiv_faceOf (hfaces : ∀ f, 0 < (faces f).boundary.length)
    (x : Flag E) : P.originalFaceEquiv hfaces (P.toRibbon.faceOf x) = P.flagFace x := rfl

/-- The recovered facial-label equivalence preserves the side incidence map. -/
@[simp] theorem originalFaceEquiv_side (hfaces : ∀ f, 0 < (faces f).boundary.length)
    (e : E) (b : Bool) :
    P.originalFaceEquiv hfaces (P.toRibbon.sidePairing.face e b) = P.face e b := by
  rw [P.toRibbon.sidePairing_face, P.originalFaceEquiv_faceOf]
  rfl

/-- Tracing the original corners preserves each actual facial boundary length,
including repeated occurrences of the same original edge label. -/
theorem originalFaceEquiv_length [Fintype F]
    (hfaces : ∀ f, 0 < (faces f).boundary.length) (f : P.toRibbon.FaceIndex) :
    (P.toRibbon.faces f).boundary.length = (faces (P.originalFaceEquiv hfaces f)).boundary.length := by
  classical
  rw [← P.toRibbon.sidePairing.face_fiber_size, ← P.face_fiber_size]
  unfold RegionParity.fiberSize
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← P.originalFaceEquiv_side hfaces s.1 s.2]
  exact (P.originalFaceEquiv hfaces).injective.eq_iff.symm

/-- The odd-facial-walk count survives the faithful corner-system conversion. -/
theorem originalFaceEquiv_odd_count [Fintype F]
    (hfaces : ∀ f, 0 < (faces f).boundary.length) :
    Fintype.card {f : P.toRibbon.FaceIndex // Odd (P.toRibbon.faces f).boundary.length} =
      Fintype.card {f : F // Odd (faces f).boundary.length} := by
  classical
  exact Fintype.card_congr ((P.originalFaceEquiv hfaces).subtypeEquiv fun f => by
    rw [P.originalFaceEquiv_length hfaces])

end SidePairing
end WeightedMIS.EmbeddingFaces
