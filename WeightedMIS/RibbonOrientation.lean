module

public import WeightedMIS.OriginalFaces
public import WeightedMIS.EmbeddingDeletionOrientation
public import WeightedMIS.RibbonComponents

/-!
# Coherent polygon orientations from actual flag signs

Signs that reverse across the three flag matchings induce coherent signs on
traced facial polygons. Conversely the original polygon orientation supplies
these signs. The actual deletion and component constructions preserve them,
so the orientable dimension bound applies to the constructed capped maps.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open SidePairing

namespace Ribbon

variable {V E : Type*} {left right : E → V} (R : Ribbon left right)

/-- Orientation of the local triangles, reversing at each actual gluing. -/
structure FlagOrientation where
  sign : Flag E → ℚ
  signs : ∀ x, sign x = 1 ∨ sign x = -1
  across : ∀ x, sign (SidePairing.across x) = -sign x
  corner : ∀ x, sign (R.corner x) = -sign x
  along : ∀ x, sign (SidePairing.along x) = -sign x

namespace FlagOrientation

variable {R} (O : R.FlagOrientation)

@[simp] theorem rotation (x : Flag E) : O.sign (R.rotation x) = O.sign x := by
  change O.sign (R.corner (SidePairing.along x)) = O.sign x
  rw [O.corner, O.along, neg_neg]

theorem iterate_rotation (n : ℕ) (x : Flag E) :
    O.sign ((R.rotation : Flag E → Flag E)^[n] x) = O.sign x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', O.rotation, ih]

variable [Fintype E]

/-- The chosen traversal direction gives a coherent sign for its actual polygon. -/
noncomputable def faceSign (f : R.FaceIndex) : ℚ := -O.sign (R.faceRoot f)

theorem faceSign_signs (f : R.FaceIndex) : O.faceSign f = 1 ∨ O.faceSign f = -1 := by
  rcases O.signs (R.faceRoot f) with h | h <;> simp [faceSign, h]

theorem faceSign_position (d : Occurrence R.faces) : O.faceSign d.1 = -O.sign (R.positionFlag d) := by
  change -O.sign (R.faceRoot d.1) =
    -O.sign ((R.rotation : Flag E → Flag E)^[d.2.val] (R.faceRoot d.1))
  rw [O.iterate_rotation]

theorem sign_startFlag (d : Occurrence R.faces) :
    O.sign (R.sidePairing.startFlag d) = -O.faceSign d.1 := by
  rw [R.sidePairing_startFlag, O.faceSign_position, neg_neg]

theorem sign_endFlag (d : Occurrence R.faces) :
    O.sign (R.sidePairing.endFlag d) = O.faceSign d.1 := by
  rw [R.sidePairing_endFlag, O.along, O.faceSign_position]

/-- The sign formula uses the actual selected direction of each edge-side occurrence. -/
theorem sign_formula (x : Flag E) :
    O.sign x = O.faceSign (R.sidePairing.flagFace x) *
      boolSign (R.sidePairing.forward x.edge x.side) * boolSign x.endpoint := by
  obtain ⟨⟨d, t⟩, rfl⟩ := R.sidePairing.flagEquiv.surjective x
  cases t
  · rw [R.sidePairing.flagEquiv_false, O.sign_startFlag, R.sidePairing.flagFace_startFlag]
    simp only [startFlag, R.sidePairing.forward_pairing, boolSign_not]
    rw [mul_neg, mul_assoc, boolSign_mul_self, mul_one]
  · rw [R.sidePairing.flagEquiv_true, O.sign_endFlag, R.sidePairing.flagFace_endFlag]
    simp only [endFlag, R.sidePairing.forward_pairing]
    rw [mul_assoc, boolSign_mul_self, mul_one]

/-- The actually traced facial polygons carry a coherent surface orientation. -/
noncomputable def polygonOrientation : R.sidePairing.Orientation where
  sign := O.faceSign
  signs := O.faceSign_signs
  coherent := by
    intro e
    have h := O.across (⟨e, false, true⟩ : Flag E)
    rw [O.sign_formula, O.sign_formula] at h
    simp only [SidePairing.across, Equiv.coe_fn_mk, Bool.not_false, flagFace,
      show boolSign true = 1 from rfl, mul_one] at h
    linarith only [h]

/-- Restrict the orientation signs to a genuine graph component. -/
def component (q : Incidence.Component left right) : (R.componentRibbon q).FlagOrientation where
  sign x := O.sign (componentFlag x)
  signs x := O.signs _
  across x := by
    change O.sign (SidePairing.across (componentFlag x)) = -O.sign (componentFlag x)
    exact O.across _
  corner x := O.corner _
  along x := by
    change O.sign (SidePairing.along (componentFlag x)) = -O.sign (componentFlag x)
    exact O.along _

end FlagOrientation
end Ribbon

namespace SidePairing.Orientation

variable {V E F : Type*} {left right : E → V} {faces : F → Faces.Face left right}
    {P : SidePairing faces} (O : P.Orientation)

/-- Original coherent face signs induce actual unit signs on every flag. -/
theorem flagOrientation_signs (x : Flag E) : O.flagOrientation x = 1 ∨ O.flagOrientation x = -1 := by
  rcases O.signs (P.flagFace x) with hs | hs <;>
    cases hf : P.forward x.edge x.side <;> cases ht : x.endpoint <;>
    simp [flagOrientation, hs, hf, ht, boolSign]

/-- The original polygon orientation is a genuine ribbon flag orientation. -/
def toFlagOrientation : P.toRibbon.FlagOrientation where
  sign := O.flagOrientation
  signs := O.flagOrientation_signs
  across := O.flagOrientation_across
  corner := O.flagOrientation_corner
  along := O.flagOrientation_along

end SidePairing.Orientation

namespace Ribbon.FlagOrientation

variable {V E : Type*} [Fintype E] {left right : E → V} {R : Ribbon left right}
    (O : R.FlagOrientation)

theorem sign_vertexNext (x : Flag E) :
    O.sign (R.sidePairing.vertexNext x) = O.sign x := by
  change O.sign (SidePairing.across (R.sidePairing.corner x)) = O.sign x
  rw [O.across, R.sidePairing_corner, O.corner, neg_neg]

theorem sign_iterate_vertexNext (n : ℕ) (x : Flag E) :
    O.sign ((R.sidePairing.vertexNext : Flag E → Flag E)^[n] x) = O.sign x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', O.sign_vertexNext, ih]

theorem sign_retainedCorner (keep : E → Prop) (x : RetainedFlag keep) :
    O.sign (R.sidePairing.retainedCorner keep x).val = -O.sign x.val := by
  change O.sign (SidePairing.across (R.sidePairing.retainedVertexNext keep x).val) = _
  rw [O.across]
  congr 1
  change O.sign (PermutationDeletion.firstReturn R.sidePairing.vertexNext
    (fun y => keep y.edge) x).val = _
  rw [PermutationDeletion.firstReturn_apply]
  exact O.sign_iterate_vertexNext _ _

/-- The spliced deletion corner matching preserves a coherent flag orientation. -/
noncomputable def restrict (keep : E → Prop) : (R.restrict keep).FlagOrientation where
  sign x := O.sign (Flag.retainedEquiv keep x).val
  signs x := O.signs _
  across x := by
    change O.sign (SidePairing.across (Flag.retainedEquiv keep x).val) =
      -O.sign (Flag.retainedEquiv keep x).val
    exact O.across _
  corner x := by
    have h := O.sign_retainedCorner keep (Flag.retainedEquiv keep x)
    simpa only [Ribbon.restrict, Equiv.trans_apply, Equiv.apply_symm_apply] using h
  along x := by
    change O.sign (SidePairing.along (Flag.retainedEquiv keep x).val) =
      -O.sign (Flag.retainedEquiv keep x).val
    exact O.along _

/-- Removing unused vertex labels does not alter any of the oriented flag matchings. -/
noncomputable def activeRestrict (keep : E → Prop) : (R.activeRestrict keep).FlagOrientation where
  sign := (O.restrict keep).sign
  signs := (O.restrict keep).signs
  across := (O.restrict keep).across
  corner := (O.restrict keep).corner
  along := (O.restrict keep).along

/-- The actual capped residual facial embedding has a coherent orientation. -/
noncomputable def cappedRestriction (keep : E → Prop) [DecidablePred keep]
    (hlinks : R.VertexLinks) (hnonempty : Nonempty {e : E // keep e}) :
    (R.cappedRestriction keep hlinks hnonempty).sides.Orientation :=
  (O.activeRestrict keep).polygonOrientation

end Ribbon.FlagOrientation
end WeightedMIS.EmbeddingFaces
