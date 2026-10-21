module

public import WeightedMIS.EmbeddingDeletion
public import WeightedMIS.Orientable

/-!
# Orientation signs on retained edge flags

A coherent orientation of the original polygons gives nonzero flag signs that
reverse across each of the three local pairings. The inherited corner matching
constructed by deletion has the same reversal property. This proves preservation
of local orientation data under the actual deletion construction.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.SidePairing.Orientation

variable {V E F : Type*} {left right : E → V}
    {faces : F → Faces.Face left right} {P : SidePairing faces} (O : P.Orientation)

/-- Orientation of the triangle represented by a side/endpoint flag. -/
def flagOrientation (x : Flag E) : ℚ :=
  O.sign (P.flagFace x) * boolSign (P.forward x.edge x.side) * boolSign x.endpoint

theorem flagOrientation_ne_zero (x : Flag E) : O.flagOrientation x ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (O.sign_ne_zero _) (boolSign_ne_zero _)) (boolSign_ne_zero _)

@[simp] theorem flagOrientation_endFlag (d : Occurrence faces) :
    O.flagOrientation (P.endFlag d) = O.sign d.1 := by
  simp only [flagOrientation, endFlag, flagFace, face_pairing, forward_pairing]
  rw [mul_assoc, boolSign_mul_self, mul_one]

@[simp] theorem flagOrientation_startFlag (d : Occurrence faces) :
    O.flagOrientation (P.startFlag d) = -O.sign d.1 := by
  simp only [flagOrientation, startFlag, flagFace, face_pairing, forward_pairing,
    boolSign_not]
  rw [mul_neg, mul_assoc, boolSign_mul_self, mul_one]

theorem flagOrientation_across (x : Flag E) :
    O.flagOrientation (across x) = -O.flagOrientation x := by
  rcases x with ⟨e, s, t⟩
  have h := congrArg (fun q : ℚ => q * boolSign t) (O.coherent e)
  cases s <;> simp only [across, Equiv.coe_fn_mk, Bool.not_false, Bool.not_true,
    flagOrientation, flagFace] <;> linarith

theorem flagOrientation_corner (x : Flag E) :
    O.flagOrientation (P.corner x) = -O.flagOrientation x := by
  obtain ⟨⟨d, t⟩, rfl⟩ := P.flagEquiv.surjective x
  cases t
  · rw [P.flagEquiv_false, P.corner_startFlag, O.flagOrientation_endFlag,
      O.flagOrientation_startFlag]
    simp [facePrev, faceNext]
  · rw [P.flagEquiv_true, P.corner_endFlag, O.flagOrientation_startFlag,
      O.flagOrientation_endFlag]
    rfl

theorem flagOrientation_along (x : Flag E) :
    O.flagOrientation (along x) = -O.flagOrientation x := by
  simp only [flagOrientation, flagFace, along, Equiv.coe_fn_mk, boolSign_not, mul_neg]

theorem flagOrientation_vertexNext (x : Flag E) :
    O.flagOrientation (P.vertexNext x) = O.flagOrientation x := by
  change O.flagOrientation (across (P.corner x)) = _
  rw [O.flagOrientation_across, O.flagOrientation_corner, neg_neg]

theorem flagOrientation_iterate_vertexNext (n : ℕ) (x : Flag E) :
    O.flagOrientation ((P.vertexNext : Flag E → Flag E)^[n] x) = O.flagOrientation x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', O.flagOrientation_vertexNext, ih]

/-- A whole inherited vertex rotation preserves orientation, despite skipping
an arbitrary number of deleted edge bands. -/
theorem flagOrientation_retainedVertexNext [Fintype E]
    (keep : E → Prop) (x : RetainedFlag keep) :
    O.flagOrientation (P.retainedVertexNext keep x).val = O.flagOrientation x.val := by
  change O.flagOrientation (PermutationDeletion.firstReturn P.vertexNext
    (fun y => keep y.edge) x).val = _
  rw [PermutationDeletion.firstReturn_apply]
  exact O.flagOrientation_iterate_vertexNext _ _

/-- The actually spliced corners retain the original orientation-reversal
condition. -/
theorem flagOrientation_retainedCorner [Fintype E]
    (keep : E → Prop) (x : RetainedFlag keep) :
    O.flagOrientation (P.retainedCorner keep x).val = -O.flagOrientation x.val := by
  change O.flagOrientation (across (P.retainedVertexNext keep x).val) = _
  rw [O.flagOrientation_across, O.flagOrientation_retainedVertexNext]

include O in
/-- Every retained pairing reverses the same nonzero flag orientation. -/
theorem retained_orientation [Fintype E] (keep : E → Prop) :
    ∃ q : RetainedFlag keep → ℚ, (∀ x, q x ≠ 0) ∧
      (∀ x, q (retainedAcross keep x) = -q x) ∧
      (∀ x, q (P.retainedCorner keep x) = -q x) ∧
      (∀ x, q (retainedAlong keep x) = -q x) := by
  refine ⟨fun x => O.flagOrientation x.val, fun x => O.flagOrientation_ne_zero x.val,
    ?_, ?_, ?_⟩
  · intro x
    exact O.flagOrientation_across x.val
  · intro x
    exact O.flagOrientation_retainedCorner keep x
  · intro x
    exact O.flagOrientation_along x.val

end WeightedMIS.EmbeddingFaces.SidePairing.Orientation
