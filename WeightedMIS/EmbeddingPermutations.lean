module

public import WeightedMIS.Embedding

/-!
# The two vertex-link involutions

The corner involution pairs the end of one genuine boundary occurrence with
the beginning of its successor. The across involution pairs the two sides at
one edge endpoint. Both are fixed-point-free and preserve the vertex label.
Their alternating composition supplies the finite link permutations used for
ribbon-graph deletion and first-return constructions.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

variable {V E F : Type*} {left right : E → V} {faces : F → Faces.Face left right}

/-- Convert a traversal-relative endpoint bit into an original edge endpoint. -/
def orientEnd (forward endpoint : Bool) : Bool := if forward then endpoint else !endpoint

@[simp] theorem orientEnd_self (f t : Bool) : orientEnd f (orientEnd f t) = t := by
  cases f <;> cases t <;> rfl

@[simp] theorem orientEnd_false (f : Bool) : orientEnd f false = !f := by
  cases f <;> rfl

@[simp] theorem orientEnd_true (f : Bool) : orientEnd f true = f := by
  cases f <;> rfl

namespace SidePairing

variable (P : SidePairing faces)

/-- Traverse-endpoint coordinates and original-edge flags are equivalent. -/
def flagEquiv : Occurrence faces × Bool ≃ Flag E where
  toFun d := ⟨(P.pairing d.1).1, (P.pairing d.1).2,
    orientEnd ((faces d.1.1).boundary.forwardAt d.1.2) d.2⟩
  invFun x := ⟨P.side x.edge x.side, orientEnd (P.forward x.edge x.side) x.endpoint⟩
  left_inv := by
    rintro ⟨d, t⟩
    change (P.side (P.pairing d).1 (P.pairing d).2,
      orientEnd (P.forward (P.pairing d).1 (P.pairing d).2)
        (orientEnd ((faces d.1).boundary.forwardAt d.2) t)) = (d, t)
    have hd : P.side (P.pairing d).1 (P.pairing d).2 = d := by
      change P.pairing.symm (P.pairing d) = d
      exact P.pairing.symm_apply_apply d
    unfold forward
    rw [hd, orientEnd_self]
  right_inv := by
    rintro ⟨e, s, t⟩
    change ⟨(P.pairing (P.side e s)).1, (P.pairing (P.side e s)).2,
      orientEnd ((faces (P.side e s).1).boundary.forwardAt (P.side e s).2)
        (orientEnd (P.forward e s) t)⟩ = (⟨e, s, t⟩ : Flag E)
    have hd : P.pairing (P.side e s) = (e, s) := P.pairing.apply_symm_apply (e, s)
    rw [hd]
    change (⟨e, s, orientEnd (P.forward e s) (orientEnd (P.forward e s) t)⟩ : Flag E) = _
    rw [orientEnd_self]

@[simp] theorem flagEquiv_false (d : Occurrence faces) :
    P.flagEquiv (d, false) = P.startFlag d := by
  simp only [flagEquiv, Equiv.coe_fn_mk, orientEnd_false]
  rfl

@[simp] theorem flagEquiv_true (d : Occurrence faces) :
    P.flagEquiv (d, true) = P.endFlag d := by
  simp only [flagEquiv, Equiv.coe_fn_mk, orientEnd_true]
  rfl

/-- Pair incoming and outgoing ends around the same face corner. -/
def cornerCoordinates : Equiv.Perm (Occurrence faces × Bool) where
  toFun x := if x.2 then (faceNext x.1, false) else (facePrev x.1, true)
  invFun x := if x.2 then (faceNext x.1, false) else (facePrev x.1, true)
  left_inv := by
    rintro ⟨d, t⟩
    cases t <;> simp [facePrev]
  right_inv := by
    rintro ⟨d, t⟩
    cases t <;> simp [facePrev]

/-- The actual corner involution on original edge flags. -/
def corner : Equiv.Perm (Flag E) :=
  P.flagEquiv.symm.trans ((cornerCoordinates (faces := faces)).trans P.flagEquiv)

/-- The other side of one fixed original edge endpoint. -/
def across : Equiv.Perm (Flag E) where
  toFun x := ⟨x.edge, !x.side, x.endpoint⟩
  invFun x := ⟨x.edge, !x.side, x.endpoint⟩
  left_inv := by intro x; cases x; simp
  right_inv := by intro x; cases x; simp

@[simp] theorem corner_endFlag (d : Occurrence faces) :
    P.corner (P.endFlag d) = P.startFlag (faceNext d) := by
  rw [← P.flagEquiv_true d]
  simp only [corner, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact P.flagEquiv_false (faceNext d)

@[simp] theorem corner_startFlag (d : Occurrence faces) :
    P.corner (P.startFlag d) = P.endFlag (facePrev d) := by
  rw [← P.flagEquiv_false d]
  simp only [corner, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact P.flagEquiv_true (facePrev d)

/-- The actual corner involution traverses one of the already defined link steps. -/
theorem linkStep_corner (x : Flag E) : P.LinkStep x (P.corner x) := by
  obtain ⟨⟨d, t⟩, rfl⟩ := P.flagEquiv.surjective x
  cases t
  · rw [P.flagEquiv_false, P.corner_startFlag]
    have h := LinkStep.cornerRev (P := P) (facePrev d)
    simpa [facePrev] using h
  · rw [P.flagEquiv_true, P.corner_endFlag]
    exact .corner d

/-- Both involutions preserve the actual graph vertex. -/
theorem corner_vertex (x : Flag E) : (P.corner x).vertex left right = x.vertex left right :=
  (P.linkStep_vertex (P.linkStep_corner x)).symm

/-- The two-sides involution preserves the actual graph vertex. -/
theorem across_vertex (x : Flag E) :
    (across x).vertex left right = x.vertex left right := rfl

@[simp] theorem corner_corner (x : Flag E) : P.corner (P.corner x) = x := by
  obtain ⟨⟨d, t⟩, rfl⟩ := P.flagEquiv.surjective x
  cases t <;> simp [facePrev]

@[simp] theorem across_across (x : Flag E) : across (across x) = x := by
  cases x
  simp [across]

/-- Corners pair distinct traversal endpoints, including loops and bridges. -/
theorem corner_ne_self (x : Flag E) : P.corner x ≠ x := by
  obtain ⟨⟨d, t⟩, rfl⟩ := P.flagEquiv.surjective x
  intro h
  have ht := congrArg (fun x => (P.flagEquiv.symm x).2) h
  simp only [corner, Equiv.trans_apply, Equiv.symm_apply_apply] at ht
  cases t <;> simp only [cornerCoordinates, Equiv.coe_fn_mk,
    Bool.false_eq_true, ite_false, ite_true, Bool.true_eq_false] at ht

/-- The two edge sides remain distinct even when they meet the same face. -/
theorem across_ne_self (x : Flag E) : across x ≠ x := by
  intro h
  have hs := congrArg Flag.side h
  cases x.side <;> simp [across] at hs

/-- One step of the vertex-link permutation alternates corner and across moves. -/
def vertexNext : Equiv.Perm (Flag E) := P.corner.trans across

/-- Vertex-link rotations preserve the supplied graph vertex. -/
theorem vertexNext_vertex (x : Flag E) :
    (P.vertexNext x).vertex left right = x.vertex left right := by
  exact (across_vertex (P.corner x)).trans (P.corner_vertex x)

@[simp] theorem corner_symm (x : Flag E) : P.corner.symm x = P.corner x := by
  apply P.corner.injective
  simp

@[simp] theorem across_symm (x : Flag E) : across.symm x = across x := rfl

/-- Reversing a link flag by its other edge side reverses the vertex rotation. -/
theorem across_vertexNext_across (x : Flag E) :
    across (P.vertexNext (across x)) = P.vertexNext.symm x := by
  simp only [vertexNext, Equiv.trans_apply, Equiv.symm_trans_apply,
    across_across, across_symm, corner_symm]

/-- The edge-side involution conjugates the vertex rotation to its inverse. -/
theorem across_conj_vertexNext :
    (across.trans P.vertexNext).trans across = P.vertexNext.symm := by
  ext x
  exact P.across_vertexNext_across x

end SidePairing
end WeightedMIS.EmbeddingFaces
