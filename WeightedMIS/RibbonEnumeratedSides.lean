module

public import WeightedMIS.RibbonEnumeration

/-!
# Certifying the computed facial walks as an actual two-sided embedding

Every occurrence on a computed least-period face is paired with its original
edge side. Injectivity follows from separated first-unseen roots and simple
oriented cycles; surjectivity follows from the complete supplied flag order.
Thus the computable face rows are the rows of a genuine cellular embedding.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open SidePairing FiniteCycleEnumeration

namespace Flag

/-- Flags of one edge side differ only by their endpoint direction. -/
theorem eq_or_eq_along {E : Type*} (x y : Flag E)
    (h : (x.edge, x.side) = (y.edge, y.side)) : x = y ∨ x = along y := by
  rcases x with ⟨e, s, t⟩
  rcases y with ⟨e', s', t'⟩
  have he : e = e' := congrArg Prod.fst h
  have hs : s = s' := congrArg Prod.snd h
  subst e'
  subst s'
  cases t <;> cases t' <;> simp [along]

end Flag

namespace Ribbon

variable {V E : Type*} [Fintype E] [DecidableEq E] {left right : E → V}
    (R : Ribbon left right) (order : List (Flag E))

/-- The actual original flag at a computed boundary occurrence. -/
def enumeratedPosition (d : Occurrence (R.enumeratedFace order)) : Flag E :=
  (R.rotation : Flag E → Flag E)^[d.2.val] (R.enumeratedRoot order d.1)

/-- Every occurrence follows the chosen root's actual oriented cycle. -/
theorem enumeratedPosition_sameCycle (d : Occurrence (R.enumeratedFace order)) :
    R.rotation.SameCycle (R.enumeratedRoot order d.1) (R.enumeratedPosition order d) :=
  ⟨(d.2.val : ℤ), by simp only [zpow_natCast, Equiv.Perm.coe_pow, enumeratedPosition]⟩

@[simp] theorem faceOf_enumeratedPosition (d : Occurrence (R.enumeratedFace order)) :
    R.faceOf (R.enumeratedPosition order d) = R.faceOf (R.enumeratedRoot order d.1) :=
  (R.faceOf_eq_of_sameCycle (R.enumeratedPosition_sameCycle order d)).symm

/-- The computed walk records precisely its traced original edge label. -/
theorem enumeratedFace_edgeAt (d : Occurrence (R.enumeratedFace order)) :
    (R.enumeratedFace order d.1).boundary.edgeAt d.2 = (R.enumeratedPosition order d).edge := by
  exact (Faces.Boundary.castEnd_edgeAt
    (R.trace (R.enumeratedRoot order d.1) (periodLength R.rotation (R.enumeratedRoot order d.1))) _ d.2).trans
    (R.trace_edgeAt (R.enumeratedRoot order d.1) _
      ⟨d.2.val, by simpa only [R.enumeratedFace_length] using d.2.isLt⟩)

/-- The computed walk records its actual traversal direction. -/
theorem enumeratedFace_forwardAt (d : Occurrence (R.enumeratedFace order)) :
    (R.enumeratedFace order d.1).boundary.forwardAt d.2 = !(R.enumeratedPosition order d).endpoint := by
  exact (Faces.Boundary.castEnd_forwardAt
    (R.trace (R.enumeratedRoot order d.1) (periodLength R.rotation (R.enumeratedRoot order d.1))) _ d.2).trans
    (R.trace_forwardAt (R.enumeratedRoot order d.1) _
      ⟨d.2.val, by simpa only [R.enumeratedFace_length] using d.2.isLt⟩)

/-- Pair a computed occurrence with its actual original edge side. -/
def enumeratedSide (d : Occurrence (R.enumeratedFace order)) : E × Bool :=
  ((R.enumeratedPosition order d).edge, (R.enumeratedPosition order d).side)

/-- No original side occurs twice among the computed facial walks. -/
theorem enumeratedSide_injective : Function.Injective (R.enumeratedSide order) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ heq
  have hflag := Flag.eq_or_eq_along (R.enumeratedPosition order ⟨i, p⟩)
    (R.enumeratedPosition order ⟨j, q⟩) heq
  have hface : R.faceOf (R.enumeratedRoot order i) = R.faceOf (R.enumeratedRoot order j) := by
    rw [← R.faceOf_enumeratedPosition order ⟨i, p⟩,
      ← R.faceOf_enumeratedPosition order ⟨j, q⟩]
    rcases hflag with h | h
    · exact congrArg R.faceOf h
    · rw [h, R.faceOf_along]
  have hij := R.enumeratedFace_injective order hface
  subst j
  rcases hflag with h | h
  · have hp : p.val < Function.minimalPeriod R.rotation (R.enumeratedRoot order i) := by
      simpa only [R.enumeratedFace_length, periodLength_eq] using p.isLt
    have hq : q.val < Function.minimalPeriod R.rotation (R.enumeratedRoot order i) := by
      simpa only [R.enumeratedFace_length, periodLength_eq] using q.isLt
    have hpq : p = q := Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hp hq).mp h)
    subst q
    rfl
  · have hp := R.enumeratedPosition_sameCycle order ⟨i, p⟩
    have hq := R.enumeratedPosition_sameCycle order ⟨i, q⟩
    have hh := hq.symm.trans hp
    rw [h] at hh
    exact False.elim (R.not_sameCycle_along _ hh)

/-- Every original edge side occurs in one computed face. -/
theorem enumeratedSide_surjective (horder : ∀ x : Flag E, x ∈ order) :
    Function.Surjective (R.enumeratedSide order) := by
  rintro ⟨e, s⟩
  let x : Flag E := ⟨e, s, false⟩
  obtain ⟨i, hi⟩ := R.enumeratedFace_surjective order horder (R.faceOf x)
  have hs : R.SameFace (R.enumeratedRoot order i) x := Quotient.exact hi
  have build : ∀ y : Flag E, R.rotation.SameCycle (R.enumeratedRoot order i) y →
      ∃ d : Occurrence (R.enumeratedFace order), R.enumeratedPosition order d = y := by
    intro y hy
    obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
    let p := Function.minimalPeriod R.rotation (R.enumeratedRoot order i)
    have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts
      (R.rotation.injective.mem_periodicPts (R.enumeratedRoot order i))
    let j : Fin (R.enumeratedFace order i).boundary.length :=
      ⟨n % p, by rw [R.enumeratedFace_length, periodLength_eq]; exact Nat.mod_lt _ hp⟩
    refine ⟨⟨i, j⟩, ?_⟩
    change (R.rotation : Flag E → Flag E)^[n % p] (R.enumeratedRoot order i) = y
    rw [Function.iterate_mod_minimalPeriod_eq]
    simpa only [Equiv.Perm.coe_pow] using hn
  rcases hs with hs | hs
  · obtain ⟨d, hd⟩ := build x hs
    exact ⟨d, by simp only [enumeratedSide, hd]; rfl⟩
  · obtain ⟨d, hd⟩ := build (along x) hs
    exact ⟨d, by simp only [enumeratedSide, hd]; rfl⟩

/-- Proof-level certification that the computed faces pair exactly the actual
original edge sides. The executable output remains the computed boundary list. -/
noncomputable def enumeratedSidePairing (horder : ∀ x : Flag E, x ∈ order) :
    SidePairing (R.enumeratedFace order) where
  pairing := Equiv.ofBijective (R.enumeratedSide order)
    ⟨R.enumeratedSide_injective order, R.enumeratedSide_surjective order horder⟩
  edge_eq := R.enumeratedFace_edgeAt order

@[simp] theorem enumeratedSidePairing_startFlag (horder : ∀ x : Flag E, x ∈ order)
    (d : Occurrence (R.enumeratedFace order)) :
    (R.enumeratedSidePairing order horder).startFlag d = R.enumeratedPosition order d := by
  change (⟨(R.enumeratedPosition order d).edge, (R.enumeratedPosition order d).side,
    !((R.enumeratedFace order d.1).boundary.forwardAt d.2)⟩ : Flag E) = _
  rw [R.enumeratedFace_forwardAt]
  simp only [Bool.not_not]

@[simp] theorem enumeratedSidePairing_endFlag (horder : ∀ x : Flag E, x ∈ order)
    (d : Occurrence (R.enumeratedFace order)) :
    (R.enumeratedSidePairing order horder).endFlag d = along (R.enumeratedPosition order d) := by
  change (⟨(R.enumeratedPosition order d).edge, (R.enumeratedPosition order d).side,
    (R.enumeratedFace order d.1).boundary.forwardAt d.2⟩ : Flag E) = _
  rw [R.enumeratedFace_forwardAt]
  rfl

/-- Consecutive computed positions follow the original boundary permutation,
including the final return to the first position. -/
theorem enumeratedPosition_faceNext (d : Occurrence (R.enumeratedFace order)) :
    R.enumeratedPosition order (faceNext d) = R.rotation (R.enumeratedPosition order d) := by
  change (R.rotation : Flag E → Flag E)^[(finRotate
    (R.enumeratedFace order d.1).boundary.length d.2).val] (R.enumeratedRoot order d.1) =
      R.rotation ((R.rotation : Flag E → Flag E)^[d.2.val] (R.enumeratedRoot order d.1))
  apply iterate_finRotate
  rw [R.enumeratedFace_length, periodLength_eq]
  exact Function.iterate_minimalPeriod

/-- Deterministic enumeration recovers the original corner matching exactly. -/
theorem enumeratedSidePairing_corner (horder : ∀ x : Flag E, x ∈ order) (x : Flag E) :
    (R.enumeratedSidePairing order horder).corner x = R.corner x := by
  obtain ⟨⟨d, t⟩, rfl⟩ := (R.enumeratedSidePairing order horder).flagEquiv.surjective x
  cases t
  · rw [(R.enumeratedSidePairing order horder).flagEquiv_false,
      (R.enumeratedSidePairing order horder).corner_startFlag,
      R.enumeratedSidePairing_startFlag, R.enumeratedSidePairing_endFlag]
    have h := R.enumeratedPosition_faceNext order (facePrev d)
    simp only [facePrev, Equiv.apply_symm_apply] at h
    rw [h]
    change along (R.enumeratedPosition order (facePrev d)) =
      R.corner (R.corner (along (R.enumeratedPosition order (facePrev d))))
    rw [R.involutive]
  · rw [(R.enumeratedSidePairing order horder).flagEquiv_true,
      (R.enumeratedSidePairing order horder).corner_endFlag,
      R.enumeratedSidePairing_endFlag, R.enumeratedSidePairing_startFlag,
      R.enumeratedPosition_faceNext]
    rfl

/-- The computed facial label of a flag is its original quotient circle. -/
@[simp] theorem enumeratedSidePairing_flagFace (horder : ∀ x : Flag E, x ∈ order) (x : Flag E) :
    R.enumeratedFaceEquiv order horder ((R.enumeratedSidePairing order horder).flagFace x) =
      R.faceOf x := by
  obtain ⟨⟨d, t⟩, rfl⟩ := (R.enumeratedSidePairing order horder).flagEquiv.surjective x
  cases t
  · rw [(R.enumeratedSidePairing order horder).flagEquiv_false,
      (R.enumeratedSidePairing order horder).flagFace_startFlag,
      R.enumeratedSidePairing_startFlag, R.faceOf_enumeratedPosition]
    rfl
  · rw [(R.enumeratedSidePairing order horder).flagEquiv_true,
      (R.enumeratedSidePairing order horder).flagFace_endFlag,
      R.enumeratedSidePairing_endFlag, R.faceOf_along, R.faceOf_enumeratedPosition]
    rfl

/-- The computed facial correspondence preserves actual edge-side incidence. -/
@[simp] theorem enumeratedSidePairing_face (horder : ∀ x : Flag E, x ∈ order) (e : E) (b : Bool) :
    R.enumeratedFaceEquiv order horder ((R.enumeratedSidePairing order horder).face e b) =
      R.sidePairing.face e b := by
  rw [R.sidePairing_face]
  exact R.enumeratedSidePairing_flagFace order horder ⟨e, b, false⟩

/-- The deterministic facial correspondence preserves every boundary length,
including repeated edge labels and reversed chosen traversal directions. -/
theorem enumeratedFaceEquiv_length (horder : ∀ x : Flag E, x ∈ order)
    (i : R.EnumeratedIndex order) :
    (R.enumeratedFace order i).boundary.length =
      (R.faces (R.enumeratedFaceEquiv order horder i)).boundary.length := by
  classical
  rw [← (R.enumeratedSidePairing order horder).face_fiber_size, ← R.sidePairing.face_fiber_size]
  unfold RegionParity.fiberSize
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← R.enumeratedSidePairing_face order horder s.1 s.2]
  exact (R.enumeratedFaceEquiv order horder).injective.eq_iff.symm

/-- Deterministic enumeration preserves the actual odd-face count. -/
theorem enumeratedFaceEquiv_odd_count (horder : ∀ x : Flag E, x ∈ order) :
    Fintype.card {i : R.EnumeratedIndex order // Odd (R.enumeratedFace order i).boundary.length} =
      Fintype.card {f : R.FaceIndex // Odd (R.faces f).boundary.length} := by
  classical
  exact Fintype.card_congr ((R.enumeratedFaceEquiv order horder).subtypeEquiv fun i => by
    rw [R.enumeratedFaceEquiv_length order horder])

/-- Every actual side is emitted once, so the total computed boundary size is
linear even though the simple marking implementation has a cubic scan bound. -/
theorem enumerated_total_length (horder : ∀ x : Flag E, x ∈ order) :
    (∑ i : R.EnumeratedIndex order, (R.enumeratedFace order i).boundary.length) =
      2 * Fintype.card E :=
  (R.enumeratedSidePairing order horder).total_face_length

/-- Original connected local links certify those of the computed faces. -/
theorem enumeratedSidePairing_vertexLinks (horder : ∀ x : Flag E, x ∈ order)
    (hlinks : R.VertexLinks) : (R.enumeratedSidePairing order horder).VertexLinks := by
  intro x y hxy
  apply Relation.ReflTransGen.mono ?_ x y (hlinks x y hxy)
  intro a b hab
  cases hab with
  | across =>
      rcases a with ⟨e, s, t⟩
      exact SidePairing.LinkStep.across e s t
  | corner =>
      have h := (R.enumeratedSidePairing order horder).linkStep_corner a
      rwa [R.enumeratedSidePairing_corner] at h

/-- The finite computed faces form an actual cellular embedding of the
original corner system, with exactly the original graph endpoints. -/
noncomputable def enumeratedEmbedding (horder : ∀ x : Flag E, x ∈ order)
    (hlinks : R.VertexLinks) (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v)
    (hne : Nonempty E) : CellularEmbedding left right (R.EnumeratedIndex order) where
  faces := R.enumeratedFace order
  face_present := by
    obtain ⟨e⟩ := hne
    obtain ⟨i, _⟩ := R.enumeratedFace_surjective order horder (R.faceOf ⟨e, false, false⟩)
    exact ⟨i⟩
  sides := R.enumeratedSidePairing order horder
  face_nonempty := R.enumeratedFace_positive order
  vertex_present := hvertices
  vertex_links := R.enumeratedSidePairing_vertexLinks order horder hlinks

/-- Alternating rows computed from the output boundary walks are literally
the actual even-face matrix of the certified embedding. -/
theorem enumeratedEmbedding_matrix (horder : ∀ x : Flag E, x ∈ order)
    (hlinks : R.VertexLinks) (hvertices : ∀ v, ∃ x : Flag E, x.vertex left right = v)
    (hne : Nonempty E) :
    Faces.matrix (R.enumeratedEmbedding order horder hlinks hvertices hne).faces =
      Faces.matrix (R.enumeratedFace order) := rfl

end Ribbon
end WeightedMIS.EmbeddingFaces
