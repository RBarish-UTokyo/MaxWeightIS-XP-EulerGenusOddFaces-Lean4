module

public import WeightedMIS.RibbonRelabeling
public import WeightedMIS.OriginalFaces
public import WeightedMIS.RibbonOrientation

/-!
# Facial invariance under actual edge relabelling

A bijection of edge labels that commutes with the actual corner matchings
induces a bijection of the traced boundary circles. Counting their edge sides
proves that every boundary length, including all repetitions, is preserved.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.Ribbon

open SidePairing

variable {U V D E : Type*} [Fintype D] [Fintype E]
    {leftU rightU : D → U} {leftV rightV : E → V}
    (S : Ribbon leftU rightU) (R : Ribbon leftV rightV) (ee : D ≃ E)
    (hc : ∀ x, Flag.mapEquiv ee (S.corner x) = R.corner (Flag.mapEquiv ee x))

include hc in
theorem map_rotation (x : Flag D) :
    Flag.mapEquiv ee (S.rotation x) = R.rotation (Flag.mapEquiv ee x) := by
  exact hc (along x)

include hc in
theorem map_iterate_rotation (k : ℕ) (x : Flag D) :
    Flag.mapEquiv ee ((S.rotation : Flag D → Flag D)^[k] x) =
      (R.rotation : Flag E → Flag E)^[k] (Flag.mapEquiv ee x) := by
  have h : Function.Semiconj (Flag.mapEquiv ee) S.rotation R.rotation :=
    map_rotation S R ee hc
  exact h.iterate_right k x

include hc in
theorem sameCycle_map_iff (x y : Flag D) :
    S.rotation.SameCycle x y ↔
      R.rotation.SameCycle (Flag.mapEquiv ee x) (Flag.mapEquiv ee y) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    refine ⟨(k : ℤ), ?_⟩
    simpa only [zpow_natCast, Equiv.Perm.coe_pow, map_iterate_rotation S R ee hc] using
      congrArg (Flag.mapEquiv ee) hk
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    refine ⟨(k : ℤ), ?_⟩
    apply (Flag.mapEquiv ee).injective
    simpa only [zpow_natCast, Equiv.Perm.coe_pow, map_iterate_rotation S R ee hc] using hk

include hc in
theorem sameFace_map_iff (x y : Flag D) :
    S.SameFace x y ↔ R.SameFace (Flag.mapEquiv ee x) (Flag.mapEquiv ee y) := by
  change (_ ∨ _) ↔ (_ ∨ _)
  rw [sameCycle_map_iff S R ee hc x y, sameCycle_map_iff S R ee hc x (along y)]
  rfl

/-- The facial correspondence induced by the supplied actual corner conjugacy. -/
def edgeFaceEquiv : S.FaceIndex ≃ R.FaceIndex :=
  Quotient.congr (Flag.mapEquiv ee) (sameFace_map_iff S R ee hc)

@[simp] theorem edgeFaceEquiv_faceOf (x : Flag D) :
    edgeFaceEquiv S R ee hc (S.faceOf x) = R.faceOf (Flag.mapEquiv ee x) := rfl

@[simp] theorem edgeFaceEquiv_side (e : D) (b : Bool) :
    edgeFaceEquiv S R ee hc (S.sidePairing.face e b) = R.sidePairing.face (ee e) b := by
  rw [S.sidePairing_face, edgeFaceEquiv_faceOf, R.sidePairing_face]
  rfl

/-- Each exact facial boundary length survives edge relabelling. -/
theorem edgeFaceEquiv_length (f : S.FaceIndex) :
    (S.faces f).boundary.length =
      (R.faces (edgeFaceEquiv S R ee hc f)).boundary.length := by
  classical
  rw [← S.sidePairing.face_fiber_size, ← R.sidePairing.face_fiber_size]
  have h := Fintype.card_congr ((ee.prodCongr (Equiv.refl Bool)).subtypeEquiv
    (p := fun s => S.sidePairing.face s.1 s.2 = f)
    (q := fun s => R.sidePairing.face s.1 s.2 = edgeFaceEquiv S R ee hc f)
    (fun s => by
      change S.sidePairing.face s.1 s.2 = f ↔
        R.sidePairing.face (ee s.1) s.2 = edgeFaceEquiv S R ee hc f
      rw [← edgeFaceEquiv_side S R ee hc]
      exact (edgeFaceEquiv S R ee hc).injective.eq_iff.symm))
  simpa only [Fintype.card_subtype, RegionParity.fiberSize] using h

include hc in
/-- The odd facial boundary count survives the same geometric relabelling. -/
theorem edgeFaceEquiv_odd_count :
    Fintype.card {f : S.FaceIndex // Odd (S.faces f).boundary.length} =
      Fintype.card {f : R.FaceIndex // Odd (R.faces f).boundary.length} := by
  classical
  exact Fintype.card_congr ((edgeFaceEquiv S R ee hc).subtypeEquiv fun f => by
    rw [edgeFaceEquiv_length S R ee hc])

/-- Coherent flag signs pull back through the same actual corner conjugacy. -/
def edgeFlagOrientation (O : R.FlagOrientation) : S.FlagOrientation where
  sign x := O.sign (Flag.mapEquiv ee x)
  signs x := O.signs _
  across x := by rw [Flag.mapEquiv_across, O.across]
  corner x := by rw [hc, O.corner]
  along x := by simpa only [Flag.mapEquiv, along, Equiv.coe_fn_mk] using O.along (Flag.mapEquiv ee x)

/-- The corner permutation determines all fields of a ribbon. -/
theorem eq_of_corner_eq {R S : Ribbon leftV rightV} (h : R.corner = S.corner) : R = S := by
  cases R
  cases S
  cases h
  rfl

include hc in
/-- An actual conjugacy preserves the connected links at corresponding
vertices, including embeddings into a larger vertex-label type. -/
theorem edge_vertexLinks (f : U → V) (hf : Function.Injective f)
    (hl : ∀ e, f (leftU e) = leftV (ee e))
    (hr : ∀ e, f (rightU e) = rightV (ee e)) (hlinks : R.VertexLinks) : S.VertexLinks := by
  have heq : S = R.relabel ee f hf leftU rightU hl hr := by
    apply eq_of_corner_eq
    apply Equiv.ext
    intro x
    apply (Flag.mapEquiv ee).injective
    exact (hc x).trans (R.relabelCorner_map ee x).symm
  rw [heq]
  exact R.relabel_vertexLinks ee f hf leftU rightU hl hr hlinks

/-- Reconstructing facial polygons leaves the actual corner ribbon unchanged. -/
@[simp] theorem sidePairing_toRibbon_eq : R.sidePairing.toRibbon = R :=
  eq_of_corner_eq (Equiv.ext R.sidePairing_corner)

end WeightedMIS.EmbeddingFaces.Ribbon
