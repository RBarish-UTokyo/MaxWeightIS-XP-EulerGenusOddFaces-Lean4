module

public import WeightedMIS.ComputedGeometryTransfer
public import WeightedMIS.DrawingParameters

/-!
# Computed-coordinate bounds for arbitrary retained surface drawings

The original drawing may be disconnected or noncellular. Its odd parameter
counts total boundary-length parity per actual complementary region. A cellular
completion supplies only the mathematical witness; no completion data are
arguments of the computed matrix construction.
-/

@[expose] public section

namespace WeightedMIS.ComputedEmbeddedMatrices

open EmbeddingFaces Incidence

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    {left right : E → V} (M : CellularEmbedding left right F)
    {n m : ℕ} {leftH rightH : Fin m → Fin n} (S : Ribbon leftH rightH)
    (drawing keep : E → Prop) [DecidablePred drawing] [DecidablePred keep]
    (ee : Fin m ≃ {e : E // keep e})
    (ev : Fin n ≃ Ribbon.ActiveVertex (left := left) (right := right) keep)
    (hl : ∀ e, ev (leftH e) = Ribbon.activeLeft keep (ee e))
    (hr : ∀ e, ev (rightH e) = Ribbon.activeRight keep (ee e))
    (hcorner : ∀ x, Flag.mapEquiv ee (S.corner x) =
      (M.sides.toRibbon.activeRestrict keep).corner (Flag.mapEquiv ee x))

include hl hr hcorner in
/-- Actual computed coordinates satisfy the original drawing's genus and
region-parity bound, with the corresponding orientable sharpening. -/
theorem globalRows_drawing_parameter_bound (hsub : ∀ e, keep e → drawing e)
    (hcM : Connected left right) (hc : Connected leftH rightH)
    (hnb : ¬ Bipartite leftH rightH) :
    (globalRows S).length ≤ Parameters.exponent M.eulerGenus (M.sides.oddRegionCount drawing) ∧
      ∀ _O : M.sides.Orientation, (globalRows S).length ≤
        Parameters.orientableExponent M.eulerGenus (M.sides.oddRegionCount drawing) := by
  classical
  let T := M.sides.toRibbon.activeRestrict keep
  have hneS : Nonempty (Fin m) := edge_nonempty hnb
  have hne : Nonempty {e : E // keep e} := hneS.map ee
  let H := M.cappedDeletion keep hne
  have hlinks : S.VertexLinks := S.edge_vertexLinks T ee hcorner ev ev.injective hl hr
    (M.sides.toRibbon.activeRestrict_vertexLinks keep (M.sides.toRibbon_vertexLinks M.vertex_links))
  have hvertices : ∀ v : Fin n, ∃ x : EmbeddingFaces.Flag (Fin m), x.vertex leftH rightH = v := by
    intro v
    obtain ⟨e, he | he⟩ := connected_vertex_incident leftH rightH hc hneS v
    · exact ⟨⟨e, false, false⟩, he⟩
    · exact ⟨⟨e, false, true⟩, he⟩
  let K := S.toCellularEmbedding hlinks hvertices hneS
  have hKS : K.sides.toRibbon = S := S.sidePairing_toRibbon_eq
  have hcH : Connected (Ribbon.activeLeft (left := left) (right := right) keep)
      (Ribbon.activeRight keep) := by
    intro u v
    obtain ⟨k, p⟩ := hc (ev.symm u) (ev.symm v)
    refine ⟨k, ?_⟩
    simpa only [Equiv.apply_symm_apply] using relabel_walk ev ee hl hr p
  have hg : K.eulerGenus = H.eulerGenus := by
    have hv := Fintype.card_congr ev
    have he := Fintype.card_congr ee
    have hf := Fintype.card_congr (S.edgeFaceEquiv T ee hcorner)
    change Fintype.card (Fin m) + 2 - (Fintype.card (Fin n) + Fintype.card S.FaceIndex) =
      Fintype.card {e : E // keep e} + 2 -
        (Fintype.card (Ribbon.ActiveVertex (left := left) (right := right) keep) + Fintype.card T.FaceIndex)
    rw [hv, he, hf]
  have hk : EmbeddedReduction.oddFaceCount K = EmbeddedReduction.oddFaceCount H :=
    S.edgeFaceEquiv_odd_count T ee hcorner
  have hm := M.drawing_parameter_mono drawing keep hne hsub hcM hcH
  change H.eulerGenus ≤ M.eulerGenus ∧
    H.eulerGenus + EmbeddedReduction.oddFaceCount H ≤ M.eulerGenus + M.sides.oddRegionCount drawing at hm
  constructor
  · have hb := globalRows_parameter_bound K hc hnb
    rw [hKS, hg, hk] at hb
    unfold Parameters.exponent at *
    omega
  · intro O
    have hO : T.FlagOrientation := O.toFlagOrientation.activeRestrict keep
    have hSK : K.sides.Orientation := (S.edgeFlagOrientation T ee hcorner hO).polygonOrientation
    have hb := globalRows_orientable_bound K hSK hc hnb
    rw [hKS, hg, hk] at hb
    unfold Parameters.orientableExponent at *
    omega

end WeightedMIS.ComputedEmbeddedMatrices
