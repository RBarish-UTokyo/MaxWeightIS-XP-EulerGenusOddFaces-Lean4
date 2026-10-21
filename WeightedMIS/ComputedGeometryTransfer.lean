module

public import WeightedMIS.ComputedEmbeddedMatrices
public import WeightedMIS.RibbonFaceRelabeling
public import WeightedMIS.DeletionParameters
public import WeightedMIS.EndpointRelabeling

/-!
# Parameter bounds for actually computed matrices after geometric relabelling

The hypotheses below are actual bijections of retained edge and vertex labels,
with endpoint and corner identities. They imply the facial, Euler-genus, and
orientation invariants; no matrix rank or numerical parameter estimate is
assumed. This bridges finite numeric algorithm indices to geometric deletion.
-/

@[expose] public section

namespace WeightedMIS.ComputedEmbeddedMatrices

open EmbeddingFaces Incidence

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    {left right : E → V} (M : CellularEmbedding left right F)
    {n m : ℕ} {leftH rightH : Fin m → Fin n} (S : Ribbon leftH rightH)
    (keep : E → Prop) [DecidablePred keep]
    (ee : Fin m ≃ {e : E // keep e})
    (ev : Fin n ≃ Ribbon.ActiveVertex (left := left) (right := right) keep)
    (hl : ∀ e, ev (leftH e) = Ribbon.activeLeft keep (ee e))
    (hr : ∀ e, ev (rightH e) = Ribbon.activeRight keep (ee e))
    (hcorner : ∀ x, Flag.mapEquiv ee (S.corner x) =
      (M.sides.toRibbon.activeRestrict keep).corner (Flag.mapEquiv ee x))

include hl hr hcorner in
/-- The coordinate count in the actual computed matrix list satisfies the
original surface bound, and the same output satisfies its orientable sharpening. -/
theorem globalRows_deleted_parameter_bound
    (hcM : Connected left right) (hc : Connected leftH rightH)
    (hnb : ¬ Bipartite leftH rightH) :
    (globalRows S).length ≤ Parameters.exponent M.eulerGenus (EmbeddedReduction.oddFaceCount M) ∧
      ∀ O : M.sides.Orientation, (globalRows S).length ≤
        Parameters.orientableExponent M.eulerGenus (EmbeddedReduction.oddFaceCount M) := by
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
  have hm := M.cappedDeletion_parameter_mono keep hne hcM hcH
  change H.eulerGenus ≤ M.eulerGenus ∧
    H.eulerGenus + EmbeddedReduction.oddFaceCount H ≤
      M.eulerGenus + EmbeddedReduction.oddFaceCount M at hm
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
