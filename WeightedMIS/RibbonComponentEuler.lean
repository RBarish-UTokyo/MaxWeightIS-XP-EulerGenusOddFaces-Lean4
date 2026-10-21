module

public import WeightedMIS.RibbonComponentFaces
public import WeightedMIS.EmbeddingDual

/-!
# Euler counting for actual ribbon components

Summing the proved cellular Euler identities and the explicit cell partitions
includes isolated vertex disks. The deleted-edge dual therefore has genuine
complement-region components with the correct cell counts.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open scoped BigOperators
open Incidence

attribute [local instance] Classical.propDecidable

namespace Ribbon

variable {V E : Type*} [Fintype V] [Fintype E] {left right : E → V} (R : Ribbon left right)

/-- Summing actual component genera gives the Euler identity of the whole
ribbon, with isolated vertices represented by their one disk boundary. -/
theorem component_euler_identity (hlinks : R.VertexLinks) :
    (∑ q, (R.cappedComponent hlinks q).genus) + Fintype.card V +
      Fintype.card R.FaceIndex + Fintype.card (IsolatedVertex left right) =
        Fintype.card E + 2 * Fintype.card (Component left right) := by
  classical
  have hv := Fintype.card_congr (vertexPartition left right)
  have he := Fintype.card_congr (edgePartition left right)
  have hf := Fintype.card_congr R.cappedFacePartition
  simp only [Fintype.card_sigma, Fintype.card_sum] at hv he hf
  have h := congrArg (fun f : Component left right → ℕ => ∑ q, f q)
    (funext fun q => (R.cappedComponent hlinks q).euler_identity)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  omega

/-- The nonnegative component genera imply the corresponding exact-cell Euler
inequality for every finite ribbon with connected local links. -/
theorem component_euler_inequality (hlinks : R.VertexLinks) :
    Fintype.card V + Fintype.card R.FaceIndex + Fintype.card (IsolatedVertex left right) ≤
      Fintype.card E + 2 * Fintype.card (Component left right) := by
  have h := R.component_euler_identity hlinks
  omega

/-- The omitted vertex labels are precisely the isolated vertices of the
retained endpoint graph, giving the actual vertex-cell partition. -/
noncomputable def retainedOmittedVertexPartition (keep : E → Prop) :
    V ≃ ActiveVertex (left := left) (right := right) keep ⊕
      IsolatedVertex (fun e : {e : E // keep e} => left e.val) (fun e => right e.val) :=
  (Equiv.sumCompl (fun v => ∃ e : E, keep e ∧ (left e = v ∨ right e = v))).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight fun v => by
      apply not_congr
      constructor
      · rintro ⟨e, he, hv⟩
        exact ⟨⟨e, he⟩, hv⟩
      · rintro ⟨⟨e, he⟩, hv⟩
        exact ⟨e, he, hv⟩))

end Ribbon

namespace SidePairing

variable {V E F : Type*} [Fintype E] {left right : E → V}
    {faces : F → Faces.Face left right} (P : SidePairing faces)

/-- The actual deleted-edge dual, keeping every original face label so that
regions consisting of a single untouched face remain as isolated disks. -/
noncomputable def deletedDual (keep : E → Prop) :
    Ribbon (fun e : {e : E // ¬keep e} => P.face e.val false)
      (fun e => P.face e.val true) := P.dualRibbon.restrict (fun e => ¬keep e)

/-- Deleting the retained primal bands in the dual preserves its connected
local vertex links, which came from the original actual facial walks. -/
theorem deletedDual_vertexLinks (keep : E → Prop) : (P.deletedDual keep).VertexLinks :=
  P.dualRibbon.restrict_vertexLinks _ P.dual_vertexLinks

/-- The complement regions are the actual walk-connected components of the
deleted-edge dual graph, including isolated original faces. -/
abbrev ComplementRegion (keep : E → Prop) :=
  Component (fun e : {e : E // ¬keep e} => P.face e.val false)
    (fun e => P.face e.val true)

/-- The complement region incident to an original polygon face. -/
def originalFaceRegion (keep : E → Prop) (f : F) : P.ComplementRegion keep :=
  componentOf (fun e : {e : E // ¬keep e} => P.face e.val false)
    (fun e => P.face e.val true) f

omit [Fintype E] in
/-- The two sides of every deleted edge belong to the same concrete region. -/
theorem deleted_same_region (keep : E → Prop) (e : E) (he : ¬keep e) :
    P.originalFaceRegion keep (P.face e false) = P.originalFaceRegion keep (P.face e true) :=
  componentOf_endpoints (fun e : {e : E // ¬keep e} => P.face e.val false)
    (fun e => P.face e.val true) ⟨e, he⟩

/-- Every original face belongs to exactly one concrete complement region. -/
def originalFacePartition (keep : E → Prop) : F ≃
    ((q : P.ComplementRegion keep) ×
      ComponentVertex (fun e : {e : E // ¬keep e} => P.face e.val false)
        (fun e => P.face e.val true) q) := vertexPartition _ _

/-- Every original edge is either retained or one deleted dual edge in one
concrete complement region. -/
noncomputable def retainedDeletedEdgePartition (keep : E → Prop) :
    E ≃ {e : E // keep e} ⊕
      ((q : P.ComplementRegion keep) ×
        ComponentEdge (fun e : {e : E // ¬keep e} => P.face e.val false)
          (fun e => P.face e.val true) q) :=
  (Equiv.sumCompl keep).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (edgePartition _ _))

end SidePairing
end WeightedMIS.EmbeddingFaces
