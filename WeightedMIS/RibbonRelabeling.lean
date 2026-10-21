module

public import WeightedMIS.RibbonLinks

/-!
# Computable ribbon relabelling

An actual bijection of edge labels transports flags and corners. Vertex labels
need only embed injectively, allowing unused labels to disappear after edge
deletion. Every operation uses the supplied finite indexing functions.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

namespace Flag

variable {D E : Type*}

/-- Relabel edge IDs while preserving both flag bits. -/
def mapEquiv (e : D ≃ E) : Flag D ≃ Flag E where
  toFun x := ⟨e x.edge, x.side, x.endpoint⟩
  invFun x := ⟨e.symm x.edge, x.side, x.endpoint⟩
  left_inv x := by cases x; simp
  right_inv x := by cases x; simp

@[simp] theorem mapEquiv_across (e : D ≃ E) (x : Flag D) :
    mapEquiv e (SidePairing.across x) = SidePairing.across (mapEquiv e x) := rfl

/-- Endpoint commutation is exactly vertex-label commutation on flags. -/
theorem mapEquiv_vertex {U V : Type*} (ee : D ≃ E) (f : U → V)
    (leftU rightU : D → U) (leftV rightV : E → V)
    (hl : ∀ e, f (leftU e) = leftV (ee e)) (hr : ∀ e, f (rightU e) = rightV (ee e))
    (x : Flag D) :
    f (x.vertex leftU rightU) = (mapEquiv ee x).vertex leftV rightV := by
  cases ht : x.endpoint <;> simp [vertex, mapEquiv, ht, hl, hr]

end Flag

namespace Ribbon

variable {U V D E : Type*} {left right : E → V} (R : Ribbon left right)
    (ee : D ≃ E) (f : U → V) (hf : Function.Injective f)
    (leftU rightU : D → U)
    (hl : ∀ e, f (leftU e) = left (ee e))
    (hr : ∀ e, f (rightU e) = right (ee e))

/-- Transport the actual corner matching through supplied numeric edge IDs. -/
def relabelCorner : Equiv.Perm (Flag D) :=
  (Flag.mapEquiv ee).trans (R.corner.trans (Flag.mapEquiv ee).symm)

@[simp] theorem relabelCorner_map (x : Flag D) :
    Flag.mapEquiv ee (R.relabelCorner ee x) = R.corner (Flag.mapEquiv ee x) := by
  simp only [relabelCorner, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- An executable finite relabelling of the same edge-band geometry. -/
def relabel : Ribbon leftU rightU where
  corner := R.relabelCorner ee
  involutive := by
    intro x
    apply (Flag.mapEquiv ee).injective
    rw [relabelCorner_map, relabelCorner_map, R.involutive]
  ne_self := by
    intro x he
    apply R.ne_self (Flag.mapEquiv ee x)
    simpa only [relabelCorner_map] using congrArg (Flag.mapEquiv ee) he
  vertex := by
    intro x
    apply hf
    rw [Flag.mapEquiv_vertex ee f leftU rightU left right hl hr,
      Flag.mapEquiv_vertex ee f leftU rightU left right hl hr,
      relabelCorner_map, R.vertex]

/-- Relabelling does not alter connectedness of an actual vertex link. -/
theorem relabel_vertexLinks (hlinks : R.VertexLinks) :
    (R.relabel ee f hf leftU rightU hl hr).VertexLinks := by
  intro x y hxy
  have hxy' : (Flag.mapEquiv ee x).vertex left right = (Flag.mapEquiv ee y).vertex left right := by
    rw [← Flag.mapEquiv_vertex ee f leftU rightU left right hl hr,
      ← Flag.mapEquiv_vertex ee f leftU rightU left right hl hr, hxy]
  have hh := hlinks _ _ hxy'
  have hmap : ∀ a b, R.LinkStep a b →
      (R.relabel ee f hf leftU rightU hl hr).LinkStep ((Flag.mapEquiv ee).symm a)
        ((Flag.mapEquiv ee).symm b) := by
    intro a b hab
    cases hab with
    | across => exact .across _
    | corner =>
      have h := LinkStep.corner (R := R.relabel ee f hf leftU rightU hl hr) ((Flag.mapEquiv ee).symm a)
      simpa only [relabel, relabelCorner, Equiv.trans_apply, Equiv.apply_symm_apply] using h
  have hh' := Relation.ReflTransGen.lift (Flag.mapEquiv ee).symm hmap _ _ hh
  simpa only [Function.onFun, Equiv.symm_apply_apply] using hh'

end Ribbon
end WeightedMIS.EmbeddingFaces
