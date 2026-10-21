module

public import WeightedMIS.RibbonDeletionRelabeling

/-!
# Deleting from an actually retained drawing

The input ribbon may already be a noncellular or disconnected retained part
of a larger cellular map. A further deletion is transported directly to its
original edge labels using exact first-return composition.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.Ribbon

variable {U V D E : Type*} [Fintype D] [Fintype E]
    {leftU rightU : D → U} {leftV rightV : E → V}
    (drawing : E → Prop) (ee : D ≃ {e : E // drawing e}) (keep : D → Prop)

/-- Original ambient edge labels retained after deleting from the drawing. -/
def drawingKeep : E → Prop := NestedRetention.keep drawing (fun e => keep (ee.symm e))

/-- Actual retained drawing edges and their single-stage ambient labels. -/
def drawingEdgeEquiv : {e : D // keep e} ≃ {e : E // drawingKeep drawing ee keep e} :=
  (ee.subtypeEquiv (p := keep) (q := fun e => keep (ee.symm e))
    (fun _ => by simp only [Equiv.symm_apply_apply])).trans
      (NestedRetention.edgeEquiv drawing (fun e => keep (ee.symm e))).symm

@[simp] theorem drawingEdgeEquiv_val (e : {e : D // keep e}) :
    (drawingEdgeEquiv drawing ee keep e).val = (ee e.val).val := rfl

/-- Exact corner composition through an arbitrary original retained drawing. -/
theorem drawing_restrict_corner_map (S : Ribbon leftU rightU) (R : Ribbon leftV rightV)
    (hcorner : ∀ x, Flag.mapEquiv ee (S.corner x) = (R.restrict drawing).corner (Flag.mapEquiv ee x))
    (x : Flag {e : D // keep e}) :
    Flag.mapEquiv (drawingEdgeEquiv drawing ee keep) ((S.restrict keep).corner x) =
      (R.restrict (drawingKeep drawing ee keep)).corner
        (Flag.mapEquiv (drawingEdgeEquiv drawing ee keep) x) := by
  classical
  let r := fun e : {e : E // drawing e} => keep (ee.symm e)
  let hp : ∀ e, keep e ↔ r (ee e) := fun _ => by simp only [r, Equiv.symm_apply_apply]
  have hc : ∀ x, Flag.mapEquiv ee (S.corner x) =
      (R.computedRestrict drawing).corner (Flag.mapEquiv ee x) := by
    rw [R.computedRestrict_eq]
    exact hcorner
  have h1 := computedRestrict_map S (R.computedRestrict drawing) ee hc keep r hp x
  have h2 := R.computedRestrict_nested drawing r (Flag.mapEquiv (ee.subtypeEquiv hp) x)
  rw [S.computedRestrict_eq] at h1
  rw [R.computedRestrict_eq (NestedRetention.keep drawing r)] at h2
  exact (congrArg (Flag.mapEquiv (NestedRetention.edgeEquiv drawing r).symm) h1).trans h2

end WeightedMIS.EmbeddingFaces.Ribbon
