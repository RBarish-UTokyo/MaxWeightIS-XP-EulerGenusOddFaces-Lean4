module

public import WeightedMIS.ComputedRestriction
public import WeightedMIS.PermutationRestriction
public import WeightedMIS.RibbonComponents
public import WeightedMIS.ComputedComponentRibbon
public import WeightedMIS.RibbonFaceRelabeling

/-!
# Computed restriction on a closed collection of graph components

When an edge predicate is preserved by the actual corners, its bounded
restriction makes no splices. In particular, the computed numeric component
ribbon has exactly the inherited component corners, so all traced face lengths
are those of the genuine mathematical component construction.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.Ribbon

open SidePairing

variable {V E : Type*} [Fintype E] {left right : E → V} (R : Ribbon left right)
    (keep : E → Prop) [DecidablePred keep]

/-- Expose the exact positive first-return trace of a computed corner. -/
theorem computedRestrict_corner_val (x : Flag {e : E // keep e}) :
    (Flag.retainedEquiv keep ((R.computedRestrict keep).corner x)).val =
      across (PermutationDeletion.firstReturn (R.corner.trans across)
        (fun y => keep y.edge) (Flag.retainedEquiv keep x)).val := by
  change (Flag.retainedEquiv keep ((R.computedRestrictedCorner keep) x)).val = _
  simp only [computedRestrictedCorner, Equiv.trans_apply, Equiv.apply_symm_apply,
    PermutationDeletion.computedFirstReturn_eq]
  rfl

/-- Retaining a corner-closed set only changes labels. -/
theorem computedRestrict_corner_closed
    (hclosed : ∀ x : Flag E, keep x.edge → keep (R.corner x).edge)
    (x : Flag {e : E // keep e}) :
    (Flag.retainedEquiv keep ((R.computedRestrict keep).corner x)).val =
      R.corner (Flag.retainedEquiv keep x).val := by
  rw [computedRestrict_corner_val,
    PermutationDeletion.firstReturn_apply_of_mem (h := hclosed _ x.edge.property)]
  exact across_across _

end WeightedMIS.EmbeddingFaces.Ribbon

namespace WeightedMIS.ComputedComponents

open EmbeddingFaces Incidence

variable {n m : ℕ} (left right : Fin m → Fin n) (root : Fin n)

/-- The computed component-edge predicate is closed under all actual corners. -/
theorem edges_corner_closed (R : Ribbon left right) (x : EmbeddingFaces.Flag (Fin m))
    (hx : x.edge ∈ edges left right root) : (R.corner x).edge ∈ edges left right root := by
  rw [mem_edges, R.corner_component]
  exact (mem_edges left right root x.edge).mp hx

/-- The numeric component's corner matching is exactly the actual restricted
matching under its computed edge-ID equivalence. -/
theorem componentRibbon_corner_map (R : Ribbon left right)
    (x : EmbeddingFaces.Flag (Fin (edges left right root).length)) :
    Flag.mapEquiv (edgeEquiv left right root) ((componentRibbon left right root R).corner x) =
      (R.componentRibbon (componentOf left right root)).corner
        (Flag.mapEquiv (edgeEquiv left right root) x) := by
  apply Ribbon.componentFlag_injective _
  change _ = Ribbon.componentFlag (R.componentCorner (componentOf left right root)
    (Flag.mapEquiv (edgeEquiv left right root) x))
  rw [Ribbon.componentCorner_coe]
  have h := (R.computedRestrict (fun e => e ∈ edges left right root)).relabelCorner_map
    (retainedEdgeEquiv left right root) x
  have hv := congrArg (fun y => (Flag.retainedEquiv (fun e => e ∈ edges left right root) y).val) h
  rw [R.computedRestrict_corner_closed (fun e => e ∈ edges left right root)
    (edges_corner_closed left right root R)] at hv
  exact hv

end WeightedMIS.ComputedComponents
