module

public import WeightedMIS.ComputedComponents
public import WeightedMIS.ComputedRestriction
public import WeightedMIS.RibbonRelabeling
public import WeightedMIS.GraphRelabeling
public import WeightedMIS.ComponentAssembly

/-!
# Computed ribbon geometry of finite indexed components

The actual computed edge list decides retention. Bounded corner splicing and
numeric relabelling then give precisely the graph indexed by the computed
component lists, without quotient representatives in the executed code.
-/

@[expose] public section

namespace WeightedMIS.ComputedComponents

open EmbeddingFaces Incidence

variable {n m : ℕ} (left right : Fin m → Fin n) (root : Fin n)

/-- The edge-index equivalence to the explicitly computed retention predicate. -/
def retainedEdgeEquiv : Fin (edges left right root).length ≃ {e // e ∈ edges left right root} :=
  List.Nodup.getEquiv _ (edges_nodup left right root)

@[simp] theorem retainedEdgeEquiv_val (e : Fin (edges left right root).length) :
    (retainedEdgeEquiv left right root e).val = (edgeEquiv left right root e).val := rfl

/-- The actual corner system of the explicitly indexed component. -/
def componentRibbon (R : Ribbon left right) : Ribbon (localLeft left right root) (localRight left right root) :=
  (R.computedRestrict (fun e => e ∈ edges left right root)).relabel
    (retainedEdgeEquiv left right root) (fun v => (vertexEquiv left right root v).val)
    (Subtype.val_injective.comp (vertexEquiv left right root).injective)
    (localLeft left right root) (localRight left right root)
    (fun e => congrArg Subtype.val (vertexEquiv_localLeft left right root e))
    (fun e => congrArg Subtype.val (vertexEquiv_localRight left right root e))

/-- Computed numeric component coordinates preserve actual all-half optimality. -/
theorem local_half_optimal (weights : Fin n → ℚ)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2)) :
    Persistence.Optimal (EdgeTransport.Adj (localLeft left right root) (localRight left right root))
      (fun v => weights (vertexEquiv left right root v).val) (fun _ => 1 / 2) := by
  classical
  exact GraphRelabeling.half_optimal_pullback (vertexEquiv left right root) _ _ (local_adj left right root)
    (fun v : ComponentVertex left right (componentOf left right root) => weights v.val)
    (ComponentAssembly.component_half_optimal left right weights ho (componentOf left right root))

/-- A component's computed vertex indices are exactly the fiber of its fixed
numeric representative. Both directions use the same supplied list lookup. -/
def representativeFiberEquiv (hfix : representative left right root = root) :
    Fin (vertices left right root).length ≃ {v // representative left right v = root} :=
  (vertexEquiv left right root).trans (Equiv.subtypeEquivRight (fun v => by
    rw [componentOf_eq_iff, ← representative_eq_iff, hfix]))

@[simp] theorem representativeFiberEquiv_val (hfix : representative left right root = root)
    (v : Fin (vertices left right root).length) :
    (representativeFiberEquiv left right root hfix v).val = (vertexEquiv left right root v).val := rfl

/-- The representative fiber has exactly the computed component adjacency. -/
theorem representativeFiber_adj (hfix : representative left right root = root)
    (u v : Fin (vertices left right root).length) :
    EdgeTransport.Adj (localLeft left right root) (localRight left right root) u v ↔
      EdgeTransport.Adj left right
        (representativeFiberEquiv left right root hfix u).val
        (representativeFiberEquiv left right root hfix v).val :=
  (local_adj left right root u v).trans (ComponentAssembly.component_adj_iff left right _ _ _)

end WeightedMIS.ComputedComponents
