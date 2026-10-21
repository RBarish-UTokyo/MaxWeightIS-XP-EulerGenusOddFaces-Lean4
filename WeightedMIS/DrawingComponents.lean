module

public import WeightedMIS.NestedRetention

/-!
# Actual residual components of a retained drawing

The original graph may be disconnected. Original vertex labels, including
isolates, are retained. Every nontrivial induced residual component is related
by actual vertex and edge equivalences to its ambient retained-edge labels.
-/

@[expose] public section

namespace WeightedMIS.DrawingComponents

open EmbeddingFaces Incidence

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (left right : E → V) (g : E → Prop) [DecidablePred g]
    (keep : V → Prop) [DecidablePred keep]

abbrev graphLeft (e : {e : E // g e}) : V := left e.val
abbrev graphRight (e : {e : E // g e}) : V := right e.val

abbrev Part := InducedComponents.Part (graphLeft left g) (graphRight right g) keep
abbrev PartVertex (q : Part left right g keep) :=
  InducedComponents.PartVertex (graphLeft left g) (graphRight right g) keep q
abbrev PartEdge (q : Part left right g keep) :=
  InducedComponents.PartEdge (graphLeft left g) (graphRight right g) keep q

/-- Original ambient edge labels in the given actual residual component. -/
def componentKeep (q : Part left right g keep) : E → Prop :=
  NestedRetention.keep g (InducedComponents.componentKeep (graphLeft left g) (graphRight right g) keep q)

/-- Ambient retained edges are exactly the actual residual component edges. -/
def componentEdgeEquiv (q : Part left right g keep) :
    {e : E // componentKeep left right g keep q e} ≃ PartEdge left right g keep q :=
  (NestedRetention.edgeEquiv g _).trans
    (InducedComponents.componentEdgeEquiv (graphLeft left g) (graphRight right g) keep q)

theorem componentKeep_nonempty (q : Part left right g keep)
    (hne : Nonempty (PartEdge left right g keep q)) :
    Nonempty {e : E // componentKeep left right g keep q e} :=
  ⟨(componentEdgeEquiv left right g keep q).symm hne.some⟩

/-- Every selected component edge belongs to the original drawing. -/
theorem componentKeep_sub (q : Part left right g keep) (e : E)
    (he : componentKeep left right g keep q e) : g e := he.1

/-- The active ambient labels are exactly the actual residual component vertices. -/
def componentVertexEquiv (q : Part left right g keep)
    (hne : Nonempty (PartEdge left right g keep q)) :
    Ribbon.ActiveVertex (left := left) (right := right) (componentKeep left right g keep q) ≃
      PartVertex left right g keep q :=
  (NestedRetention.vertexEquiv left right g _).trans
    (InducedComponents.activeComponentEquiv (graphLeft left g) (graphRight right g) keep q hne)

@[simp] theorem componentVertexEquiv_left (q : Part left right g keep)
    (hne : Nonempty (PartEdge left right g keep q))
    (e : {e : E // componentKeep left right g keep q e}) :
    componentVertexEquiv left right g keep q hne
      (Ribbon.activeLeft (left := left) (right := right) _ e) =
    componentLeft (InducedComponents.edgeLeft (graphLeft left g) (graphRight right g) keep)
      (InducedComponents.edgeRight (graphLeft left g) (graphRight right g) keep) q
      (componentEdgeEquiv left right g keep q e) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

@[simp] theorem componentVertexEquiv_right (q : Part left right g keep)
    (hne : Nonempty (PartEdge left right g keep q))
    (e : {e : E // componentKeep left right g keep q e}) :
    componentVertexEquiv left right g keep q hne
      (Ribbon.activeRight (left := left) (right := right) _ e) =
    componentRight (InducedComponents.edgeLeft (graphLeft left g) (graphRight right g) keep)
      (InducedComponents.edgeRight (graphLeft left g) (graphRight right g) keep) q
      (componentEdgeEquiv left right g keep q e) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The ambient retained graph representing this component is connected. -/
theorem component_connected (q : Part left right g keep)
    (hne : Nonempty (PartEdge left right g keep q)) :
    Connected (Ribbon.activeLeft (left := left) (right := right) (componentKeep left right g keep q))
      (Ribbon.activeRight (componentKeep left right g keep q)) :=
  connected_relabel (componentVertexEquiv left right g keep q hne) (componentEdgeEquiv left right g keep q)
    (componentVertexEquiv_left left right g keep q hne) (componentVertexEquiv_right left right g keep q hne)
    (Incidence.component_connected _ _ q)

/-- Actual adjacency is preserved by the component vertex equivalence. -/
theorem component_adj (q : Part left right g keep)
    (hne : Nonempty (PartEdge left right g keep q))
    (u v : Ribbon.ActiveVertex (left := left) (right := right) (componentKeep left right g keep q)) :
    EdgeTransport.Adj (Ribbon.activeLeft (left := left) (right := right) (componentKeep left right g keep q))
      (Ribbon.activeRight (componentKeep left right g keep q)) u v ↔
    EdgeTransport.Adj
      (componentLeft (InducedComponents.edgeLeft (graphLeft left g) (graphRight right g) keep)
        (InducedComponents.edgeRight (graphLeft left g) (graphRight right g) keep) q)
      (componentRight (InducedComponents.edgeLeft (graphLeft left g) (graphRight right g) keep)
        (InducedComponents.edgeRight (graphLeft left g) (graphRight right g) keep) q)
      (componentVertexEquiv left right g keep q hne u) (componentVertexEquiv left right g keep q hne v) :=
  adj_relabel (componentVertexEquiv left right g keep q hne) (componentEdgeEquiv left right g keep q)
    (componentVertexEquiv_left left right g keep q hne) (componentVertexEquiv_right left right g keep q hne) u v

/-- The ambient graph representing a nonbipartite component is nonbipartite. -/
theorem component_nonbipartite (q : Part left right g keep)
    (hne : Nonempty (PartEdge left right g keep q))
    (hnb : ¬Bipartite
      (componentLeft (InducedComponents.edgeLeft (graphLeft left g) (graphRight right g) keep)
        (InducedComponents.edgeRight (graphLeft left g) (graphRight right g) keep) q)
      (componentRight (InducedComponents.edgeLeft (graphLeft left g) (graphRight right g) keep)
        (InducedComponents.edgeRight (graphLeft left g) (graphRight right g) keep) q)) :
    ¬Bipartite (Ribbon.activeLeft (left := left) (right := right) (componentKeep left right g keep q))
      (Ribbon.activeRight (componentKeep left right g keep q)) :=
  fun hh => hnb (bipartite_relabel (componentVertexEquiv left right g keep q hne)
    (componentEdgeEquiv left right g keep q) (componentVertexEquiv_left left right g keep q hne)
    (componentVertexEquiv_right left right g keep q hne) hh)

end WeightedMIS.DrawingComponents
