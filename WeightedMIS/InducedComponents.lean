module

public import WeightedMIS.GraphComponents
public import WeightedMIS.RibbonRestriction
public import WeightedMIS.EndpointRelabeling

/-!
# Actual endpoint graphs of induced residual components

The original edge labels are retained exactly when both endpoints survive.
A component's original edge subset has active vertices equivalent to its
actual walk-component vertices, including all incidence proofs.
-/

@[expose] public section

namespace WeightedMIS.InducedComponents

open Incidence EmbeddingFaces

variable {V E : Type*} (left right : E → V) (keep : V → Prop)

abbrev Vertex := {v : V // keep v}
abbrev Edge := {e : E // keep (left e) ∧ keep (right e)}

def edgeLeft (e : Edge left right keep) : Vertex keep := ⟨left e.val, e.property.1⟩
def edgeRight (e : Edge left right keep) : Vertex keep := ⟨right e.val, e.property.2⟩

/-- Induced endpoint adjacency is exactly original adjacency on retained vertices. -/
theorem adj_iff (u v : Vertex keep) :
    EdgeTransport.Adj (edgeLeft left right keep) (edgeRight left right keep) u v ↔
      EdgeTransport.Adj left right u.val v.val := by
  constructor
  · rintro ⟨e, ⟨hl, hr⟩ | ⟨hl, hr⟩⟩
    · exact ⟨e.val, Or.inl ⟨congrArg Subtype.val hl, congrArg Subtype.val hr⟩⟩
    · exact ⟨e.val, Or.inr ⟨congrArg Subtype.val hl, congrArg Subtype.val hr⟩⟩
  · rintro ⟨e, ⟨hl, hr⟩ | ⟨hl, hr⟩⟩
    · refine ⟨⟨e, hl ▸ u.property, hr ▸ v.property⟩, Or.inl ?_⟩
      exact ⟨Subtype.ext hl, Subtype.ext hr⟩
    · refine ⟨⟨e, hl ▸ v.property, hr ▸ u.property⟩, Or.inr ?_⟩
      exact ⟨Subtype.ext hl, Subtype.ext hr⟩

abbrev Part := Component (edgeLeft left right keep) (edgeRight left right keep)
abbrev PartVertex (q : Part left right keep) :=
  ComponentVertex (edgeLeft left right keep) (edgeRight left right keep) q
abbrev PartEdge (q : Part left right keep) :=
  ComponentEdge (edgeLeft left right keep) (edgeRight left right keep) q

/-- The original edges in one actual induced connected component. -/
def componentKeep (q : Part left right keep) (e : E) : Prop :=
  keep (left e) ∧ keep (right e) ∧
    ∀ h : keep (left e), componentOf (edgeLeft left right keep) (edgeRight left right keep) ⟨left e, h⟩ = q

/-- This original-edge subset is exactly the component's retained edge labels. -/
def componentEdgeEquiv (q : Part left right keep) :
    {e : E // componentKeep left right keep q e} ≃ PartEdge left right keep q where
  toFun e := ⟨⟨e.val, e.property.1, e.property.2.1⟩, e.property.2.2 _⟩
  invFun e := ⟨e.val.val, e.val.property.1, e.val.property.2, fun _ => e.property⟩
  left_inv := by intro e; rfl
  right_inv := by intro e; rfl

/-- The retained component edge set is nonempty whenever the actual component is. -/
theorem componentKeep_nonempty (q : Part left right keep) (hne : Nonempty (PartEdge left right keep q)) :
    Nonempty {e : E // componentKeep left right keep q e} :=
  hne.map (componentEdgeEquiv left right keep q).symm

/-- Every active original vertex of the component is an actual component vertex. -/
def activeToComponent (q : Part left right keep)
    (v : Ribbon.ActiveVertex (left := left) (right := right) (componentKeep left right keep q)) :
    PartVertex left right keep q := by
  have hv : keep v.val := by
    obtain ⟨e, he, hv | hv⟩ := v.property
    · exact hv ▸ he.1
    · exact hv ▸ he.2.1
  refine ⟨⟨v.val, hv⟩, ?_⟩
  obtain ⟨e, he, hv' | hv'⟩ := v.property
  · have h := he.2.2 he.1
    simpa only [show (⟨left e, he.1⟩ : Vertex keep) = ⟨v.val, hv⟩ from Subtype.ext hv'] using h
  · have h := (componentOf_endpoints (edgeLeft left right keep) (edgeRight left right keep)
        (⟨e, he.1, he.2.1⟩ : Edge left right keep)).symm.trans (he.2.2 he.1)
    simpa only [show edgeRight left right keep ⟨e, he.1, he.2.1⟩ = ⟨v.val, hv⟩ from Subtype.ext hv'] using h

@[simp] theorem activeToComponent_val (q : Part left right keep)
    (v : Ribbon.ActiveVertex (left := left) (right := right) (componentKeep left right keep q)) :
    (activeToComponent left right keep q v).val.val = v.val := rfl

/-- Every vertex in a nontrivial component is incident to one of its original edges. -/
def componentToActive (q : Part left right keep) (hne : Nonempty (PartEdge left right keep q))
    (v : PartVertex left right keep q) :
    Ribbon.ActiveVertex (left := left) (right := right) (componentKeep left right keep q) := by
  refine ⟨v.val.val, ?_⟩
  obtain ⟨e, he | he⟩ := connected_vertex_incident
    (componentLeft (edgeLeft left right keep) (edgeRight left right keep) q)
    (componentRight (edgeLeft left right keep) (edgeRight left right keep) q)
    (component_connected _ _ q) hne v
  · refine ⟨e.val.val, ?_, Or.inl (congrArg (fun u => u.val.val) he)⟩
    exact ((componentEdgeEquiv left right keep q).symm e).property
  · refine ⟨e.val.val, ?_, Or.inr (congrArg (fun u => u.val.val) he)⟩
    exact ((componentEdgeEquiv left right keep q).symm e).property

/-- Active original vertices are precisely the vertices of a nontrivial
actual residual component. -/
def activeComponentEquiv (q : Part left right keep) (hne : Nonempty (PartEdge left right keep q)) :
    Ribbon.ActiveVertex (left := left) (right := right) (componentKeep left right keep q) ≃
      PartVertex left right keep q where
  toFun := activeToComponent left right keep q
  invFun := componentToActive left right keep q hne
  left_inv := by intro v; apply Subtype.ext; rfl
  right_inv := by intro v; apply Subtype.ext; apply Subtype.ext; rfl

@[simp] theorem activeComponentEquiv_left (q : Part left right keep)
    (hne : Nonempty (PartEdge left right keep q)) (e : {e // componentKeep left right keep q e}) :
    activeComponentEquiv left right keep q hne (Ribbon.activeLeft (left := left) (right := right) _ e) =
      componentLeft (edgeLeft left right keep) (edgeRight left right keep) q
        (componentEdgeEquiv left right keep q e) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

@[simp] theorem activeComponentEquiv_right (q : Part left right keep)
    (hne : Nonempty (PartEdge left right keep q)) (e : {e // componentKeep left right keep q e}) :
    activeComponentEquiv left right keep q hne (Ribbon.activeRight (left := left) (right := right) _ e) =
      componentRight (edgeLeft left right keep) (edgeRight left right keep) q
        (componentEdgeEquiv left right keep q e) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The active original labels of a nontrivial residual component are connected. -/
theorem activeComponent_connected (q : Part left right keep)
    (hne : Nonempty (PartEdge left right keep q)) :
    Connected (Ribbon.activeLeft (left := left) (right := right) (componentKeep left right keep q))
      (Ribbon.activeRight (componentKeep left right keep q)) :=
  connected_relabel (activeComponentEquiv left right keep q hne) (componentEdgeEquiv left right keep q)
    (activeComponentEquiv_left left right keep q hne) (activeComponentEquiv_right left right keep q hne)
    (component_connected _ _ q)

/-- Nonbipartiteness is preserved by the actual residual component label equivalences. -/
theorem activeComponent_nonbipartite (q : Part left right keep)
    (hne : Nonempty (PartEdge left right keep q))
    (hnb : ¬Bipartite (componentLeft (edgeLeft left right keep) (edgeRight left right keep) q)
      (componentRight (edgeLeft left right keep) (edgeRight left right keep) q)) :
    ¬Bipartite (Ribbon.activeLeft (left := left) (right := right) (componentKeep left right keep q))
      (Ribbon.activeRight (componentKeep left right keep q)) :=
  fun h => hnb (bipartite_relabel (activeComponentEquiv left right keep q hne)
    (componentEdgeEquiv left right keep q) (activeComponentEquiv_left left right keep q hne)
    (activeComponentEquiv_right left right keep q hne) h)

/-- The active retained graph has exactly the actual component adjacency. -/
theorem activeComponent_adj (q : Part left right keep)
    (hne : Nonempty (PartEdge left right keep q))
    (u v : Ribbon.ActiveVertex (left := left) (right := right) (componentKeep left right keep q)) :
    EdgeTransport.Adj (Ribbon.activeLeft (left := left) (right := right) (componentKeep left right keep q))
      (Ribbon.activeRight (componentKeep left right keep q)) u v ↔
    EdgeTransport.Adj (componentLeft (edgeLeft left right keep) (edgeRight left right keep) q)
      (componentRight (edgeLeft left right keep) (edgeRight left right keep) q)
      (activeComponentEquiv left right keep q hne u) (activeComponentEquiv left right keep q hne v) :=
  adj_relabel (activeComponentEquiv left right keep q hne) (componentEdgeEquiv left right keep q)
    (activeComponentEquiv_left left right keep q hne) (activeComponentEquiv_right left right keep q hne) u v

end WeightedMIS.InducedComponents
