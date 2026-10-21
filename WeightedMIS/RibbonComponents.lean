module

public import WeightedMIS.GraphComponents
public import WeightedMIS.RibbonRestriction
public import WeightedMIS.ComplementEuler

/-!
# Actual connected components of a ribbon

A corner preserves its graph vertex and therefore its actual walk component.
Restricting that matching to each component requires no assumed face or Euler
identity. Isolated vertices are retained as disk components separately.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.Ribbon

open SidePairing Incidence

attribute [local instance] Classical.propDecidable

variable {V E : Type*} {left right : E → V} (R : Ribbon left right)

/-- Forget the component membership of the edge in a flag. -/
def componentFlag {q : Component left right} (x : Flag (ComponentEdge left right q)) : Flag E :=
  ⟨x.edge.val, x.side, x.endpoint⟩

theorem componentFlag_injective (q : Component left right) :
    Function.Injective (componentFlag (left := left) (right := right) (q := q)) := by
  intro x y h
  rcases x with ⟨e, s, t⟩
  rcases y with ⟨e', s', t'⟩
  simp only [componentFlag, Flag.mk.injEq] at h
  obtain ⟨he, hs, ht⟩ := h
  have he' : e = e' := Subtype.ext he
  subst e'; subst s'; subst t'
  rfl

/-- Either endpoint of a flag has the component of its edge. -/
theorem flag_vertex_component (x : Flag E) :
    componentOf left right (x.vertex left right) = componentOf left right (left x.edge) := by
  cases h : x.endpoint
  · simp [Flag.vertex, h]
  · simpa only [Flag.vertex, h, Bool.true_eq, ite_true] using (componentOf_endpoints left right x.edge).symm

theorem corner_component (x : Flag E) :
    componentOf left right (left (R.corner x).edge) = componentOf left right (left x.edge) := by
  rw [← flag_vertex_component, R.vertex, flag_vertex_component]

/-- The actual corner restricted to one endpoint-graph component. -/
def componentCorner (q : Component left right) : Equiv.Perm (Flag (ComponentEdge left right q)) :=
  (Flag.retainedEquiv (fun e => componentOf left right (left e) = q)).trans
    ((R.corner.subtypePerm (fun x => by
      change componentOf left right (left (R.corner x).edge) = q ↔
        componentOf left right (left x.edge) = q
      rw [R.corner_component])).trans
      (Flag.retainedEquiv (fun e => componentOf left right (left e) = q)).symm)

@[simp] theorem componentCorner_coe (q : Component left right)
    (x : Flag (ComponentEdge left right q)) :
    componentFlag (R.componentCorner q x) = R.corner (componentFlag x) := rfl

@[simp] theorem componentFlag_vertex {q : Component left right}
    (x : Flag (ComponentEdge left right q)) :
    (x.vertex (componentLeft left right q) (componentRight left right q)).val =
      (componentFlag x).vertex left right := by
  cases h : x.endpoint <;> simp [Flag.vertex, componentFlag, h, componentLeft, componentRight]

/-- Each component inherits the original corners exactly, with the restricted
actual vertex and edge labels. -/
def componentRibbon (q : Component left right) :
    Ribbon (componentLeft left right q) (componentRight left right q) where
  corner := R.componentCorner q
  involutive := by
    intro x
    apply componentFlag_injective q
    simp only [componentCorner_coe]
    exact R.involutive _
  ne_self := by
    intro x hx
    apply R.ne_self (componentFlag x)
    simpa only [componentCorner_coe] using congrArg componentFlag hx
  vertex := by
    intro x
    apply Subtype.ext
    have h := R.vertex (componentFlag x)
    simpa only [← componentCorner_coe, ← componentFlag_vertex] using h

/-- Embed a flag whose edge has the specified actual component. -/
def inComponent (q : Component left right) (x : Flag E)
    (h : componentOf left right (left x.edge) = q) : Flag (ComponentEdge left right q) :=
  ⟨⟨x.edge, h⟩, x.side, x.endpoint⟩

@[simp] theorem componentFlag_inComponent (q : Component left right) (x : Flag E)
    (h : componentOf left right (left x.edge) = q) : componentFlag (inComponent q x h) = x := rfl

@[simp] theorem inComponent_componentFlag (q : Component left right)
    (x : Flag (ComponentEdge left right q)) :
    inComponent q (componentFlag x) x.edge.property = x := by cases x; rfl

/-- A total projection used only to transport link paths inside a component. -/
noncomputable def componentProjection (q : Component left right)
    (base : Flag (ComponentEdge left right q)) (x : Flag E) : Flag (ComponentEdge left right q) :=
  if h : componentOf left right (left x.edge) = q then inComponent q x h else base

@[simp] theorem componentProjection_of_mem (q : Component left right)
    (base : Flag (ComponentEdge left right q)) (x : Flag E)
    (h : componentOf left right (left x.edge) = q) :
    componentProjection q base x = inComponent q x h := by simp [componentProjection, h]

/-- Link steps cannot change the walk component. -/
theorem linkStep_component {x y : Flag E} (h : R.LinkStep x y) :
    componentOf left right (left y.edge) = componentOf left right (left x.edge) := by
  cases h with
  | across => rfl
  | corner => exact R.corner_component x

/-- Actual connected vertex links restrict to each graph component. -/
theorem component_vertexLinks (hlinks : R.VertexLinks) (q : Component left right) :
    (R.componentRibbon q).VertexLinks := by
  intro x y hxy
  have hp : ∀ a b, R.LinkStep a b →
      Relation.ReflTransGen (R.componentRibbon q).LinkStep
        (componentProjection q x a) (componentProjection q x b) := by
    intro a b hab
    have hc := R.linkStep_component hab
    by_cases ha : componentOf left right (left a.edge) = q
    · have hb := hc.trans ha
      rw [componentProjection_of_mem q x a ha, componentProjection_of_mem q x b hb]
      apply Relation.ReflTransGen.single
      cases hab with
      | across => exact .across _
      | corner => exact .corner _
    · have hb : componentOf left right (left b.edge) ≠ q := by rwa [hc]
      simp only [componentProjection, dite_eq_right ha, dite_eq_right hb]
      exact .refl
  have hxy' : (componentFlag x).vertex left right = (componentFlag y).vertex left right := by
    simpa only [componentFlag_vertex] using congrArg Subtype.val hxy
  have h := (hlinks (componentFlag x) (componentFlag y) hxy').lift'
    (componentProjection q x) hp
  change Relation.ReflTransGen _ (componentProjection q x (componentFlag x))
    (componentProjection q x (componentFlag y)) at h
  simpa only [componentProjection_of_mem q x (componentFlag x) x.edge.property,
    componentProjection_of_mem q x (componentFlag y) y.edge.property, inComponent_componentFlag] using h

/-- A nontrivial connected component has a flag at every vertex. -/
theorem component_vertex_present (q : Component left right)
    (hne : Nonempty (ComponentEdge left right q))
    (v : ComponentVertex left right q) :
    ∃ x : Flag (ComponentEdge left right q),
      x.vertex (componentLeft left right q) (componentRight left right q) = v := by
  obtain ⟨e⟩ := hne
  obtain ⟨n, p⟩ := component_connected left right q (componentLeft left right q e) v
  cases p with
  | nil => exact ⟨⟨e, false, false⟩, rfl⟩
  | forward e => exact ⟨⟨e, false, true⟩, rfl⟩
  | backward e => exact ⟨⟨e, false, false⟩, rfl⟩

variable [Fintype E]

/-- The genuine cellular embedding of a nontrivial component, with faces
constructed by tracing its restricted corner matching. -/
noncomputable def componentEmbedding (hlinks : R.VertexLinks) (q : Component left right)
    (hne : Nonempty (ComponentEdge left right q)) :
    CellularEmbedding (componentLeft left right q) (componentRight left right q)
      (R.componentRibbon q).FaceIndex :=
  (R.componentRibbon q).toCellularEmbedding (R.component_vertexLinks hlinks q)
    (component_vertex_present q hne) hne

/-- Face labels of a capped component: traced circles when it has edges,
and the single boundary of a disk at an isolated vertex. -/
noncomputable def CappedFace (q : Component left right) : Type _ :=
  if Nonempty (ComponentEdge left right q) then (R.componentRibbon q).FaceIndex else PUnit

noncomputable instance (q : Component left right) : Fintype (R.CappedFace q) := by
  unfold CappedFace
  split <;> infer_instance

/-- Every graph component gives an actual capped ribbon component, including
isolated vertex disks rather than dropping their contribution to Euler counts. -/
noncomputable def cappedComponent (hlinks : R.VertexLinks) (q : Component left right) :
    CappedComponent (componentLeft left right q) (componentRight left right q) (R.CappedFace q) := by
  by_cases he : Nonempty (ComponentEdge left right q)
  · rw [CappedFace, ite_eq_left he]
    exact .embedded (R.componentEmbedding hlinks q he) (component_connected left right q)
  · rw [CappedFace, ite_eq_right he]
    let : IsEmpty (ComponentEdge left right q) := not_nonempty_iff.mp he
    let : Subsingleton (ComponentVertex left right q) := componentVertex_subsingleton left right q
    let : Nonempty (ComponentVertex left right q) := componentVertex_nonempty left right q
    exact .isolated ⟨⟨Classical.choice (componentVertex_nonempty left right q)⟩,
      fun v => Subsingleton.elim v _⟩ inferInstance inferInstance

end WeightedMIS.EmbeddingFaces.Ribbon
