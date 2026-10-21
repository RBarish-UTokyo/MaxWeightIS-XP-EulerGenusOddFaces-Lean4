module

public import WeightedMIS.InducedComponents

/-!
# Exact labels for nested edge retention

Retaining edges from an already retained drawing gives the same endpoint
graph as retaining their original labels in one step. The equivalences include
the active vertices and preserve every edge endpoint.
-/

@[expose] public section

namespace WeightedMIS.NestedRetention

open EmbeddingFaces Incidence

variable {V E : Type*} (left right : E → V) (g : E → Prop)
    (h : {e : E // g e} → Prop)

/-- The actual original labels retained by two successive selections. -/
def keep (e : E) : Prop := g e ∧ ∀ he : g e, h ⟨e, he⟩

/-- Both orders of retaining edges give the same labels. -/
def edgeEquiv : {e : E // keep g h e} ≃ {e : {e : E // g e} // h e} where
  toFun e := ⟨⟨e.val, e.property.1⟩, e.property.2 _⟩
  invFun e := ⟨e.val.val, e.val.property, fun _ => e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nonempty (hne : Nonempty {e : {e : E // g e} // h e}) :
    Nonempty {e : E // keep g h e} := ⟨(edgeEquiv g h).symm hne.some⟩

/-- Active vertices have identical original labels after nested retention. -/
def vertexEquiv : Ribbon.ActiveVertex (left := left) (right := right) (keep g h) ≃
    Ribbon.ActiveVertex (left := fun e : {e // g e} => left e.val)
      (right := fun e => right e.val) h where
  toFun v := ⟨v.val, by
    obtain ⟨e, he, hv⟩ := v.property
    exact ⟨⟨e, he.1⟩, he.2 _, hv⟩⟩
  invFun v := ⟨v.val, by
    obtain ⟨e, he, hv⟩ := v.property
    exact ⟨e.val, ⟨e.property, fun _ => he⟩, hv⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem vertexEquiv_left (e : {e : E // keep g h e}) :
    vertexEquiv left right g h (Ribbon.activeLeft (left := left) (right := right) (keep g h) e) =
      Ribbon.activeLeft (left := fun e : {e // g e} => left e.val)
        (right := fun e => right e.val) h (edgeEquiv g h e) := rfl

@[simp] theorem vertexEquiv_right (e : {e : E // keep g h e}) :
    vertexEquiv left right g h (Ribbon.activeRight (left := left) (right := right) (keep g h) e) =
      Ribbon.activeRight (left := fun e : {e // g e} => left e.val)
        (right := fun e => right e.val) h (edgeEquiv g h e) := rfl

end WeightedMIS.NestedRetention
