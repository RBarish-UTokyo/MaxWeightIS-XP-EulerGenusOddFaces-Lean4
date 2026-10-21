module

public import WeightedMIS.RibbonRestriction
public import WeightedMIS.GraphComponents

/-! # Faithful vertex indexing of connected retained-edge subgraphs -/

@[expose] public section

namespace WeightedMIS.IndexedActiveVertices

open WeightedMIS.Incidence WeightedMIS.EmbeddingFaces

variable {U V D E : Type*} {leftD rightD : D → U} {leftE rightE : E → V}
    (keep : E → Prop) (f : U → V) (ee : D ≃ {e : E // keep e})
    (hl : ∀ e, f (leftD e) = leftE (ee e).val)
    (hr : ∀ e, f (rightD e) = rightE (ee e).val)
    (hc : Connected leftD rightD) (hne : Nonempty D)

def activeMap (u : U) : Ribbon.ActiveVertex (left := leftE) (right := rightE) keep :=
  ⟨f u, by
    obtain ⟨e, he | he⟩ := connected_vertex_incident leftD rightD hc hne u
    · exact ⟨(ee e).val, (ee e).property, Or.inl ((hl e).symm.trans (congrArg f he))⟩
    · exact ⟨(ee e).val, (ee e).property, Or.inr ((hr e).symm.trans (congrArg f he))⟩⟩

theorem activeMap_bijective (hf : Function.Injective f) :
    Function.Bijective (activeMap keep f ee hl hr hc hne) := by
  constructor
  · intro a b hab
    exact hf (congrArg Subtype.val hab)
  · intro v
    obtain ⟨e, he, hlv | hrv⟩ := v.property
    · refine ⟨leftD (ee.symm ⟨e, he⟩), Subtype.ext ?_⟩
      change f (leftD (ee.symm ⟨e, he⟩)) = v.val
      simpa only [hl, Equiv.apply_symm_apply] using hlv
    · refine ⟨rightD (ee.symm ⟨e, he⟩), Subtype.ext ?_⟩
      change f (rightD (ee.symm ⟨e, he⟩)) = v.val
      simpa only [hr, Equiv.apply_symm_apply] using hrv

/-- This equivalence transports counts and geometry; executable indexing uses
the original finite lists. -/
noncomputable def activeEquiv (hf : Function.Injective f) :
    U ≃ Ribbon.ActiveVertex (left := leftE) (right := rightE) keep :=
  Equiv.ofBijective (activeMap keep f ee hl hr hc hne)
    (activeMap_bijective keep f ee hl hr hc hne hf)

@[simp] theorem activeEquiv_val (hf : Function.Injective f) (u : U) :
    (activeEquiv keep f ee hl hr hc hne hf u).val = f u := rfl

@[simp] theorem activeEquiv_left (hf : Function.Injective f) (e : D) :
    activeEquiv keep f ee hl hr hc hne hf (leftD e) = Ribbon.activeLeft keep (ee e) :=
  Subtype.ext (hl e)

@[simp] theorem activeEquiv_right (hf : Function.Injective f) (e : D) :
    activeEquiv keep f ee hl hr hc hne hf (rightD e) = Ribbon.activeRight keep (ee e) :=
  Subtype.ext (hr e)

end WeightedMIS.IndexedActiveVertices
