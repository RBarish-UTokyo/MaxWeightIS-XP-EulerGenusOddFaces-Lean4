module

public import WeightedMIS.RibbonCellular

/-!
# Restricting an actual ribbon to retained edges

The new corner matching is constructed by first-return tracing and transported
to flags whose edge labels are the retained-edge subtype. Connected local links
are preserved. Restricting the vertex labels to incident vertices removes the
unused labels left by deletion.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open SidePairing

namespace Flag

/-- Flags on a retained-edge subtype are exactly retained original flags. -/
def retainedEquiv {E : Type*} (keep : E → Prop) :
    Flag {e : E // keep e} ≃ RetainedFlag keep where
  toFun x := ⟨⟨x.edge.val, x.side, x.endpoint⟩, x.edge.property⟩
  invFun x := ⟨⟨x.val.edge, x.property⟩, x.val.side, x.val.endpoint⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by rintro ⟨⟨e, s, t⟩, h⟩; rfl

end Flag

namespace Ribbon

variable {V E : Type*} [Fintype E] {left right : E → V} (R : Ribbon left right)

/-- The edge-deleted ribbon, with its inherited actual corner matching. -/
noncomputable def restrict (keep : E → Prop) :
    Ribbon (fun e : {e // keep e} => left e.val) (fun e => right e.val) where
  corner := (Flag.retainedEquiv keep).trans
    ((R.sidePairing.retainedCorner keep).trans (Flag.retainedEquiv keep).symm)
  involutive := by
    intro x
    change (Flag.retainedEquiv keep).symm (R.sidePairing.retainedCorner keep
      ((Flag.retainedEquiv keep) ((Flag.retainedEquiv keep).symm
        (R.sidePairing.retainedCorner keep ((Flag.retainedEquiv keep) x))))) = x
    rw [Equiv.apply_symm_apply, R.sidePairing.retainedCorner_involutive, Equiv.symm_apply_apply]
  ne_self := by
    intro x h
    apply R.sidePairing.retainedCorner_ne_self keep (Flag.retainedEquiv keep x)
    have hx := congrArg (Flag.retainedEquiv keep) h
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using hx
  vertex := by
    intro x
    change (R.sidePairing.retainedCorner keep ((Flag.retainedEquiv keep) x)).val.vertex left right =
      ((Flag.retainedEquiv keep) x).val.vertex left right
    exact R.sidePairing.retainedCorner_vertex keep _

/-- The retained corner-system links are exactly the transported links of the
first-return construction. -/
theorem restrict_vertexLinks (keep : E → Prop) (hlinks : R.VertexLinks) :
    (R.restrict keep).VertexLinks := by
  intro x y hxy
  have hr := R.sidePairing.retained_vertexLinks keep (R.sidePairing_vertexLinks hlinks)
    (Flag.retainedEquiv keep x) (Flag.retainedEquiv keep y) hxy
  have hmap : ∀ a b, R.sidePairing.RetainedLinkStep keep a b →
      (R.restrict keep).LinkStep ((Flag.retainedEquiv keep).symm a)
        ((Flag.retainedEquiv keep).symm b) := by
    intro a b hab
    cases hab with
    | across => exact LinkStep.across (R := R.restrict keep) _
    | corner =>
        have h := LinkStep.corner (R := R.restrict keep) ((Flag.retainedEquiv keep).symm a)
        simpa only [restrict, Equiv.trans_apply, Equiv.apply_symm_apply] using h
  have h := Relation.ReflTransGen.lift (Flag.retainedEquiv keep).symm hmap _ _ hr
  simpa only [Function.onFun, Equiv.symm_apply_apply] using h

/-- Vertex labels incident to at least one retained edge. -/
abbrev ActiveVertex (keep : E → Prop) :=
  {v : V // ∃ e : E, keep e ∧ (left e = v ∨ right e = v)}

/-- The left endpoint as an actually incident vertex. -/
def activeLeft (keep : E → Prop) (e : {e : E // keep e}) :
    ActiveVertex (left := left) (right := right) keep :=
  ⟨left e.val, e.val, e.property, Or.inl rfl⟩

/-- The right endpoint as an actually incident vertex. -/
def activeRight (keep : E → Prop) (e : {e : E // keep e}) :
    ActiveVertex (left := left) (right := right) keep :=
  ⟨right e.val, e.val, e.property, Or.inr rfl⟩

omit [Fintype E] in
@[simp] theorem active_vertex_val (keep : E → Prop) (x : Flag {e : E // keep e}) :
    (x.vertex (activeLeft (left := left) (right := right) keep) (activeRight keep)).val =
      x.vertex (fun e => left e.val) (fun e => right e.val) := by
  cases h : x.endpoint <;> simp [Flag.vertex, activeLeft, activeRight, h]

/-- The edge-deleted ribbon with unused original vertex labels removed. -/
noncomputable def activeRestrict (keep : E → Prop) :
    Ribbon (activeLeft (left := left) (right := right) keep) (activeRight keep) where
  corner := (R.restrict keep).corner
  involutive := (R.restrict keep).involutive
  ne_self := (R.restrict keep).ne_self
  vertex := by
    intro x
    apply Subtype.ext
    simpa only [active_vertex_val] using (R.restrict keep).vertex x

/-- Removing unused vertex labels preserves connected local links. -/
theorem activeRestrict_vertexLinks (keep : E → Prop) (hlinks : R.VertexLinks) :
    (R.activeRestrict keep).VertexLinks := by
  intro x y hxy
  have hxy' := congrArg Subtype.val hxy
  simp only [active_vertex_val] at hxy'
  have h := R.restrict_vertexLinks keep hlinks x y hxy'
  exact Relation.ReflTransGen.mono (fun a b hab => by
    cases hab with
    | across => exact .across a
    | corner => exact .corner a) _ _ h

omit [Fintype E] in
/-- Every retained active vertex is represented by an actual flag. -/
theorem activeRestrict_vertex_present (keep : E → Prop)
    (v : ActiveVertex (left := left) (right := right) keep) :
    ∃ x : Flag {e : E // keep e}, x.vertex (activeLeft keep) (activeRight keep) = v := by
  obtain ⟨e, he, hv | hv⟩ := v.property
  · refine ⟨⟨⟨e, he⟩, false, false⟩, ?_⟩
    apply Subtype.ext
    exact hv
  · refine ⟨⟨⟨e, he⟩, false, true⟩, ?_⟩
    apply Subtype.ext
    exact hv

/-- Deleting edge bands and capping the traced boundary circles gives a fully
constructed cellular combinatorial embedding of the remaining active graph. -/
noncomputable def cappedRestriction (keep : E → Prop) [DecidablePred keep]
    (hlinks : R.VertexLinks) (hnonempty : Nonempty {e : E // keep e}) :
    CellularEmbedding (activeLeft (left := left) (right := right) keep) (activeRight keep)
      (R.activeRestrict keep).FaceIndex :=
  (R.activeRestrict keep).toCellularEmbedding (R.activeRestrict_vertexLinks keep hlinks)
    (activeRestrict_vertex_present keep) hnonempty

end Ribbon
end WeightedMIS.EmbeddingFaces
