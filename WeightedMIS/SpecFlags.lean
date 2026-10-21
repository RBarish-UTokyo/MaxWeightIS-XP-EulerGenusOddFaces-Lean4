module

public import WeightedMIS.Spec
public import WeightedMIS.RibbonRelabeling

/-!
# Statement flags and the internal flag type

The statement-level flags of `WeightedMIS.Spec` and the internal
`EmbeddingFaces.Flag` carry the same three fields. This file identifies them,
transports the three involutions, and builds an internal corner system
(`EmbeddingFaces.Ribbon`) from a statement-level corner pairing.
-/

@[expose] public section

namespace WeightedMIS.Spec

namespace Flag

/-- Statement flags and internal flags are the same records. -/
def equiv (E : Type) : Flag E ≃ EmbeddingFaces.Flag E where
  toFun x := ⟨x.edge, x.side, x.endpoint⟩
  invFun x := ⟨x.edge, x.side, x.endpoint⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

variable {E : Type}

@[simp] theorem equiv_edge (x : Flag E) : (equiv E x).edge = x.edge := rfl
@[simp] theorem equiv_side (x : Flag E) : (equiv E x).side = x.side := rfl
@[simp] theorem equiv_endpoint (x : Flag E) : (equiv E x).endpoint = x.endpoint := rfl
@[simp] theorem equiv_symm_edge (x : EmbeddingFaces.Flag E) : ((equiv E).symm x).edge = x.edge := rfl
@[simp] theorem equiv_symm_side (x : EmbeddingFaces.Flag E) : ((equiv E).symm x).side = x.side := rfl
@[simp] theorem equiv_symm_endpoint (x : EmbeddingFaces.Flag E) :
    ((equiv E).symm x).endpoint = x.endpoint := rfl

theorem equiv_along (x : Flag E) :
    equiv E x.along = EmbeddingFaces.SidePairing.along (equiv E x) := rfl

theorem equiv_across (x : Flag E) :
    equiv E x.across = EmbeddingFaces.SidePairing.across (equiv E x) := rfl

theorem equiv_symm_along (x : EmbeddingFaces.Flag E) :
    (equiv E).symm (EmbeddingFaces.SidePairing.along x) = ((equiv E).symm x).along := rfl

theorem equiv_symm_across (x : EmbeddingFaces.Flag E) :
    (equiv E).symm (EmbeddingFaces.SidePairing.across x) = ((equiv E).symm x).across := rfl

@[simp] theorem along_along (x : Flag E) : x.along.along = x := by
  cases x; simp [along]

@[simp] theorem across_across (x : Flag E) : x.across.across = x := by
  cases x; simp [across]

theorem equiv_map {D : Type} (e : D ≃ E) (x : Flag D) :
    equiv E (x.map e) = EmbeddingFaces.Flag.mapEquiv e (equiv D x) := rfl

end Flag

/-- The vertex of a statement flag is the internal flag vertex. -/
theorem Map.vertexOf_eq (A : Map) (x : Flag (Fin A.edges)) :
    A.vertexOf x = (Flag.equiv _ x).vertex A.left A.right := rfl

/-- An internal corner system from a statement-level corner pairing with the
local properties of a corner matching. -/
def ribbonOf {V E : Type} (left right : E → V) (c : Flag E → Flag E)
    (hinv : ∀ x, c (c x) = x) (hne : ∀ x, c x ≠ x)
    (hv : ∀ x, (Flag.equiv E (c x)).vertex left right = (Flag.equiv E x).vertex left right) :
    EmbeddingFaces.Ribbon left right where
  corner :=
    { toFun := fun x => Flag.equiv E (c ((Flag.equiv E).symm x))
      invFun := fun x => Flag.equiv E (c ((Flag.equiv E).symm x))
      left_inv := fun x => by simp [hinv]
      right_inv := fun x => by simp [hinv] }
  involutive := fun x => by simp [hinv]
  ne_self := fun x h => hne ((Flag.equiv E).symm x) (by
    apply (Flag.equiv E).injective
    simpa using h)
  vertex := fun x => by simpa using hv ((Flag.equiv E).symm x)

@[simp] theorem ribbonOf_corner {V E : Type} (left right : E → V) (c : Flag E → Flag E)
    (hinv : ∀ x, c (c x) = x) (hne : ∀ x, c x ≠ x)
    (hv : ∀ x, (Flag.equiv E (c x)).vertex left right = (Flag.equiv E x).vertex left right)
    (x : Flag E) :
    (ribbonOf left right c hinv hne hv).corner (Flag.equiv E x) = Flag.equiv E (c x) := by
  simp [ribbonOf]

namespace Map

variable (A : Map) (hA : A.IsClosedSurface)

/-- The internal corner system of a closed-surface map. -/
def ribbon : EmbeddingFaces.Ribbon A.left A.right :=
  ribbonOf A.left A.right A.corner hA.corner_involutive hA.corner_ne hA.corner_vertex

@[simp] theorem ribbon_corner (x : Flag (Fin A.edges)) :
    (A.ribbon hA).corner (Flag.equiv _ x) = Flag.equiv _ (A.corner x) :=
  ribbonOf_corner _ _ _ _ _ _ x

theorem ribbon_corner' (x : EmbeddingFaces.Flag (Fin A.edges)) :
    (A.ribbon hA).corner x = Flag.equiv _ (A.corner ((Flag.equiv _).symm x)) := by
  simpa using A.ribbon_corner hA ((Flag.equiv _).symm x)

/-- Statement vertex links are the internal vertex links. -/
theorem ribbon_vertexLinks : (A.ribbon hA).VertexLinks := by
  intro x y hxy
  have h := hA.links ((Flag.equiv _).symm x) ((Flag.equiv _).symm y) (by
    simpa [Map.vertexOf_eq] using hxy)
  have hmap : ∀ a b, A.LinkStep a b →
      (A.ribbon hA).LinkStep (Flag.equiv _ a) (Flag.equiv _ b) := by
    rintro a b (rfl | rfl)
    · exact EmbeddingFaces.Ribbon.LinkStep.across _
    · have := EmbeddingFaces.Ribbon.LinkStep.corner (R := A.ribbon hA) (Flag.equiv _ a)
      rwa [A.ribbon_corner hA] at this
  have h' := Relation.ReflTransGen.lift (Flag.equiv _) hmap _ _ h
  simpa only [Function.onFun, Equiv.apply_symm_apply] using h'

end Map

end WeightedMIS.Spec
