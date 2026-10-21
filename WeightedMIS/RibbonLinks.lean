module

public import WeightedMIS.RibbonTracing

/-!
# Actual vertex links of a ribbon corner matching
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.Ribbon

open SidePairing

variable {V E : Type*} {left right : E → V} (R : Ribbon left right)

/-- A vertex link alternates paired edge sides and actual corners. -/
inductive LinkStep : Flag E → Flag E → Prop where
  | across (x) : LinkStep x (SidePairing.across x)
  | corner (x) : LinkStep x (R.corner x)

/-- The local manifold condition at each supplied graph vertex. -/
def VertexLinks : Prop :=
  ∀ x y : Flag E, x.vertex left right = y.vertex left right →
    Relation.ReflTransGen R.LinkStep x y

theorem linkStep_vertex {x y : Flag E} (h : R.LinkStep x y) :
    x.vertex left right = y.vertex left right := by
  cases h with
  | across => rfl
  | corner => exact (R.vertex x).symm

theorem linkStep_symm {x y : Flag E} (h : R.LinkStep x y) : R.LinkStep y x := by
  cases h with
  | across =>
      have h' := LinkStep.across (R := R) (SidePairing.across x)
      simpa only [across_across] using h'
  | corner =>
      have h' := LinkStep.corner (R := R) (R.corner x)
      rw [R.involutive x] at h'
      exact h'

theorem linkReach_symm {x y : Flag E} (h : Relation.ReflTransGen R.LinkStep x y) :
    Relation.ReflTransGen R.LinkStep y x := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact (Relation.ReflTransGen.single (R.linkStep_symm hs)).trans ih

end WeightedMIS.EmbeddingFaces.Ribbon
