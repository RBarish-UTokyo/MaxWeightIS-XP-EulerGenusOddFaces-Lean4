module

public import WeightedMIS.DeletionParameters

/-!
# Complementary regions of a retained drawing

A cellular decomposition is used only as a geometric witness. The drawing
itself consists of retained edge bands and the inherited vertex disks. Its
complementary regions are actual deleted-dual components. Their boundary
lengths count the retained side occurrences, including multiplicities.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.SidePairing

open Incidence
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V E F : Type*} [Fintype E] [Fintype F]
    {left right : E → V} {faces : F → Faces.Face left right}
    (P : SidePairing faces) (g h : E → Prop)

/-- A region of the larger drawing belongs to a unique region after deleting
additional edges. The map is induced by actual deleted-dual walks. -/
def regionRefinement (hsub : ∀ e, h e → g e) : P.ComplementRegion g → P.ComplementRegion h :=
  Quotient.map' id (by
    intro a b hab
    obtain ⟨n, p⟩ := hab
    refine ⟨n, ?_⟩
    induction p with
    | nil => exact .nil _
    | @forward b n e hb p ih =>
        exact .forward ⟨e.val, fun he => e.property (hsub e.val he)⟩ hb ih
    | @backward b n e hb p ih =>
        exact .backward ⟨e.val, fun he => e.property (hsub e.val he)⟩ hb ih)

@[simp] theorem regionRefinement_originalFace (hsub : ∀ e, h e → g e) (f : F) :
    P.regionRefinement g h hsub (P.originalFaceRegion g f) = P.originalFaceRegion h f := rfl

/-- Each retained edge-side is assigned to the actual original complementary
region on that side of the drawing. -/
def drawingBoundary [DecidablePred g] (s : E × Bool) : Option (P.ComplementRegion g) :=
  if g s.1 then some (P.originalFaceRegion g (P.face s.1 s.2)) else none

/-- Total boundary length of a complementary region, counted with genuine
edge-side multiplicity. Isolated vertex circles have length zero. -/
noncomputable def regionBoundaryLength [DecidablePred g] (r : P.ComplementRegion g) : ℕ :=
  RegionParity.boundarySize (P.drawingBoundary g) r

/-- The manuscript's odd-region parameter for an arbitrary retained drawing. -/
noncomputable def oddRegionCount [DecidablePred g] : ℕ :=
  Fintype.card {r : P.ComplementRegion g // Odd (P.regionBoundaryLength g r)}

/-- The two occurrences of each removed edge cancel in its actual complementary
region. Thus grouping the ambient face sides gives the same boundary parity. -/
theorem regionBoundaryLength_mod [DecidablePred g] (r : P.ComplementRegion g) :
    P.regionBoundaryLength g r % 2 =
      RegionParity.fiberSize (fun s : E × Bool => P.originalFaceRegion g (P.face s.1 s.2)) r % 2 := by
  classical
  have hc := RegionParity.side_cancellation
    (fun s : E × Bool => P.originalFaceRegion g (P.face s.1 s.2)) id
    (P.drawingBoundary g) id
    (fun e => by by_cases he : g e <;> simp [drawingBoundary, he])
    (fun e he => by
      have hn : ¬g e := by intro hg; simp [drawingBoundary, hg] at he
      exact P.deleted_same_region g e hn)
    (fun s b hs => by
      by_cases hg : g s.1
      · simpa [drawingBoundary, hg] using hs.symm
      · simp [drawingBoundary, hg] at hs) r
  have ho := RegionParity.grouped_fiber_sum
    (fun s : E × Bool => P.originalFaceRegion g (P.face s.1 s.2)) id r
  have hb := RegionParity.grouped_boundary_sum (P.drawingBoundary g) id r
  simp only [id_eq, Finset.sum_filter, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at ho hb
  simp only [id_eq] at hc
  unfold regionBoundaryLength
  omega

/-- Counting odd total region-boundary lengths agrees with counting odd
fibers of the original face-side grouping. -/
theorem oddRegionCount_eq [DecidablePred g] :
    P.oddRegionCount g = Fintype.card {r : P.ComplementRegion g //
      Odd (RegionParity.fiberSize (fun s : E × Bool => P.originalFaceRegion g (P.face s.1 s.2)) r)} := by
  classical
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun r => by
    rw [Nat.odd_iff, Nat.odd_iff, P.regionBoundaryLength_mod g r])

end WeightedMIS.EmbeddingFaces.SidePairing
