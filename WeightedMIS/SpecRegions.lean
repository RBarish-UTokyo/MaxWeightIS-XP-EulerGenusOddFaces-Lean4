module

public import WeightedMIS.SpecOrientation
public import WeightedMIS.DrawingRegions

/-!
# Statement complementary regions are the deleted-dual components

The statement defines the regions of a subdrawing as classes of flags under
face steps and crossings of deleted edges. Internally a region is a connected
component of the dual graph whose edges are the deleted edges. The two are
identified, the boundary lengths (retained edge sides with multiplicity)
agree, and so do the odd-region counts.
-/

@[expose] public section

namespace WeightedMIS.Spec

open EmbeddingFaces

namespace Map

variable (A : Map) (hA : A.IsClosedSurface) (g : Fin A.edges → Prop)

/-- The internal face of a statement flag is the face of its edge side. -/
theorem faceOf_equiv (x : Flag (Fin A.edges)) :
    (A.ribbon hA).faceOf (Flag.equiv _ x) = (A.ribbon hA).sidePairing.face x.edge x.side := by
  rw [Ribbon.sidePairing_face]
  exact A.faceOf_endpoint hA x.edge x.side x.endpoint

/-- The region map on flags respects every statement region step. -/
theorem region_step {x y : Flag (Fin A.edges)} (h : A.RegionStep g x y) :
    (A.ribbon hA).sidePairing.originalFaceRegion g ((A.ribbon hA).faceOf (Flag.equiv _ x)) =
      (A.ribbon hA).sidePairing.originalFaceRegion g ((A.ribbon hA).faceOf (Flag.equiv _ y)) := by
  rcases h with h | ⟨hdel, rfl⟩
  · rw [A.faceOf_faceStep hA h]
  · rw [A.faceOf_equiv hA, A.faceOf_equiv hA]
    have hd := (A.ribbon hA).sidePairing.deleted_same_region g x.edge hdel
    change _ = (A.ribbon hA).sidePairing.originalFaceRegion g
      ((A.ribbon hA).sidePairing.face x.edge (!x.side))
    cases x.side
    · exact hd
    · exact hd.symm

/-- The flags of a root of an internal face lie in the region of every flag
of that face. -/
theorem region_root (x : Flag (Fin A.edges)) :
    Quot.mk (A.RegionStep g)
        ((Flag.equiv _).symm ((A.ribbon hA).faceRoot ((A.ribbon hA).faceOf (Flag.equiv _ x)))) =
      Quot.mk (A.RegionStep g) x := by
  apply A.quot_eq_of_sameFace hA (A.RegionStep g) (fun _ _ h => Or.inl h)
  rw [Equiv.apply_symm_apply]
  exact (A.ribbon hA).root_related _

/-- Statement regions are exactly the internal complementary regions. -/
noncomputable def regionEquiv :
    A.Region g ≃ (A.ribbon hA).sidePairing.ComplementRegion g where
  toFun := Quot.lift
    (fun x => (A.ribbon hA).sidePairing.originalFaceRegion g ((A.ribbon hA).faceOf (Flag.equiv _ x)))
    (fun _ _ h => A.region_step hA g h)
  invFun := Quotient.lift
    (fun f => Quot.mk (A.RegionStep g) ((Flag.equiv _).symm ((A.ribbon hA).faceRoot f)))
    (by
      rintro a b ⟨n, p⟩
      induction p with
      | nil => rfl
      | @forward b n e hb p ih =>
          rw [ih, hb]
          have h1 := A.region_root hA g ⟨e.val, false, false⟩
          have h2 := A.region_root hA g ⟨e.val, true, false⟩
          rw [A.faceOf_equiv hA] at h1 h2
          rw [h1, h2]
          exact Quot.sound (Or.inr ⟨e.property, rfl⟩)
      | @backward b n e hb p ih =>
          rw [ih, hb]
          have h1 := A.region_root hA g ⟨e.val, false, false⟩
          have h2 := A.region_root hA g ⟨e.val, true, false⟩
          rw [A.faceOf_equiv hA] at h1 h2
          rw [h1, h2]
          exact Quot.sound (Or.inr ⟨e.property, rfl⟩))
  left_inv := by
    intro r
    induction r using Quot.ind with
    | mk x => exact A.region_root hA g x
  right_inv := by
    intro r
    induction r using Quotient.ind
    rename_i f
    change (A.ribbon hA).sidePairing.originalFaceRegion g
      ((A.ribbon hA).faceOf (Flag.equiv _ ((Flag.equiv _).symm ((A.ribbon hA).faceRoot f)))) = _
    rw [Equiv.apply_symm_apply, Ribbon.faceOf_root]
    rfl

theorem regionEquiv_mk (x : Flag (Fin A.edges)) :
    A.regionEquiv hA g (Quot.mk _ x) =
      (A.ribbon hA).sidePairing.originalFaceRegion g ((A.ribbon hA).faceOf (Flag.equiv _ x)) := rfl

/-- Statement boundary lengths are the internal boundary lengths. -/
theorem boundaryLength_eq [DecidablePred g] (r : A.Region g) :
    A.boundaryLength g r =
      (A.ribbon hA).sidePairing.regionBoundaryLength g (A.regionEquiv hA g r) := by
  classical
  unfold boundaryLength SidePairing.regionBoundaryLength RegionParity.boundarySize
    RegionParity.fiberSize
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro s
  unfold SidePairing.drawingBoundary
  by_cases hs : g s.1
  · simp only [hs, ↓reduceIte, Option.some_inj, true_and]
    constructor
    · intro h
      subst h
      rw [regionEquiv_mk, A.faceOf_equiv hA]
    · intro h
      apply (A.regionEquiv hA g).injective
      rw [regionEquiv_mk, A.faceOf_equiv hA]
      exact h
  · simp [hs]

/-- The statement odd-region parameter is the internal one. -/
theorem cellular_oddRegionCount [Fintype (A.ribbon hA).FaceIndex] [DecidablePred g] :
    (A.cellular hA).sides.oddRegionCount g = A.oddRegionCount g := by
  unfold SidePairing.oddRegionCount oddRegionCount
  rw [← Nat.card_eq_fintype_card]
  symm
  apply Nat.card_congr
  exact Equiv.subtypeEquiv (A.regionEquiv hA g) (fun r => by
    rw [A.boundaryLength_eq hA g r]
    rfl)

end Map

end WeightedMIS.Spec
