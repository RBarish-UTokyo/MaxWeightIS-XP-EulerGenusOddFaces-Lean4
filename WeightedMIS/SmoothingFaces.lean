module

public import WeightedMIS.RibbonSmoothing

/-!
# Boundary circles surviving an edge restriction

The first-return identity induces a bijection between the actual boundary
circles of the restricted ribbon and the shared smoothing circles that meet
retained edges. This is an orbit statement about constructed permutations.
-/

@[expose] public section

namespace WeightedMIS.PermutationDeletion

/-- An injective semiconjugacy of finite permutations preserves and reflects
membership in an actual rotation orbit. -/
theorem sameCycle_iff_of_semiconj {α β : Type*} [Finite α] [Finite β]
    (σ : Equiv.Perm α) (ρ : Equiv.Perm β) (f : α → β)
    (hf : Function.Injective f) (hcomm : Function.Semiconj f σ ρ) (x y : α) :
    σ.SameCycle x y ↔ ρ.SameCycle (f x) (f y) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    have hh := congrArg f hn
    have hn' : f ((σ : α → α)^[n] x) = f y := by
      simpa only [Equiv.Perm.coe_pow] using hh
    simpa only [zpow_natCast, Equiv.Perm.coe_pow] using
      (hcomm.iterate_right n x).symm.trans hn'
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    apply hf
    have hn' : (ρ : β → β)^[n] (f x) = f y := by
      simpa only [Equiv.Perm.coe_pow] using hn
    simpa only [zpow_natCast, Equiv.Perm.coe_pow] using
      (hcomm.iterate_right n x).trans hn'

end WeightedMIS.PermutationDeletion

namespace WeightedMIS.EmbeddingFaces.Ribbon

open SidePairing

variable {V E : Type*} [Fintype E] {left right : E → V} (R : Ribbon left right)
    (keep : E → Prop) [DecidablePred keep]

/-- Restriction flags commute with their actual first-return rotation. -/
theorem restrict_rotation_semiconj :
    Function.Semiconj (Flag.retainedEquiv keep) (R.restrict keep).rotation
      (PermutationDeletion.firstReturn (R.sidePairing.smoothing keep) (fun x => keep x.edge)) := by
  intro x
  rw [R.sidePairing.smoothing_firstReturn]
  simp only [rotation, restrict, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- A retained oriented boundary orbit is precisely its shared smoothing orbit. -/
theorem restrict_sameCycle_iff (x y : Flag {e : E // keep e}) :
    (R.restrict keep).rotation.SameCycle x y ↔
      (R.sidePairing.smoothing keep).SameCycle (Flag.retainedEquiv keep x).val
        (Flag.retainedEquiv keep y).val := by
  rw [PermutationDeletion.sameCycle_iff_of_semiconj (R.restrict keep).rotation
    (PermutationDeletion.firstReturn (R.sidePairing.smoothing keep) (fun x => keep x.edge))
    (Flag.retainedEquiv keep) (Flag.retainedEquiv keep).injective (R.restrict_rotation_semiconj keep)]
  exact PermutationDeletion.sameCycle_firstReturn_iff _ _ _ _

/-- Include a retained flag in the shared smoothing ribbon. -/
def smoothingFlag (x : Flag {e : E // keep e}) : Flag E :=
  (Flag.retainedEquiv keep x).val

@[simp] theorem smoothingFlag_along (x : Flag {e : E // keep e}) :
    smoothingFlag keep (along x) = along (smoothingFlag keep x) := rfl

/-- The actual retained unoriented facial relation is the restriction of the
shared smoothing facial relation. -/
theorem restrict_sameFace_iff (x y : Flag {e : E // keep e}) :
    (R.restrict keep).SameFace x y ↔
      (R.sidePairing.smoothingRibbon keep).SameFace (smoothingFlag keep x)
        (smoothingFlag keep y) := by
  have hx : Flag.deletionToggle keep (smoothingFlag keep x) = smoothingFlag keep x := by
    simp only [smoothingFlag, Flag.retainedEquiv, Equiv.coe_fn_mk, Flag.deletionToggle,
      x.edge.property, ite_true]
  have hy : Flag.deletionToggle keep (smoothingFlag keep y) = smoothingFlag keep y := by
    simp only [smoothingFlag, Flag.retainedEquiv, Equiv.coe_fn_mk, Flag.deletionToggle,
      y.edge.property, ite_true]
  have hya : Flag.deletionToggle keep (along (smoothingFlag keep y)) =
      along (smoothingFlag keep y) := by
    simp only [smoothingFlag, Flag.retainedEquiv, Equiv.coe_fn_mk, Flag.deletionToggle,
      along, y.edge.property, ite_true]
  simp only [SameFace, R.restrict_sameCycle_iff keep]
  rw [PermutationDeletion.sameCycle_iff_of_semiconj (R.sidePairing.smoothing keep)
    (R.sidePairing.smoothingRibbon keep).rotation (Flag.deletionToggle keep)
    (Flag.deletionToggle keep).injective (R.sidePairing.smoothing_conjugate keep)]
  rw [PermutationDeletion.sameCycle_iff_of_semiconj (R.sidePairing.smoothing keep)
    (R.sidePairing.smoothingRibbon keep).rotation (Flag.deletionToggle keep)
    (Flag.deletionToggle keep).injective (R.sidePairing.smoothing_conjugate keep)]
  change ((R.sidePairing.smoothingRibbon keep).rotation.SameCycle (Flag.deletionToggle keep (smoothingFlag keep x))
    (Flag.deletionToggle keep (smoothingFlag keep y)) ∨
    (R.sidePairing.smoothingRibbon keep).rotation.SameCycle (Flag.deletionToggle keep (smoothingFlag keep x))
      (Flag.deletionToggle keep (along (smoothingFlag keep y)))) ↔ _
  rw [hx, hy, hya]

/-- The shared boundary circle containing a retained boundary circle. -/
noncomputable def smoothingFaceMap : (R.restrict keep).FaceIndex →
    (R.sidePairing.smoothingRibbon keep).FaceIndex :=
  Quotient.map (smoothingFlag keep) (fun _ _ h => (R.restrict_sameFace_iff keep _ _).mp h)

@[simp] theorem smoothingFaceMap_faceOf (x : Flag {e : E // keep e}) :
    R.smoothingFaceMap keep ((R.restrict keep).faceOf x) =
      (R.sidePairing.smoothingRibbon keep).faceOf (smoothingFlag keep x) := rfl

/-- Deleting edge intervals never identifies distinct surviving circles. -/
theorem smoothingFaceMap_injective : Function.Injective (R.smoothingFaceMap keep) := by
  intro f g
  induction f using Quotient.inductionOn with
  | h x =>
      induction g using Quotient.inductionOn with
      | h y =>
          intro h
          apply Quotient.sound
          exact (R.restrict_sameFace_iff keep x y).mpr (Quotient.exact h)

/-- A shared circle meets the retained edge set. -/
def MeetsRetained (f : (R.sidePairing.smoothingRibbon keep).FaceIndex) : Prop :=
  ∃ x : Flag {e : E // keep e}, (R.sidePairing.smoothingRibbon keep).faceOf
    (smoothingFlag keep x) = f

/-- Actual restricted circles are exactly the shared circles with retained
edge positions. -/
noncomputable def smoothingFaceEquiv : (R.restrict keep).FaceIndex ≃
    {f : (R.sidePairing.smoothingRibbon keep).FaceIndex // R.MeetsRetained keep f} :=
  Equiv.ofBijective (fun f => ⟨R.smoothingFaceMap keep f, by
    induction f using Quotient.inductionOn with
    | h x => exact ⟨x, rfl⟩⟩) ⟨by
      intro f g h
      exact R.smoothingFaceMap_injective keep (congrArg Subtype.val h), by
      rintro ⟨f, x, hx⟩
      refine ⟨(R.restrict keep).faceOf x, ?_⟩
      apply Subtype.ext
      exact hx⟩

end WeightedMIS.EmbeddingFaces.Ribbon
