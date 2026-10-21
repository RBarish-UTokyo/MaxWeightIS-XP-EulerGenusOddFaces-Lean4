module

public import WeightedMIS.RibbonRestriction
public import WeightedMIS.EmbeddingDual

/-!
# The shared boundary smoothing for complementary edge sets

At a retained edge a trace follows its endpoint; at a deleted edge it crosses
to the other side. Turning through the original corner then gives one shared
permutation. The first-return trace on retained flags is exactly the actual
boundary rotation after deletion.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open SidePairing

namespace Flag

variable {E : Type*}

/-- Swap side and endpoint only on the deleted edge flags. -/
def deletionToggle (keep : E → Prop) [DecidablePred keep] : Equiv.Perm (Flag E) where
  toFun x := if keep x.edge then x else swapSideEndpoint x
  invFun x := if keep x.edge then x else swapSideEndpoint x
  left_inv := by
    intro x
    by_cases h : keep x.edge <;> simp [h, swapSideEndpoint]
  right_inv := by
    intro x
    by_cases h : keep x.edge <;> simp [h, swapSideEndpoint]

@[simp] theorem deletionToggle_edge (keep : E → Prop) [DecidablePred keep] (x : Flag E) :
    (deletionToggle keep x).edge = x.edge := by
  by_cases h : keep x.edge <;> simp [deletionToggle, h, swapSideEndpoint]

@[simp] theorem deletionToggle_twice (keep : E → Prop) [DecidablePred keep] (x : Flag E) :
    deletionToggle keep (deletionToggle keep x) = x :=
  (deletionToggle keep).symm_apply_apply x

/-- The local switch follows retained edges and crosses deleted edges. -/
def deletionSwitch (keep : E → Prop) [DecidablePred keep] : Equiv.Perm (Flag E) :=
  ((deletionToggle keep).trans along).trans (deletionToggle keep)

theorem deletionSwitch_apply (keep : E → Prop) [DecidablePred keep] (x : Flag E) :
    deletionSwitch keep x = if keep x.edge then along x else across x := by
  by_cases h : keep x.edge
  · simp [deletionSwitch, deletionToggle, h, along]
  · simp [deletionSwitch, deletionToggle, h, along, swapSideEndpoint, across]

@[simp] theorem deletionSwitch_twice (keep : E → Prop) [DecidablePred keep] (x : Flag E) :
    deletionSwitch keep (deletionSwitch keep x) = x := by
  simp only [deletionSwitch, Equiv.trans_apply, deletionToggle_twice, along_along]

theorem deletionSwitch_ne_self (keep : E → Prop) [DecidablePred keep] (x : Flag E) :
    deletionSwitch keep x ≠ x := by
  rw [deletionSwitch_apply]
  split
  · exact along_ne_self _
  · exact across_ne_self _

end Flag

namespace SidePairing

variable {V E F : Type*} [Fintype E] {left right : E → V}
    {faces : F → Faces.Face left right} (P : SidePairing faces)
    (keep : E → Prop) [DecidablePred keep]

/-- One common permutation traces the boundary between retained primal bands
and deleted dual bands. -/
def smoothing : Equiv.Perm (Flag E) := (Flag.deletionSwitch keep).trans P.corner

theorem smoothing_apply (x : Flag E) :
    P.smoothing keep x = P.corner (if keep x.edge then along x else across x) := by
  exact congrArg P.corner (Flag.deletionSwitch_apply keep x)

/-- The common smoothing can itself be represented as an ordinary finite
ribbon, after exchanging the side/endpoint coordinates on deleted edges.
The single vertex label is used only for this boundary-cycle representation. -/
def smoothingRibbon : Ribbon (fun _ : E => ()) (fun _ : E => ()) where
  corner := ((Flag.deletionToggle keep).trans P.corner).trans (Flag.deletionToggle keep)
  involutive := by
    intro x
    simp only [Equiv.trans_apply, Flag.deletionToggle_twice, P.corner_corner]
  ne_self := by
    intro x h
    have h' := congrArg (Flag.deletionToggle keep) h
    simp only [Equiv.trans_apply, Flag.deletionToggle_twice] at h'
    exact P.corner_ne_self _ h'
  vertex := by intro x; exact Subsingleton.elim _ _

/-- Relabelling identifies the ordinary ribbon rotation with the common
smoothing permutation. -/
theorem smoothing_conjugate :
    Function.Semiconj (Flag.deletionToggle keep) (P.smoothing keep)
      (P.smoothingRibbon keep).rotation := by
  intro x
  simp only [smoothing, smoothingRibbon, Ribbon.rotation, Flag.deletionSwitch,
    Equiv.trans_apply, Flag.deletionToggle_twice]

/-- Until the first retained return, smoothing follows the original vertex
rotation through precisely the deleted flags. -/
theorem smoothing_trace (x : RetainedFlag keep) {j : ℕ} (hj : 0 < j)
    (hle : j ≤ PermutationDeletion.returnTime P.vertexNext (fun z => keep z.edge)
      (retainedAlong keep x)) :
    (P.smoothing keep : Flag E → Flag E)^[j] x.val =
      across ((P.vertexNext : Flag E → Flag E)^[j] (along x.val)) := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases hz : j = 0
      · subst j
        simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
          smoothing_apply, x.property, ite_true, vertexNext, Equiv.trans_apply, across_across]
      · have hjpos : 0 < j := by omega
        have hlt : j < PermutationDeletion.returnTime P.vertexNext (fun z => keep z.edge)
            (retainedAlong keep x) := by omega
        have hdel := PermutationDeletion.before_return_deleted P.vertexNext
          (fun z => keep z.edge) (retainedAlong keep x) hjpos hlt
        have hi := ih hjpos (by omega)
        rw [Function.iterate_succ_apply', hi, P.smoothing_apply]
        have hdel' : ¬keep (across ((P.vertexNext : Flag E → Flag E)^[j] (along x.val))).edge := hdel
        rw [ite_eq_right hdel', across_across, Function.iterate_succ_apply']
        simp only [vertexNext, Equiv.trans_apply, across_across]

/-- The first retained smoothing return occurs after exactly the same number
of steps as the original corner-splicing trace. -/
theorem smoothing_returnTime (x : RetainedFlag keep) :
    PermutationDeletion.returnTime (P.smoothing keep) (fun z => keep z.edge) x =
      PermutationDeletion.returnTime P.vertexNext (fun z => keep z.edge) (retainedAlong keep x) := by
  apply PermutationDeletion.returnTime_eq_of_trace
  · exact PermutationDeletion.returnTime_pos _ _ _
  · rw [P.smoothing_trace keep x (PermutationDeletion.returnTime_pos _ _ _) le_rfl]
    exact PermutationDeletion.returnTime_mem P.vertexNext (fun z => keep z.edge) (retainedAlong keep x)
  · intro j hj hlt
    rw [P.smoothing_trace keep x hj hlt.le]
    exact PermutationDeletion.before_return_deleted P.vertexNext (fun z => keep z.edge)
      (retainedAlong keep x) hj hlt

/-- The boundary rotation after actual deletion is the first-return
restriction of the common smoothing permutation. -/
theorem smoothing_firstReturn (x : RetainedFlag keep) :
    PermutationDeletion.firstReturn (P.smoothing keep) (fun z => keep z.edge) x =
      P.retainedCorner keep (retainedAlong keep x) := by
  apply Subtype.ext
  rw [PermutationDeletion.firstReturn_apply, P.smoothing_returnTime]
  rw [P.smoothing_trace keep x (PermutationDeletion.returnTime_pos _ _ _) le_rfl]
  rfl

end SidePairing
end WeightedMIS.EmbeddingFaces
