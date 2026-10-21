module

public import WeightedMIS.FiniteCycleLength
public import WeightedMIS.OriginalFaces

/-!
# Deterministic enumeration of actual ribbon boundary circles

The input supplies a finite flag order. The executable first-unseen scan
selects one root on every unoriented facial circle. Finite indices of this
computed list are explicitly equivalent to the mathematical face quotient;
computable first-return lengths produce actual closed boundary walks.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open SidePairing FiniteCycleEnumeration

deriving instance DecidableEq for Flag

namespace Ribbon

variable {V E : Type*} [Fintype E] [DecidableEq E] {left right : E → V}
    (R : Ribbon left right) (order : List (Flag E))

/-- Execute the first-unseen scan of both actual boundary orientations. -/
def enumeratedRoots : List (Flag E) :=
  representatives (bothTrace R.rotation along (Fintype.card (Flag E))) [] order

/-- Actual indices of the computed list of facial roots. -/
abbrev EnumeratedIndex := Fin (R.enumeratedRoots order).length

/-- The executable root at the supplied output index. -/
def enumeratedRoot (i : R.EnumeratedIndex order) : Flag E :=
  (R.enumeratedRoots order).get i

/-- No two selected roots are on the same actual unoriented circle. -/
theorem enumeratedRoots_pairwise :
    (R.enumeratedRoots order).Pairwise (fun x y => ¬R.SameFace x y) := by
  have h := representatives_pairwise
    (bothTrace R.rotation along (Fintype.card (Flag E))) [] order
  apply h.imp
  intro x y hxy hsame
  exact hxy ((mem_bothTrace_iff R.rotation along along_along x y).mpr hsame)

/-- The output indices map injectively to actual facial circles. -/
theorem enumeratedFace_injective :
    Function.Injective (fun i : R.EnumeratedIndex order => R.faceOf (R.enumeratedRoot order i)) := by
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · have hp := (R.enumeratedRoots_pairwise order).rel_get_of_lt h
    exact False.elim (hp (Quotient.exact hij))
  · exact h
  · have hp := (R.enumeratedRoots_pairwise order).rel_get_of_lt h
    exact False.elim (hp (Quotient.exact hij.symm))

/-- A complete supplied flag order makes the actual facial map surjective. -/
theorem enumeratedFace_surjective (horder : ∀ x : Flag E, x ∈ order) :
    Function.Surjective (fun i : R.EnumeratedIndex order => R.faceOf (R.enumeratedRoot order i)) := by
  intro f
  let x := R.faceRoot f
  have hc := representatives_cover (bothTrace R.rotation along (Fintype.card (Flag E)))
    (fun y => (mem_bothTrace_iff R.rotation along along_along y y).mpr (R.sameFace_refl y))
    [] order x (horder x)
  rcases hc with h | ⟨y, hy, hxy⟩
  · simp at h
  · obtain ⟨i, hi⟩ := List.get_of_mem hy
    refine ⟨i, ?_⟩
    have hs : R.SameFace y x := (mem_bothTrace_iff R.rotation along along_along y x).mp hxy
    change R.faceOf ((representatives (bothTrace R.rotation along
      (Fintype.card (Flag E))) [] order).get i) = f
    rw [hi]
    exact (Quotient.sound hs).trans (R.faceOf_root f)

/-- The computed root indices enumerate exactly the actual facial circles.
Only the proof-level inverse of this correspondence uses choice. -/
noncomputable def enumeratedFaceEquiv (horder : ∀ x : Flag E, x ∈ order) :
    R.EnumeratedIndex order ≃ R.FaceIndex :=
  Equiv.ofBijective (fun i => R.faceOf (R.enumeratedRoot order i))
    ⟨R.enumeratedFace_injective order, R.enumeratedFace_surjective order horder⟩

@[simp] theorem enumeratedFaceEquiv_apply (horder : ∀ x : Flag E, x ∈ order)
    (i : R.EnumeratedIndex order) :
    R.enumeratedFaceEquiv order horder i = R.faceOf (R.enumeratedRoot order i) := rfl

/-- The number of selected faces never exceeds the supplied scan length. -/
theorem enumeratedRoots_length_le : (R.enumeratedRoots order).length ≤ order.length :=
  representatives_length_le _ [] order

/-- The deterministic scan has a cubic bound for a flag order of linear size. -/
theorem enumerated_scanWork_le :
    scanWork (bothTrace R.rotation along (Fintype.card (Flag E)))
      (fun _ => 3 * Fintype.card (Flag E)) [] order ≤
      order.length * (4 * Fintype.card (Flag E) * order.length +
        3 * Fintype.card (Flag E) + 2) :=
  bothTrace_scanWork_le _ _ _ _

/-- The executable actual closed boundary at a computed facial root. -/
def enumeratedFace (i : R.EnumeratedIndex order) : Faces.Face left right where
  root := (R.enumeratedRoot order i).vertex left right
  boundary := (R.trace (R.enumeratedRoot order i)
    (periodLength R.rotation (R.enumeratedRoot order i))).castEnd (by
      apply congrArg (Flag.vertex left right)
      rw [periodLength_eq]
      exact Function.iterate_minimalPeriod)

/-- The computed face is the genuine least-period closed boundary trace. -/
theorem enumeratedFace_eq (i : R.EnumeratedIndex order) :
    R.enumeratedFace order i = R.tracedFace (R.enumeratedRoot order i) := by
  let x := R.enumeratedRoot order i
  have hmk : ∀ (n m : ℕ) (hn : (R.rotation : Flag E → Flag E)^[n] x = x)
      (hm : (R.rotation : Flag E → Flag E)^[m] x = x), n = m →
      (⟨x.vertex left right, (R.trace x n).castEnd (congrArg (Flag.vertex left right) hn)⟩ :
        Faces.Face left right) =
      ⟨x.vertex left right, (R.trace x m).castEnd (congrArg (Flag.vertex left right) hm)⟩ := by
    intro n m hn hm h
    subst m
    rfl
  have hn : (R.rotation : Flag E → Flag E)^[periodLength R.rotation x] x = x := by
    rw [periodLength_eq]
    exact Function.iterate_minimalPeriod
  exact hmk _ _ hn Function.iterate_minimalPeriod (periodLength_eq R.rotation x)

@[simp] theorem enumeratedFace_length (i : R.EnumeratedIndex order) :
    (R.enumeratedFace order i).boundary.length =
      periodLength R.rotation (R.enumeratedRoot order i) := by
  simp only [enumeratedFace, Faces.Boundary.castEnd_length, R.trace_length]

/-- An actual bounded-size facial walk, with no selected quotient root in the
executable definition. -/
theorem enumeratedFace_positive (i : R.EnumeratedIndex order) :
    0 < (R.enumeratedFace order i).boundary.length := by
  rw [R.enumeratedFace_length]
  exact periodLength_pos _ _

theorem enumeratedFace_length_le (i : R.EnumeratedIndex order) :
    (R.enumeratedFace order i).boundary.length ≤ 4 * Fintype.card E := by
  rw [R.enumeratedFace_length, ← Flag.card]
  exact periodLength_le_card _ _

end Ribbon
end WeightedMIS.EmbeddingFaces
