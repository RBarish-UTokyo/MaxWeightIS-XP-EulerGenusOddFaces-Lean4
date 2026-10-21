module

public import WeightedMIS.EmbeddingDeletion

/-!
# Boundary tracing from an actual corner matching

A corner system pairs the endpoint flags at each supplied graph vertex.
Composing edge traversal with this matching gives the actual boundary
rotation. Its finite periodic traces are genuine closed edge walks.
-/

@[expose] public section

namespace WeightedMIS.Faces.Boundary

variable {V E : Type*} {left right : E → V} {a b c : V}

/-- Transport only the final vertex of a boundary walk. -/
def castEnd (p : Boundary left right a b) (h : b = c) : Boundary left right a c := h ▸ p

@[simp] theorem castEnd_length (p : Boundary left right a b) (h : b = c) :
    (p.castEnd h).length = p.length := by subst c; rfl

@[simp] theorem castEnd_edgeAt (p : Boundary left right a b) (h : b = c)
    (i : Fin (p.castEnd h).length) :
    (p.castEnd h).edgeAt i = p.edgeAt ⟨i.val, by simpa using i.isLt⟩ := by
  subst c
  rfl

@[simp] theorem castEnd_forwardAt (p : Boundary left right a b) (h : b = c)
    (i : Fin (p.castEnd h).length) :
    (p.castEnd h).forwardAt i = p.forwardAt ⟨i.val, by simpa using i.isLt⟩ := by
  subst c
  rfl

end WeightedMIS.Faces.Boundary

namespace WeightedMIS.EmbeddingFaces

open SidePairing

variable {V E : Type*} {left right : E → V}

/-- A corner matching with the local properties needed for boundary tracing.
Connected vertex links are a further condition, proved separately after deletion. -/
structure Ribbon (left right : E → V) where
  corner : Equiv.Perm (Flag E)
  involutive : Function.Involutive corner
  ne_self : ∀ x, corner x ≠ x
  vertex : ∀ x, (corner x).vertex left right = x.vertex left right

namespace Ribbon

variable (R : Ribbon left right)

/-- Traverse an edge side and then turn through its actual corner. -/
def rotation : Equiv.Perm (Flag E) := along.trans R.corner

theorem rotation_vertex (x : Flag E) :
    (R.rotation x).vertex left right = (along x).vertex left right := R.vertex _

/-- Append precisely the edge side at the current flag. -/
def appendFlag {a : V} (x : Flag E) (p : Faces.Boundary left right a (x.vertex left right)) :
    Faces.Boundary left right a ((R.rotation x).vertex left right) := by
  rcases x with ⟨e, s, t⟩
  cases t
  · have h : (R.rotation ⟨e, s, false⟩).vertex left right = right e := R.rotation_vertex _
    exact (Faces.Boundary.forward e p).castEnd h.symm
  · have h : (R.rotation ⟨e, s, true⟩).vertex left right = left e := R.rotation_vertex _
    exact (Faces.Boundary.backward e p).castEnd h.symm

@[simp] theorem appendFlag_length {a : V} (x : Flag E)
    (p : Faces.Boundary left right a (x.vertex left right)) :
    (R.appendFlag x p).length = p.length + 1 := by
  rcases x with ⟨e, s, t⟩
  cases t <;> simp [appendFlag, Faces.Boundary.length] <;> rfl

/-- At old positions appending a flag leaves the recorded edge unchanged. -/
theorem appendFlag_edgeAt_old {a : V} (x : Flag E)
    (p : Faces.Boundary left right a (x.vertex left right)) (i : Fin p.length) :
    (R.appendFlag x p).edgeAt ⟨i.val, by rw [R.appendFlag_length]; omega⟩ = p.edgeAt i := by
  rcases x with ⟨e, s, t⟩
  cases t <;> simp only [appendFlag, Faces.Boundary.castEnd_edgeAt, Faces.Boundary.edgeAt]
  all_goals
    change Fin.lastCases e p.edgeAt i.castSucc = p.edgeAt i
    rw [Fin.lastCases_castSucc]

/-- The last position records exactly the edge just traversed. -/
theorem appendFlag_edgeAt_last {a : V} (x : Flag E)
    (p : Faces.Boundary left right a (x.vertex left right)) :
    (R.appendFlag x p).edgeAt ⟨p.length, by rw [R.appendFlag_length]; omega⟩ = x.edge := by
  rcases x with ⟨e, s, t⟩
  cases t <;> simp only [appendFlag, Faces.Boundary.castEnd_edgeAt, Faces.Boundary.edgeAt]
  all_goals
    change Fin.lastCases e p.edgeAt (Fin.last p.length) = e
    rw [Fin.lastCases_last]

/-- The actual length-`n` boundary trace of the rotation, with its starting
and ending vertices enforced by the indexed walk type. -/
def trace (x : Flag E) : (n : ℕ) → Faces.Boundary left right (x.vertex left right)
    (((R.rotation : Flag E → Flag E)^[n] x).vertex left right)
  | 0 => .nil _
  | n + 1 => (R.appendFlag ((R.rotation : Flag E → Flag E)^[n] x) (trace x n)).castEnd
      (congrArg (Flag.vertex left right) (Function.iterate_succ_apply' R.rotation n x).symm)

@[simp] theorem trace_length (x : Flag E) (n : ℕ) : (R.trace x n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [trace, Faces.Boundary.castEnd_length, R.appendFlag_length, ih]

/-- Every occurrence of a trace is the corresponding edge of the actual
rotation orbit. -/
theorem trace_edgeAt (x : Flag E) (n : ℕ) (i : Fin n) :
    (R.trace x n).edgeAt ⟨i.val, by simp⟩ =
      ((R.rotation : Flag E → Flag E)^[i.val] x).edge := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      by_cases hi : i.val < n
      · have hold := R.appendFlag_edgeAt_old
          ((R.rotation : Flag E → Flag E)^[n] x) (R.trace x n)
          ⟨i.val, by simpa using hi⟩
        simpa only [trace, Faces.Boundary.castEnd_edgeAt] using hold.trans (ih ⟨i.val, hi⟩)
      · have hilast : i.val = n := by omega
        have hiEq : i = Fin.last n := Fin.ext hilast
        subst i
        simpa only [trace, Faces.Boundary.castEnd_edgeAt, Fin.val_last, R.trace_length] using R.appendFlag_edgeAt_last
          ((R.rotation : Flag E → Flag E)^[n] x) (R.trace x n)

/-- Appending a flag preserves the directions at previous occurrences. -/
theorem appendFlag_forwardAt_old {a : V} (x : Flag E)
    (p : Faces.Boundary left right a (x.vertex left right)) (i : Fin p.length) :
    (R.appendFlag x p).forwardAt ⟨i.val, by rw [R.appendFlag_length]; omega⟩ = p.forwardAt i := by
  rcases x with ⟨e, s, t⟩
  cases t <;> simp only [appendFlag, Faces.Boundary.castEnd_forwardAt, Faces.Boundary.forwardAt]
  · change Fin.lastCases true p.forwardAt i.castSucc = p.forwardAt i
    rw [Fin.lastCases_castSucc]
  · change Fin.lastCases false p.forwardAt i.castSucc = p.forwardAt i
    rw [Fin.lastCases_castSucc]

/-- A traversal is forward precisely when it starts at the left endpoint. -/
theorem appendFlag_forwardAt_last {a : V} (x : Flag E)
    (p : Faces.Boundary left right a (x.vertex left right)) :
    (R.appendFlag x p).forwardAt ⟨p.length, by rw [R.appendFlag_length]; omega⟩ = !x.endpoint := by
  rcases x with ⟨e, s, t⟩
  cases t <;> simp only [appendFlag, Faces.Boundary.castEnd_forwardAt, Faces.Boundary.forwardAt]
  · change Fin.lastCases true p.forwardAt (Fin.last p.length) = true
    rw [Fin.lastCases_last]
  · change Fin.lastCases false p.forwardAt (Fin.last p.length) = false
    rw [Fin.lastCases_last]

theorem trace_forwardAt (x : Flag E) (n : ℕ) (i : Fin n) :
    (R.trace x n).forwardAt ⟨i.val, by simp⟩ =
      !((R.rotation : Flag E → Flag E)^[i.val] x).endpoint := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      by_cases hi : i.val < n
      · have hold := R.appendFlag_forwardAt_old
          ((R.rotation : Flag E → Flag E)^[n] x) (R.trace x n)
          ⟨i.val, by simpa using hi⟩
        simpa only [trace, Faces.Boundary.castEnd_forwardAt] using hold.trans (ih ⟨i.val, hi⟩)
      · have hilast : i.val = n := by omega
        have hiEq : i = Fin.last n := Fin.ext hilast
        subst i
        simpa only [trace, Faces.Boundary.castEnd_forwardAt, Fin.val_last, R.trace_length]
          using R.appendFlag_forwardAt_last
            ((R.rotation : Flag E → Flag E)^[n] x) (R.trace x n)

/-- The closed facial walk traced from one flag through its least positive
rotation period. -/
noncomputable def tracedFace (x : Flag E) : Faces.Face left right where
  root := x.vertex left right
  boundary := (R.trace x (Function.minimalPeriod R.rotation x)).castEnd
    (congrArg (Flag.vertex left right) (Function.iterate_minimalPeriod))

@[simp] theorem tracedFace_length (x : Flag E) :
    (R.tracedFace x).boundary.length = Function.minimalPeriod R.rotation x := by
  simp [tracedFace]

/-- Facial occurrences retain the exact original edge labels. -/
theorem tracedFace_edgeAt (x : Flag E) (i : Fin (R.tracedFace x).boundary.length) :
    (R.tracedFace x).boundary.edgeAt i = ((R.rotation : Flag E → Flag E)^[i.val] x).edge := by
  exact (Faces.Boundary.castEnd_edgeAt (R.trace x (Function.minimalPeriod R.rotation x))
    (congrArg (Flag.vertex left right) Function.iterate_minimalPeriod) i).trans
      (R.trace_edgeAt x (Function.minimalPeriod R.rotation x)
        ⟨i.val, by simpa using i.isLt⟩)

/-- Facial occurrences retain their actual traversal directions. -/
theorem tracedFace_forwardAt (x : Flag E) (i : Fin (R.tracedFace x).boundary.length) :
    (R.tracedFace x).boundary.forwardAt i = !((R.rotation : Flag E → Flag E)^[i.val] x).endpoint := by
  exact (Faces.Boundary.castEnd_forwardAt (R.trace x (Function.minimalPeriod R.rotation x))
    (congrArg (Flag.vertex left right) Function.iterate_minimalPeriod) i).trans
      (R.trace_forwardAt x (Function.minimalPeriod R.rotation x)
        ⟨i.val, by simpa using i.isLt⟩)

theorem tracedFace_positive [Fintype E] (x : Flag E) :
    0 < (R.tracedFace x).boundary.length := by
  rw [R.tracedFace_length]
  exact Function.minimalPeriod_pos_of_mem_periodicPts (R.rotation.injective.mem_periodicPts x)

theorem tracedFace_length_le [Fintype E] (x : Flag E) :
    (R.tracedFace x).boundary.length ≤ 4 * Fintype.card E := by
  rw [R.tracedFace_length, ← Flag.card]
  exact Function.minimalPeriod_le_card

end Ribbon
end WeightedMIS.EmbeddingFaces
