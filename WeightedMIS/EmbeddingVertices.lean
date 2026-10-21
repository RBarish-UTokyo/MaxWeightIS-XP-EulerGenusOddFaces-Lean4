module

public import WeightedMIS.EmbeddingFaces
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Boundary endpoints and cyclic corners

The face successor is the cyclic successor of actual traversal positions.
Its endpoint compatibility follows from the indexed boundary walk itself.
-/

@[expose] public section

namespace WeightedMIS.Faces.Boundary

variable {V E : Type*} {left right : E → V}

/-- Vertices visited by the actual boundary, including both endpoints. -/
def vertexAt {a b : V} : (p : Boundary left right a b) → Fin (p.length + 1) → V
  | .nil _, _ => a
  | .forward e p, i => Fin.lastCases (right e) p.vertexAt i
  | .backward e p, i => Fin.lastCases (left e) p.vertexAt i

@[simp] theorem vertexAt_zero {a b : V} (p : Boundary left right a b) :
    p.vertexAt 0 = a := by
  induction p with
  | nil => rfl
  | forward e p ih =>
      change Fin.lastCases (right e) p.vertexAt (Fin.castSucc 0) = a
      rw [Fin.lastCases_castSucc]
      exact ih
  | backward e p ih =>
      change Fin.lastCases (left e) p.vertexAt (Fin.castSucc 0) = a
      rw [Fin.lastCases_castSucc]
      exact ih

@[simp] theorem vertexAt_last {a b : V} (p : Boundary left right a b) :
    p.vertexAt (Fin.last p.length) = b := by
  cases p <;> simp [vertexAt, length]

/-- Every occurrence has its actual graph-edge endpoints, in its recorded
forward or backward direction. -/
theorem vertexAt_endpoints {a b : V} (p : Boundary left right a b) (i : Fin p.length) :
    (p.vertexAt i.castSucc =
      if p.forwardAt i then left (p.edgeAt i) else right (p.edgeAt i)) ∧
    (p.vertexAt i.succ =
      if p.forwardAt i then right (p.edgeAt i) else left (p.edgeAt i)) := by
  induction p with
  | nil => exact Fin.elim0 i
  | forward e p ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [length, vertexAt, edgeAt, forwardAt, Fin.lastCases_last,
          Fin.lastCases_castSucc, Fin.succ_last, ite_true, vertexAt_last, and_self]
      · simpa only [length, vertexAt, edgeAt, forwardAt, Fin.succ_castSucc,
          Fin.lastCases_castSucc] using ih j
  | backward e p ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [length, vertexAt, edgeAt, forwardAt, Fin.lastCases_last,
          Fin.lastCases_castSucc, Fin.succ_last, Bool.false_eq_true, ite_false,
          vertexAt_last, and_self]
      · simpa only [length, vertexAt, edgeAt, forwardAt, Fin.succ_castSucc,
          Fin.lastCases_castSucc] using ih j

/-- The start vertex at one occurrence. -/
def startAt {a b : V} (p : Boundary left right a b) (i : Fin p.length) : V :=
  if p.forwardAt i then left (p.edgeAt i) else right (p.edgeAt i)

/-- The end vertex at one occurrence. -/
def endAt {a b : V} (p : Boundary left right a b) (i : Fin p.length) : V :=
  if p.forwardAt i then right (p.edgeAt i) else left (p.edgeAt i)

/-- Cyclic successor identifies consecutive entries of a closed vertex list. -/
theorem cyclic_vertices {n : ℕ} (v : Fin (n + 1) → V)
    (hv : v (Fin.last n) = v 0) (i : Fin n) :
    v i.succ = v (finRotate n i).castSucc := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      by_cases hi : i = Fin.last n
      · subst i
        simpa only [finRotate_last, Fin.castSucc_zero, Fin.succ_last] using hv
      · congr 1
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact (coe_finRotate_of_ne_last hi).symm

/-- Consecutive occurrences around a closed boundary share their vertex. -/
theorem endAt_eq_startAt_rotate {a : V} (p : Boundary left right a a)
    (i : Fin p.length) : p.endAt i = p.startAt (finRotate p.length i) := by
  unfold endAt startAt
  rw [← (p.vertexAt_endpoints i).2, ← (p.vertexAt_endpoints _).1]
  exact cyclic_vertices p.vertexAt (p.vertexAt_last.trans p.vertexAt_zero.symm) i

end WeightedMIS.Faces.Boundary

namespace WeightedMIS.EmbeddingFaces

variable {V E F : Type*} {left right : E → V} {faces : F → Faces.Face left right}

/-- Cyclic face successor on actual indexed occurrences. -/
def faceNext : Equiv.Perm (Occurrence faces) :=
  Equiv.sigmaCongrRight (fun f => finRotate (faces f).boundary.length)

/-- The cyclic predecessor is the inverse successor permutation. -/
def facePrev : Equiv.Perm (Occurrence faces) := (faceNext (faces := faces)).symm

end WeightedMIS.EmbeddingFaces
