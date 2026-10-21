module

public import WeightedMIS.RationalElimination

/-!
# Materialized rational elimination

Rows and generators are stored in fixed-size arrays. Each pivot projection
materializes every new coordinate, so later constraints read stored values
instead of recursively evaluating earlier vector expressions. The resulting
arrays refine the deterministic kernel-generation specification exactly.
-/

@[expose] public section

namespace WeightedMIS.StoredElimination

open Matrix RationalElimination

variable {m : ℕ}

/-- Stored coordinates viewed as a mathematical vector. -/
def decode (v : Vector ℚ m) : Fin m → ℚ := fun i => v[i.val]

/-- Store all coordinates of a mathematical vector in an array. -/
def encode (v : Fin m → ℚ) : Vector ℚ m := Vector.ofFn v

@[simp] theorem decode_encode (v : Fin m → ℚ) : decode (encode v) = v := by
  ext i
  simp [decode, encode]

/-- Dot product of two materialized vectors. -/
def dot (c v : Vector ℚ m) : ℚ := dotProduct (decode c) (decode v)

/-- Materialize projection along a selected pivot with cached pivot value. -/
def projectVector (c p : Vector ℚ m) (pivotValue : ℚ) (v : Vector ℚ m) : Vector ℚ m :=
  let coefficient := dot c v / pivotValue
  encode (fun i => v.get i - coefficient * p.get i)

theorem decode_projectVector (c p v : Vector ℚ m) :
    decode (projectVector c p (dot c p) v) =
      RationalElimination.project (rowMap (decode c)) (decode p) (decode v) := by
  rw [project_apply]
  ext i
  simp [projectVector, decode, rowMap, dot, dotProductBilin, encode, Vector.get, Fin.val_cast]

/-- Process one stored equation, selecting the first nonzero pivot. -/
def cut (c : Vector ℚ m) (vs : List (Vector ℚ m)) : List (Vector ℚ m) :=
  (RationalElimination.cut (rowMap (decode c)) (vs.map decode)).map encode

/-- Stored projection implements the mathematical projection specification. -/
theorem decode_cut (c : Vector ℚ m) (vs : List (Vector ℚ m)) :
    (cut c vs).map decode = RationalElimination.cut (rowMap (decode c)) (vs.map decode) := by
  simp [cut, List.map_map, Function.comp_def]

/-- Process the stored constraint rows in their given order. -/
def eliminateRows : List (Vector ℚ m) → List (Vector ℚ m) → List (Vector ℚ m)
  | [], vs => vs
  | c :: cs, vs => eliminateRows cs (cut c vs)

theorem decode_eliminateRows (cs vs : List (Vector ℚ m)) :
    (eliminateRows cs vs).map decode =
      RationalElimination.eliminateRows (cs.map (fun c => rowMap (decode c))) (vs.map decode) := by
  induction cs generalizing vs with
  | nil => rfl
  | cons c cs ih => simp [eliminateRows, ih, decode_cut, RationalElimination.eliminateRows]

/-- Initial coordinate vectors, each stored in its own array. -/
def coordinateVectors (m : ℕ) : List (Vector ℚ m) :=
  (RationalElimination.coordinateVectors m).map encode

theorem decode_coordinateVectors (m : ℕ) :
    (coordinateVectors m).map decode = RationalElimination.coordinateVectors m := by
  simp [coordinateVectors, List.map_map, Function.comp_def]

/-- Array-based rational nullspace generation for an arbitrary stored matrix. -/
def kernelGenerators {n m : ℕ} (A : Vector (Vector ℚ m) n) : List (Vector ℚ m) :=
  eliminateRows A.toList (coordinateVectors m)

/-- Materialized output agrees with the verified rational elimination result. -/
theorem decode_kernelGenerators {n m : ℕ} (A : Vector (Vector ℚ m) n) :
    (kernelGenerators A).map decode =
      RationalElimination.kernelGenerators (fun i j => (A.get i).get j) := by
  rw [kernelGenerators, decode_eliminateRows, decode_coordinateVectors]
  unfold RationalElimination.kernelGenerators
  congr 1
  have heq : A.toList = List.ofFn (fun i : Fin n => A[i.val]) := by
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  rw [heq, List.map_ofFn]
  congr 1

/-- The materialized algorithm computes an exact generating family for the
nullspace of every rational matrix. -/
theorem kernelGenerators_span {n m : ℕ} (A : Vector (Vector ℚ m) n) :
    RationalElimination.listSpan ((kernelGenerators A).map decode) =
      LinearMap.ker (Matrix.mulVecLin (fun i j => (A.get i).get j : Matrix (Fin n) (Fin m) ℚ)) := by
  rw [decode_kernelGenerators]
  exact RationalElimination.kernelGenerators_span _

end WeightedMIS.StoredElimination
