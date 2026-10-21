module

public import WeightedMIS.DeterministicComplement

/-!
# Operation traces for stored elimination and complement selection

The counters use scalar arithmetic operations, scalar comparisons, coordinate
reads and writes, and list visits as unit operations. They follow the actual
first-pivot and candidate-selection branches. In particular, the projection
counter permits both dot products to be evaluated anew at every coordinate,
as in the existing materialized implementation. Bit costs of the scalar
operations are a separate obligation.
-/

@[expose] public section

namespace WeightedMIS.StoredEliminationCost

open Matrix
open StoredElimination

variable {m : ℕ}

/-- Evaluate a dot product in coordinate order, recording two coordinate reads,
one multiplication and one addition per coordinate. -/
def dotLoop (c v : Vector ℚ m) : List (Fin m) → ℚ × ℕ
  | [] => (0, 0)
  | i :: is =>
      let r := dotLoop c v is
      (c.get i * v.get i + r.1, 4 + r.2)

theorem dotLoop_spec (c v : Vector ℚ m) (is : List (Fin m)) :
    (dotLoop c v is).1 = (is.map (fun i => c.get i * v.get i)).sum ∧
      (dotLoop c v is).2 = 4 * is.length := by
  induction is with
  | nil => simp [dotLoop]
  | cons i is ih => simp [dotLoop, ih.1, ih.2, Nat.mul_add, Nat.add_comm]

/-- A counted evaluation of the stored dot product. -/
def countedDot (c v : Vector ℚ m) : ℚ × ℕ := dotLoop c v (List.finRange m)

theorem countedDot_spec (c v : Vector ℚ m) :
    (countedDot c v).1 = dot c v ∧ (countedDot c v).2 = 4 * m := by
  have h := dotLoop_spec c v (List.finRange m)
  constructor
  · rw [countedDot, h.1]
    simp [dot, dotProduct, decode, ← List.ofFn_id, List.sum_ofFn, Vector.get]
  · simpa [countedDot] using h.2

/-- Count the pivot search itself, including its scalar comparison and list
visit. The return value is the actual first stored pivot. -/
def pivot (c : Vector ℚ m) : List (Vector ℚ m) → Option (Vector ℚ m) × ℕ
  | [] => (none, 0)
  | v :: vs =>
      let q := countedDot c v
      if q.1 ≠ 0 then (some v, q.2 + 2)
      else let r := pivot c vs; (r.1, q.2 + 2 + r.2)

theorem pivot_spec (c : Vector ℚ m) (vs : List (Vector ℚ m)) :
    (pivot c vs).1 = vs.find? (fun v => decide (dot c v ≠ 0)) ∧
      (pivot c vs).2 ≤ vs.length * (4 * m + 2) := by
  induction vs with
  | nil => simp [pivot]
  | cons v vs ih =>
      simp only [pivot, (countedDot_spec c v).1, (countedDot_spec c v).2]
      split
      next h =>
        constructor
        · simp [List.find?, h]
        · simp only [List.length_cons]; nlinarith
      next h =>
        constructor
        · simpa [List.find?, h] using ih.1
        · simp only [List.length_cons]; nlinarith [ih.2]

/-- The counted pivot is exactly the pivot used by the existing cut. -/
theorem pivot_decoded (c : Vector ℚ m) (vs : List (Vector ℚ m)) :
    (vs.map decode).find? (fun v => decide (RationalElimination.rowMap (decode c) v ≠ 0)) =
      (pivot c vs).1.map decode := by
  rw [List.find?_map, (pivot_spec c vs).1]
  rfl

/-- Evaluate one coordinate of the projection, allowing the dot products to be
recomputed exactly as in the materializing specification. -/
def projectedCoordinate (c p v : Vector ℚ m) (i : Fin m) : ℚ × ℕ :=
  let a := countedDot c v
  let b := countedDot c p
  (v.get i - (a.1 / b.1) * p.get i, a.2 + b.2 + 6)

theorem projectedCoordinate_spec (c p v : Vector ℚ m) (i : Fin m) :
    (projectedCoordinate c p v i).1 =
        RationalElimination.project (RationalElimination.rowMap (decode c)) (decode p)
          (decode v) i ∧
      (projectedCoordinate c p v i).2 = 8 * m + 6 := by
  rw [RationalElimination.project_apply]
  simp [projectedCoordinate, (countedDot_spec c v).1, (countedDot_spec c p).1,
    (countedDot_spec c v).2, (countedDot_spec c p).2, dot,
    RationalElimination.rowMap_apply, decode, Vector.get]
  omega

/-- The operation count for materializing one projected vector. Each coordinate
uses two dot products, two reads, a division, multiplication, subtraction and
write. One additional operation visits its list cell. -/
def projectWork (c p v : Vector ℚ m) : ℕ :=
  ((List.finRange m).map fun _ =>
    (countedDot c v).2 + (countedDot c p).2 + 6).sum + 1

theorem projectWork_eq (c p v : Vector ℚ m) :
    projectWork c p v = m * (8 * m + 6) + 1 := by
  simp [projectWork, (countedDot_spec c v).2, (countedDot_spec c p).2,
    List.sum_replicate, Nat.mul_add]
  ring

/-- Count one call of the existing materialized cut. The no-pivot branch
includes its decode/encode copy, even though that copy preserves the values. -/
def cutWork (c : Vector ℚ m) (vs : List (Vector ℚ m)) : ℕ :=
  let p := pivot c vs
  p.2 + match p.1 with
    | none => vs.length * (2 * m + 1)
    | some v => (vs.map (projectWork c v)).sum

/-- Uniform per-generator polynomial, including pivot search and projection. -/
def cutFactor (m : ℕ) : ℕ := 8 * m ^ 2 + 10 * m + 3

theorem cutWork_le (c : Vector ℚ m) (vs : List (Vector ℚ m)) :
    cutWork c vs ≤ vs.length * cutFactor m := by
  have hp := (pivot_spec c vs).2
  unfold cutWork
  cases h : (pivot c vs).1 with
  | none =>
      simp only [h]
      unfold cutFactor
      nlinarith
  | some p =>
      simp only [h]
      have hs : (vs.map (projectWork c p)).sum =
          vs.length * (m * (8 * m + 6) + 1) := by
        have hf : projectWork c p = fun _ => m * (8 * m + 6) + 1 :=
          funext (projectWork_eq c p)
        rw [hf]
        simp
      rw [hs]
      unfold cutFactor
      nlinarith

theorem cut_length (c : Vector ℚ m) (vs : List (Vector ℚ m)) :
    (StoredElimination.cut c vs).length = vs.length := by
  simp [StoredElimination.cut, RationalElimination.cut_length]

/-- Count the successive stored cuts on the actual intermediate lists. -/
def eliminateWork : List (Vector ℚ m) → List (Vector ℚ m) → ℕ
  | [], _ => 0
  | c :: cs, vs => cutWork c vs + eliminateWork cs (StoredElimination.cut c vs)

theorem eliminateWork_le (cs vs : List (Vector ℚ m)) :
    eliminateWork cs vs ≤ cs.length * vs.length * cutFactor m := by
  induction cs generalizing vs with
  | nil => simp [eliminateWork]
  | cons c cs ih =>
      have h := ih (StoredElimination.cut c vs)
      rw [cut_length] at h
      have hc := cutWork_le c vs
      simp only [eliminateWork, List.length_cons]
      nlinarith

theorem coordinateVectors_length (m : ℕ) :
    (StoredElimination.coordinateVectors m).length = m := by
  simp [StoredElimination.coordinateVectors, RationalElimination.coordinateVectors]

/-- Initial array construction followed by all matrix rows. -/
def kernelWork {n m : ℕ} (A : Vector (Vector ℚ m) n) : ℕ :=
  m * (m + 1) + eliminateWork A.toList (StoredElimination.coordinateVectors m)

theorem kernelWork_le {n m : ℕ} (A : Vector (Vector ℚ m) n) :
    kernelWork A ≤ m * (m + 1) + n * m * cutFactor m := by
  have h := eliminateWork_le A.toList (StoredElimination.coordinateVectors m)
  simpa [kernelWork, coordinateVectors_length] using Nat.add_le_add_left h (m * (m + 1))

/-- A counted short-circuit scan of annihilator generators. -/
def anyWork (x : Fin m → ℚ) : List (Fin m → ℚ) → ℕ
  | [] => 0
  | y :: ys => (4 * m + 2) + if dotProduct x y ≠ 0 then 0 else anyWork x ys

theorem anyWork_le (x : Fin m → ℚ) (ys : List (Fin m → ℚ)) :
    anyWork x ys ≤ ys.length * (4 * m + 2) := by
  induction ys with
  | nil => simp [anyWork]
  | cons y ys ih =>
      simp only [anyWork, List.length_cons]
      split <;> nlinarith

/-- Materialize the input rows, construct the coordinate basis, execute all
cuts, then scan the resulting annihilator with the actual short-circuit test. -/
def outsideWork (rows : List (Fin m → ℚ)) (x : Fin m → ℚ) : ℕ :=
  rows.length * (m + 1) + m * (m + 1) +
    eliminateWork (rows.map StoredElimination.encode)
      (StoredElimination.coordinateVectors m) +
    anyWork x (DeterministicComplement.annihilatorGenerators rows)

def outsideBound (m n : ℕ) : ℕ :=
  n * (m + 1) + m * (m + 1) + n * m * cutFactor m + m * (4 * m + 2)

theorem outsideWork_le (rows : List (Fin m → ℚ)) (x : Fin m → ℚ) :
    outsideWork rows x ≤ outsideBound m rows.length := by
  have he := eliminateWork_le (rows.map StoredElimination.encode)
    (StoredElimination.coordinateVectors m)
  simp only [List.length_map, coordinateVectors_length] at he
  have ha := anyWork_le x (DeterministicComplement.annihilatorGenerators rows)
  have hl : (DeterministicComplement.annihilatorGenerators rows).length = m := by
    rw [DeterministicComplement.annihilatorGenerators_eq]
    simp [RationalElimination.eliminateRows_length, RationalElimination.coordinateVectors]
  rw [hl] at ha
  unfold outsideWork outsideBound
  omega

theorem outsideBound_mono {a b : ℕ} (h : a ≤ b) :
    outsideBound m a ≤ outsideBound m b := by
  unfold outsideBound
  gcongr

/-- Follow precisely the existing complement-selection branches. -/
def selectWork (rows : List (Fin m → ℚ)) : List (Fin m → ℚ) → ℕ
  | [] => 0
  | v :: vs => outsideWork rows v + 1 +
      if DeterministicComplement.outside rows v then selectWork (v :: rows) vs
      else selectWork rows vs

theorem selectWork_le (rows candidates : List (Fin m → ℚ)) :
    selectWork rows candidates ≤
      candidates.length * (outsideBound m (rows.length + candidates.length) + 1) := by
  induction candidates generalizing rows with
  | nil => simp [selectWork]
  | cons v vs ih =>
      have ho := outsideWork_le rows v
      have hb := outsideBound_mono (m := m)
        (show rows.length ≤ rows.length + (v :: vs).length by omega)
      simp only [selectWork]
      split
      next h =>
        have hi := ih (v :: rows)
        simp only [List.length_cons] at hi ⊢ hb
        have heq : rows.length + 1 + vs.length = rows.length + (vs.length + 1) := by omega
        rw [heq] at hi
        nlinarith
      next h =>
        have hi := ih rows
        have hm := outsideBound_mono (m := m)
          (show rows.length + vs.length ≤ rows.length + (v :: vs).length by simp)
        simp only [List.length_cons] at hm ⊢ hb
        nlinarith

end WeightedMIS.StoredEliminationCost
