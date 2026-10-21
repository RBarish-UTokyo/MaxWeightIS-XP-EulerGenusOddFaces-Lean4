module

public import WeightedMIS.Incidence
public import Mathlib.Data.Fintype.BigOperators

/-!
# Alternating rows of closed boundary walks

A boundary below is data recording every traversal of an endpoint graph edge,
in either direction. Its row adds the alternating integer sign of every
occurrence, including repetitions. Closed even boundaries give the equations
`B*A = 0` and `B*1 = 0`. A separate two-sides occurrence count bounds the sum
of the absolute values in each even-face column by two.
Realizing these data as faces of a surface embedding is a separate obligation.
-/

@[expose] public section

namespace WeightedMIS.Faces

open Matrix Finset

universe u v w
variable {V : Type u} {E : Type v}

/-- Actual edge traversals, with endpoints enforced by the indices. -/
inductive Boundary (left right : E → V) : V → V → Type (max u v) where
  | nil (a : V) : Boundary left right a a
  | forward {a : V} (e : E) : Boundary left right a (left e) →
      Boundary left right a (right e)
  | backward {a : V} (e : E) : Boundary left right a (right e) →
      Boundary left right a (left e)

namespace Boundary

variable {left right : E → V}

/-- Number of edge occurrences in the boundary. -/
def length {a b : V} : Boundary left right a b → ℕ
  | .nil _ => 0
  | .forward _ p => p.length + 1
  | .backward _ p => p.length + 1

/-- The corresponding genuine graph walk of the same length. -/
theorem toWalk {a b : V} (p : Boundary left right a b) :
    Incidence.Walk left right a b p.length := by
  induction p with
  | nil => exact .nil _
  | forward e p ih => exact .forward e rfl ih
  | backward e p ih => exact .backward e rfl ih

/-- Alternating coefficients add every occurrence of each edge label. -/
def row [DecidableEq E] {a b : V} : Boundary left right a b → E → ℤ
  | .nil _, _ => 0
  | .forward e p, f => p.row f + if f = e then (-1 : ℤ) ^ p.length else 0
  | .backward e p, f => p.row f + if f = e then (-1 : ℤ) ^ p.length else 0

/-- Number of occurrences of a given edge label, irrespective of direction. -/
def count [DecidableEq E] {a b : V} : Boundary left right a b → E → ℕ
  | .nil _, _ => 0
  | .forward e p, f => p.count f + if f = e then 1 else 0
  | .backward e p, f => p.count f + if f = e then 1 else 0

/-- Telescoping of the actual alternating boundary row. -/
theorem row_spec [Fintype E] [DecidableEq E] {a b : V}
    (p : Boundary left right a b) :
    2 * (∑ e, p.row e) = 1 - (-1 : ℤ) ^ p.length ∧
      ∀ x : V → ℚ,
        (∑ e, (p.row e : ℚ) * (x (left e) + x (right e))) =
          x a - (-1 : ℚ) ^ p.length * x b := by
  induction p with
  | nil => constructor <;> simp [row, length]
  | forward e p ih =>
      obtain ⟨hsum, hrow⟩ := ih
      constructor
      · simp only [row, length, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true, pow_succ]
        linarith
      · intro x
        have hx := hrow x
        simp only [row, length, Int.cast_add, Int.cast_ite, Int.cast_pow,
          Int.cast_neg, Int.cast_one, Int.cast_zero, add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true, pow_succ]
        linarith
  | backward e p ih =>
      obtain ⟨hsum, hrow⟩ := ih
      constructor
      · simp only [row, length, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true, pow_succ]
        linarith
      · intro x
        have hx := hrow x
        simp only [row, length, Int.cast_add, Int.cast_ite, Int.cast_pow,
          Int.cast_neg, Int.cast_one, Int.cast_zero, add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true, pow_succ]
        linarith

/-- Cancellation can only reduce the absolute value of an edge coefficient. -/
theorem natAbs_row_le_count [DecidableEq E] {a b : V}
    (p : Boundary left right a b) (f : E) : (p.row f).natAbs ≤ p.count f := by
  induction p with
  | nil => simp [row, count]
  | forward e p ih =>
      by_cases h : f = e
      · simp only [row, count, ite_eq_left h]
        calc
          (p.row f + (-1 : ℤ) ^ p.length).natAbs ≤
              (p.row f).natAbs + ((-1 : ℤ) ^ p.length).natAbs := Int.natAbs_add_le _ _
          _ ≤ p.count f + 1 := by simpa using Nat.add_le_add_right ih 1
      · simpa [row, count, h] using ih
  | backward e p ih =>
      by_cases h : f = e
      · simp only [row, count, ite_eq_left h]
        calc
          (p.row f + (-1 : ℤ) ^ p.length).natAbs ≤
              (p.row f).natAbs + ((-1 : ℤ) ^ p.length).natAbs := Int.natAbs_add_le _ _
          _ ≤ p.count f + 1 := by simpa using Nat.add_le_add_right ih 1
      · simpa [row, count, h] using ih

/-- A closed even walk has alternating row sum zero. -/
theorem row_sum_zero [Fintype E] [DecidableEq E] {a : V}
    (p : Boundary left right a a) (hp : Even p.length) : ∑ e, p.row e = 0 := by
  have h := (row_spec p).1
  rw [hp.neg_one_pow] at h
  linarith

/-- The alternating row of a closed even walk annihilates every unsigned
edge-sum vector. -/
theorem row_annihilates [Fintype E] [DecidableEq E] {a : V}
    (p : Boundary left right a a) (hp : Even p.length) (x : V → ℚ) :
    (∑ e, (p.row e : ℚ) * (x (left e) + x (right e))) = 0 := by
  have h := (row_spec p).2 x
  simpa [hp.neg_one_pow] using h

end Boundary

/-- One facial boundary, with all repeated edge occurrences preserved. -/
structure Face (left right : E → V) where
  root : V
  boundary : Boundary left right root root

variable {F : Type w} {left right : E → V}

/-- The faces whose actual boundary lengths are even. -/
abbrev EvenFaces (faces : F → Face left right) := { f // Even (faces f).boundary.length }

/-- Integer even-face matrix. -/
def integerMatrix [DecidableEq E] (faces : F → Face left right) :
    Matrix (EvenFaces faces) E ℤ := fun f e => (faces f.val).boundary.row e

/-- Rational even-face matrix, for ordinary exact linear algebra. -/
def matrix [DecidableEq E] (faces : F → Face left right) :
    Matrix (EvenFaces faces) E ℚ := fun f e => (integerMatrix faces f e : ℚ)

/-- The `B*1 = 0` identity follows from actual even boundary lengths. -/
theorem matrix_mulVec_one [Fintype E] [DecidableEq E]
    (faces : F → Face left right) : matrix faces *ᵥ (1 : E → ℚ) = 0 := by
  funext f
  have h := Boundary.row_sum_zero (faces f.val).boundary f.property
  have hq : (∑ e, ((faces f.val).boundary.row e : ℚ)) = 0 := by exact_mod_cast h
  simpa [matrix, integerMatrix, Matrix.mulVec, dotProduct] using hq

/-- The genuine alternating even-face matrix satisfies `B*A = 0`. -/
theorem matrix_mul_unsigned [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (faces : F → Face left right) :
    matrix faces * Incidence.unsigned left right = 0 := by
  ext f v
  have h := Boundary.row_annihilates (faces f.val).boundary f.property (Pi.single v 1)
  simpa [matrix, integerMatrix, Matrix.mul_apply, Incidence.unsigned,
    Pi.single_apply, eq_comm] using h

/-- Every ordinary row combination of genuine even-face equations belongs
in the left kernel of the unsigned incidence matrix. -/
theorem row_span_le_left_kernel [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (faces : F → Face left right) :
    Submodule.span ℚ (Set.range (matrix faces)) ≤
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin := by
  apply Submodule.span_le.mpr
  rintro g ⟨f, rfl⟩
  change (Incidence.unsigned left right)ᵀ *ᵥ matrix faces f = 0
  ext v
  have h := congrFun (congrFun (matrix_mul_unsigned faces) f) v
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h

/-- Each original edge has exactly two occurrences among all facial
boundaries. This counts sides, including repeated incidences with one face. -/
def TwoSides [Fintype F] [DecidableEq E] (faces : F → Face left right) : Prop :=
  ∀ e, ∑ f, (faces f).boundary.count e = 2

/-- The absolute column sum of the actual even-face integer matrix is at
most two, by the two-side occurrence count. -/
theorem column_natAbs_sum_le_two [Fintype F] [DecidableEq E]
    (faces : F → Face left right) (hsides : TwoSides faces) (e : E) :
    ∑ f : EvenFaces faces, (integerMatrix faces f e).natAbs ≤ 2 := by
  classical
  calc
    (∑ f : EvenFaces faces, (integerMatrix faces f e).natAbs) ≤
        ∑ f : EvenFaces faces, (faces f.val).boundary.count e := by
      apply Finset.sum_le_sum
      intro f _
      exact Boundary.natAbs_row_le_count (faces f.val).boundary e
    _ ≤ ∑ f : F, (faces f).boundary.count e := by
      have h := Fintype.sum_subtype_add_sum_subtype
        (fun f => Even (faces f).boundary.length) (fun f => (faces f).boundary.count e)
      change (∑ f : { f // Even (faces f).boundary.length },
        (faces f.val).boundary.count e) ≤ _
      omega
    _ = 2 := hsides e

end WeightedMIS.Faces
