module

public import WeightedMIS.Faces
public import WeightedMIS.FaceRank
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Facial occurrences and two-sided edge gluing

The occurrences here are positions in actual closed endpoint walks, rather
than a matrix sparsity certificate. Pairing those positions with the two sides
of each edge constructs the signed face-dual matrix from the same boundaries.
The pairing allows either direction of traversal on either side, so it does
not impose orientability. Vertex-link conditions and connectivity are separate
combinatorial surface conditions.
-/

@[expose] public section

namespace WeightedMIS.Faces.Boundary

variable {V E : Type*} {left right : E → V}

/-- The original edge traversed at a specified boundary occurrence. -/
def edgeAt {a b : V} : (p : Boundary left right a b) → Fin p.length → E
  | .nil _, i => Fin.elim0 i
  | .forward e p, i => Fin.lastCases e p.edgeAt i
  | .backward e p, i => Fin.lastCases e p.edgeAt i

/-- Whether this occurrence traverses its edge from left to right. -/
def forwardAt {a b : V} : (p : Boundary left right a b) → Fin p.length → Bool
  | .nil _, i => Fin.elim0 i
  | .forward _ p, i => Fin.lastCases true p.forwardAt i
  | .backward _ p, i => Fin.lastCases false p.forwardAt i

/-- The alternating row is the sum of its genuine occurrence contributions. -/
theorem row_eq_sum_occurrences [DecidableEq E] {a b : V}
    (p : Boundary left right a b) (e : E) :
    p.row e = ∑ i : Fin p.length, if p.edgeAt i = e then (-1 : ℤ) ^ i.val else 0 := by
  induction p with
  | nil =>
      change 0 = ∑ i : Fin 0, _
      simp
  | forward f p ih =>
      change p.row e + (if e = f then (-1 : ℤ) ^ p.length else 0) =
        ∑ i : Fin (p.length + 1), if Fin.lastCases f p.edgeAt i = e then (-1 : ℤ) ^ i.val else 0
      rw [Fin.sum_univ_castSucc]
      simpa only [Fin.lastCases_castSucc, Fin.lastCases_last,
        Fin.val_castSucc, Fin.val_last, eq_comm] using
        congrArg (fun z => z + if e = f then (-1 : ℤ) ^ p.length else 0) ih
  | backward f p ih =>
      change p.row e + (if e = f then (-1 : ℤ) ^ p.length else 0) =
        ∑ i : Fin (p.length + 1), if Fin.lastCases f p.edgeAt i = e then (-1 : ℤ) ^ i.val else 0
      rw [Fin.sum_univ_castSucc]
      simpa only [Fin.lastCases_castSucc, Fin.lastCases_last,
        Fin.val_castSucc, Fin.val_last, eq_comm] using
        congrArg (fun z => z + if e = f then (-1 : ℤ) ^ p.length else 0) ih

/-- Occurrence counting agrees with the recursive boundary count. -/
theorem count_eq_sum_occurrences [DecidableEq E] {a b : V}
    (p : Boundary left right a b) (e : E) :
    p.count e = ∑ i : Fin p.length, if p.edgeAt i = e then 1 else 0 := by
  induction p with
  | nil =>
      change 0 = ∑ i : Fin 0, _
      simp
  | forward f p ih =>
      change p.count e + (if e = f then 1 else 0) =
        ∑ i : Fin (p.length + 1), if Fin.lastCases f p.edgeAt i = e then 1 else 0
      rw [Fin.sum_univ_castSucc]
      simpa only [Fin.lastCases_castSucc, Fin.lastCases_last, eq_comm] using
        congrArg (fun z => z + if e = f then 1 else 0) ih
  | backward f p ih =>
      change p.count e + (if e = f then 1 else 0) =
        ∑ i : Fin (p.length + 1), if Fin.lastCases f p.edgeAt i = e then 1 else 0
      rw [Fin.sum_univ_castSucc]
      simpa only [Fin.lastCases_castSucc, Fin.lastCases_last, eq_comm] using
        congrArg (fun z => z + if e = f then 1 else 0) ih

end WeightedMIS.Faces.Boundary

namespace WeightedMIS.EmbeddingFaces

open Matrix Finset

universe u v w
variable {V : Type u} {E : Type v} {F : Type w} {left right : E → V}

/-- A position in one of the actual facial boundary walks. -/
abbrev Occurrence (faces : F → Faces.Face left right) :=
  (f : F) × Fin (faces f).boundary.length

/-- Pair every actual occurrence with exactly one of the two original edge
sides. The equality checks the traversed edge, not merely cardinalities. -/
structure SidePairing (faces : F → Faces.Face left right) where
  pairing : Occurrence faces ≃ E × Bool
  edge_eq : ∀ d, (faces d.1).boundary.edgeAt d.2 = (pairing d).1

namespace SidePairing

variable {faces : F → Faces.Face left right} (P : SidePairing faces)

/-- The occurrence representing a specified edge side. -/
def side (e : E) (b : Bool) : Occurrence faces := P.pairing.symm (e, b)

@[simp] theorem side_edge (e : E) (b : Bool) :
    (faces (P.side e b).1).boundary.edgeAt (P.side e b).2 = e := by
  simpa [side] using P.edge_eq (P.pairing.symm (e, b))

/-- The incident face of this side. -/
def face (e : E) (b : Bool) : F := (P.side e b).1

/-- Alternating integer sign of the actual side occurrence. -/
def sign (e : E) (b : Bool) : ℚ := (-1 : ℚ) ^ (P.side e b).2.val

/-- The direction used by the actual facial walk on this side. -/
def forward (e : E) (b : Bool) : Bool :=
  (faces (P.side e b).1).boundary.forwardAt (P.side e b).2

/-- Every occurrence contributes one of the two ordinary signs. -/
theorem signs (b : Bool) : FaceRank.Signs (fun e => P.sign e b) := by
  intro e
  exact neg_one_pow_eq_or ℚ _

include P in
/-- Pairing actual occurrences with edge sides proves the two-sides count. -/
theorem twoSides [Fintype F] [Fintype E] [DecidableEq E] : Faces.TwoSides faces := by
  intro e
  simp only [Faces.Boundary.count_eq_sum_occurrences]
  rw [← Fintype.sum_sigma (fun d : Occurrence faces =>
    if (faces d.1).boundary.edgeAt d.2 = e then (1 : ℕ) else 0)]
  calc
    (∑ d : Occurrence faces, if (faces d.1).boundary.edgeAt d.2 = e then 1 else 0) =
        ∑ s : E × Bool, if s.1 = e then 1 else 0 := by
      simpa only [P.edge_eq] using
        P.pairing.sum_comp (fun s : E × Bool => if s.1 = e then (1 : ℕ) else 0)
    _ = 2 := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool]
      rw [Finset.sum_add_distrib]
      simp

/-- The row of any face is precisely the sum of the signed contributions of
its two specified edge sides, including repeated incidence with one face. -/
theorem row_eq_signed [Fintype F] [Fintype E] [DecidableEq E] [DecidableEq F]
    (f : F) (e : E) :
    ((faces f).boundary.row e : ℚ) =
      FaceRank.signed (fun e => P.face e false) (fun e => P.face e true)
        (fun e => P.sign e false) (fun e => P.sign e true) f e := by
  have hsum : (∑ d : Occurrence faces,
      if d.1 = f then
        (if (faces d.1).boundary.edgeAt d.2 = e then (-1 : ℚ) ^ d.2.val else 0)
      else 0) = ((faces f).boundary.row e : ℚ) := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    exact_mod_cast (Faces.Boundary.row_eq_sum_occurrences (faces f).boundary e).symm
  rw [← hsum]
  have heq := P.pairing.symm.sum_comp (fun d : Occurrence faces =>
    if d.1 = f then
      (if (faces d.1).boundary.edgeAt d.2 = e then (-1 : ℚ) ^ d.2.val else 0)
    else 0)
  rw [← heq]
  change (∑ s : E × Bool,
    if (P.side s.1 s.2).1 = f then
      (if (faces (P.side s.1 s.2).1).boundary.edgeAt (P.side s.1 s.2).2 = e
        then P.sign s.1 s.2 else 0) else 0) = _
  simp only [P.side_edge]
  rw [Fintype.sum_prod_type]
  simp_rw [← ite_and, and_comm, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Fintype.sum_bool]
  simp only [FaceRank.signed, face, eq_comm, sign, add_comm]
  rfl

/-- The genuine even-face matrix is the restriction of the signed side matrix
constructed from the same indexed boundary occurrences. -/
theorem matrix_eq_restricted [Fintype F] [Fintype E] [DecidableEq E] [DecidableEq F] :
    Faces.matrix faces =
      FaceRank.restricted (fun e => P.face e false) (fun e => P.face e true)
        (fun e => P.sign e false) (fun e => P.sign e true)
        (fun f => Even (faces f).boundary.length) := by
  ext f e
  exact P.row_eq_signed f.val e

/-- A connected side dual and an actual odd facial boundary imply independence
of all genuine even-face rows. -/
theorem even_matrix_rank [Fintype F] [Fintype E] [DecidableEq E] [DecidableEq F]
    (hdual : Incidence.Connected (fun e => P.face e false) (fun e => P.face e true))
    (f : F) (hf : ¬ Even (faces f).boundary.length) :
    (Faces.matrix faces).rank = Fintype.card (Faces.EvenFaces faces) := by
  rw [P.matrix_eq_restricted]
  exact FaceRank.restricted_rank_eq_card _ _ _ _ (P.signs false) (P.signs true)
    hdual _ f hf

/-- Without omitting a face, connected signed-dual propagation still gives
the general rank lower bound. -/
theorem all_even_matrix_rank [Fintype F] [Fintype E] [DecidableEq E] [DecidableEq F]
    (hdual : Incidence.Connected (fun e => P.face e false) (fun e => P.face e true))
    (heven : ∀ f, Even (faces f).boundary.length) :
    Fintype.card F - 1 ≤ (Faces.matrix faces).rank := by
  let ef : Faces.EvenFaces faces ≃ F :=
    { toFun := Subtype.val
      invFun := fun f => ⟨f, heven f⟩
      left_inv := fun f => rfl
      right_inv := fun f => rfl }
  have heq : Faces.matrix faces =
      (FaceRank.signed (fun e => P.face e false) (fun e => P.face e true)
        (fun e => P.sign e false) (fun e => P.sign e true)).submatrix ef (Equiv.refl E) := by
    ext f e
    exact P.row_eq_signed f.val e
  rw [heq, Matrix.rank_submatrix]
  exact FaceRank.signed_rank_ge_card_sub_one _ _ _ _ (P.signs false) (P.signs true) hdual

end SidePairing

end WeightedMIS.EmbeddingFaces
