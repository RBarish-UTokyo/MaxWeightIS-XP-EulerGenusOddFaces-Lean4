module

public import WeightedMIS.Orientable
public import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# Euler's inequality from the actual polygon incidence maps

The directed vertex-edge and face-edge boundary matrices form a chain complex:
every actual closed face boundary telescopes. Their ranks are at least `n-1`
and `f-1` by primal and dual connectedness. The rank-nullity inequality proves
`n+f ≤ m+2`, including nonorientable maps, so the combinatorial Euler genus is
nonnegative without assuming an Euler bound as an embedding field.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces

open Matrix Finset

variable {V E F : Type*} {left right : E → V}

namespace SidePairing

variable {faces : F → Faces.Face left right} (P : SidePairing faces)

/-- Regroup arbitrary actual occurrence weights by the two sides of an edge. -/
theorem side_weight_sum [Fintype F] [Fintype E] [DecidableEq E] [DecidableEq F]
    (w : Occurrence faces → ℚ) (f : F) (e : E) :
    (∑ i : Fin (faces f).boundary.length,
      if (faces f).boundary.edgeAt i = e then w ⟨f, i⟩ else 0) =
      (if f = P.face e false then w (P.side e false) else 0) +
      (if f = P.face e true then w (P.side e true) else 0) := by
  have hsum : (∑ d : Occurrence faces, if d.1 = f then
      (if (faces d.1).boundary.edgeAt d.2 = e then w d else 0) else 0) =
      ∑ i : Fin (faces f).boundary.length,
        if (faces f).boundary.edgeAt i = e then w ⟨f, i⟩ else 0 := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  rw [← hsum]
  rw [← P.pairing.symm.sum_comp (fun d : Occurrence faces => if d.1 = f then
    (if (faces d.1).boundary.edgeAt d.2 = e then w d else 0) else 0)]
  change (∑ s : E × Bool, if (P.side s.1 s.2).1 = f then
    (if (faces (P.side s.1 s.2).1).boundary.edgeAt (P.side s.1 s.2).2 = e
      then w (P.side s.1 s.2) else 0) else 0) = _
  simp only [P.side_edge]
  rw [Fintype.sum_prod_type]
  simp_rw [← ite_and, and_comm, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Fintype.sum_bool]
  simp only [face, eq_comm, add_comm]
  rfl

/-- The directed face-edge boundary uses actual traversal directions. -/
def boundaryMatrix [DecidableEq F] : Matrix F E ℚ :=
  FaceRank.signed (fun e => P.face e false) (fun e => P.face e true)
    (fun e => boolSign (P.forward e false)) (fun e => boolSign (P.forward e true))

/-- The side formula agrees with the full signed sum of genuine traversals. -/
theorem boundaryMatrix_apply [Fintype F] [Fintype E] [DecidableEq E] [DecidableEq F]
    (f : F) (e : E) :
    P.boundaryMatrix f e = ∑ i : Fin (faces f).boundary.length,
      if (faces f).boundary.edgeAt i = e then boolSign ((faces f).boundary.forwardAt i)
      else 0 := by
  rw [P.side_weight_sum (fun d => boolSign ((faces d.1).boundary.forwardAt d.2))]
  rfl

include P in
/-- Counting actual side positions gives the exact total facial length. -/
theorem total_face_length [Fintype F] [Fintype E] :
    (∑ f, (faces f).boundary.length) = 2 * Fintype.card E := by
  have h := Fintype.card_congr P.pairing
  simpa only [Fintype.card_sigma, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_bool, mul_comm] using h

include P in
/-- The odd-face count is even because every edge has exactly two sides. -/
theorem odd_face_count_even [Fintype F] [Fintype E] :
    Even (Fintype.card { f // Odd (faces f).boundary.length }) := by
  classical
  have ht : Even (∑ f, (faces f).boundary.length) := by
    rw [P.total_face_length]
    exact even_two_mul _
  have h := (Finset.even_sum_iff_even_card_odd
    (s := Finset.univ) (fun f => (faces f).boundary.length)).mp ht
  simpa only [Fintype.card_subtype] using h

end SidePairing

namespace Directed

/-- Ordinary directed edge-by-vertex incidence, with multiplicities at loops. -/
def matrix [DecidableEq V] (left right : E → V) : Matrix E V ℚ :=
  fun e v => (if v = right e then 1 else 0) - (if v = left e then 1 else 0)

@[simp] theorem mulVec [Fintype V] [DecidableEq V] (left right : E → V)
    (x : V → ℚ) (e : E) : (matrix left right *ᵥ x) e = x (right e) - x (left e) := by
  simp [matrix, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul]

theorem constant_along_walk (x : V → ℚ) (hx : ∀ e, x (right e) - x (left e) = 0)
    {a b : V} {n : ℕ} (p : Incidence.Walk left right a b n) : x a = x b := by
  induction p with
  | nil => rfl
  | @forward b n e hb p ih =>
      subst b
      have he := hx e
      linarith
  | @backward b n e hb p ih =>
      subst b
      have he := hx e
      linarith

/-- Directed-incidence kernel vectors on a connected graph are constant. -/
theorem kernel_finrank_le_one [Fintype V] [DecidableEq V]
    (hc : Incidence.Connected left right) (root : V) :
    Module.finrank ℚ (LinearMap.ker (matrix left right).mulVecLin) ≤ 1 := by
  let K := LinearMap.ker (matrix left right).mulVecLin
  let ev : K →ₗ[ℚ] ℚ := (LinearMap.proj root).comp K.subtype
  have hinj : Function.Injective ev := by
    intro c d hcd
    have hz : (c : V → ℚ) - (d : V → ℚ) ∈ K := K.sub_mem c.property d.property
    have hrow : ∀ e, (c.val - d.val) (right e) - (c.val - d.val) (left e) = 0 := by
      intro e
      have he := congrFun hz e
      simpa using he
    apply Subtype.ext
    funext v
    obtain ⟨n, p⟩ := hc root v
    have hv := constant_along_walk (c.val - d.val) hrow p
    change c.val root = d.val root at hcd
    simp only [Pi.sub_apply] at hv
    linarith
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [K] using hdim

/-- The usual `n-1` directed-incidence rank lower bound. -/
theorem rank_ge_card_sub_one [Fintype V] [DecidableEq V]
    (hc : Incidence.Connected left right) :
    Fintype.card V - 1 ≤ (matrix left right).rank := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · have : IsEmpty V := hV
    simp
  · let root : V := Classical.choice hV
    have hk := kernel_finrank_le_one hc root
    have hdim := LinearMap.finrank_range_add_finrank_ker (matrix left right).mulVecLin
    change (matrix left right).rank +
      Module.finrank ℚ (LinearMap.ker (matrix left right).mulVecLin) =
        Module.finrank ℚ (V → ℚ) at hdim
    rw [Module.finrank_pi] at hdim
    omega

end Directed
end WeightedMIS.EmbeddingFaces

namespace WeightedMIS.Faces.Boundary

open WeightedMIS.EmbeddingFaces Finset

variable {V E : Type*} {left right : E → V}

/-- Telescoping of directed edge differences along actual indexed occurrences. -/
theorem directed_sum {a b : V} (p : Boundary left right a b) (x : V → ℚ) :
    (∑ i : Fin p.length, boolSign (p.forwardAt i) *
      (x (right (p.edgeAt i)) - x (left (p.edgeAt i)))) = x b - x a := by
  induction p with
  | nil =>
      change (∑ i : Fin 0, _) = x a - x a
      simp
  | forward e p ih =>
      change (∑ i : Fin (p.length + 1),
        boolSign (Fin.lastCases true p.forwardAt i) *
          (x (right (Fin.lastCases e p.edgeAt i)) -
            x (left (Fin.lastCases e p.edgeAt i)))) = _
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, show boolSign true = (1 : ℚ) from rfl, one_mul]
      rw [ih]
      ring
  | backward e p ih =>
      change (∑ i : Fin (p.length + 1),
        boolSign (Fin.lastCases false p.forwardAt i) *
          (x (right (Fin.lastCases e p.edgeAt i)) -
            x (left (Fin.lastCases e p.edgeAt i)))) = _
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last,
        show boolSign false = (-1 : ℚ) from rfl, neg_one_mul]
      rw [ih]
      ring

end WeightedMIS.Faces.Boundary

namespace WeightedMIS.EmbeddingFaces

open Matrix Finset

variable {V E F : Type*} {left right : E → V} {faces : F → Faces.Face left right}

namespace SidePairing

variable (P : SidePairing faces)

/-- A closed actual face boundary annihilates every directed vertex difference. -/
theorem boundaryMatrix_annihilates [Fintype F] [Fintype E] [DecidableEq E] [DecidableEq F]
    (f : F) (x : V → ℚ) :
    (∑ e, P.boundaryMatrix f e * (x (right e) - x (left e))) = 0 := by
  simp only [P.boundaryMatrix_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul]
  have h := (faces f).boundary.directed_sum x
  simpa using h

/-- Boundary of a boundary is zero, for the actual polygon incidence maps. -/
theorem boundaryMatrix_mul_directed [Fintype F] [Fintype E] [Fintype V]
    [DecidableEq E] [DecidableEq F] [DecidableEq V] :
    P.boundaryMatrix * Directed.matrix left right = 0 := by
  ext f v
  have h := P.boundaryMatrix_annihilates f (Pi.single v 1)
  simpa [Matrix.mul_apply, Directed.matrix, Pi.single_apply, eq_comm] using h

end SidePairing

namespace CellularEmbedding

variable (M : CellularEmbedding left right F)

include M in
/-- Euler's inequality follows from the two genuine boundary maps. -/
theorem euler_inequality [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    (hc : Incidence.Connected left right) :
    Fintype.card V + Fintype.card F ≤ Fintype.card E + 2 := by
  have hA := Directed.rank_ge_card_sub_one hc
  have hsign (b : Bool) : FaceRank.Signs (fun e => boolSign (M.sides.forward e b)) := by
    intro e
    change boolSign (M.sides.forward e b) = 1 ∨ boolSign (M.sides.forward e b) = -1
    by_cases h : M.sides.forward e b = true
    · left
      simp [boolSign, h]
    · right
      simp [boolSign, h]
  have hB := FaceRank.signed_rank_ge_card_sub_one
    (fun e => M.sides.face e false) (fun e => M.sides.face e true)
    (fun e => boolSign (M.sides.forward e false))
    (fun e => boolSign (M.sides.forward e true))
    (hsign false) (hsign true) (M.dual_connected hc)
  change Fintype.card F - 1 ≤ M.sides.boundaryMatrix.rank at hB
  have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero (M.sides.boundaryMatrix_mul_directed)
  omega

/-- The nonnegative Euler genus read from the finite cell counts. -/
def eulerGenus [Fintype V] [Fintype E] [Fintype F]
    (_M : CellularEmbedding left right F) : ℕ :=
  Fintype.card E + 2 - (Fintype.card V + Fintype.card F)

/-- No truncation is hidden in the combinatorial Euler-genus definition. -/
theorem eulerGenus_identity [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    (hc : Incidence.Connected left right) :
    M.eulerGenus + Fintype.card V + Fintype.card F = Fintype.card E + 2 := by
  have h := M.euler_inequality hc
  unfold eulerGenus
  omega

end CellularEmbedding
end WeightedMIS.EmbeddingFaces
