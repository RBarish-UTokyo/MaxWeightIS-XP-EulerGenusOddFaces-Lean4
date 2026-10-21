module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic

/-!
# Unsigned incidence and connected nonbipartite graphs

A graph is represented by two endpoints for each edge, so parallel edges are
retained. The unsigned incidence matrix counts both endpoints, including both
occurrences of a loop. Walks below record genuine traversals of these edges.
We prove the full-column-rank claim of Lemma 6, both from an odd closed walk
and directly from nonexistence of a two-coloring.
-/

@[expose] public section

namespace WeightedMIS.Incidence

open Matrix

variable {V E : Type*}

/-- An edge walk with its number of traversed edges. -/
inductive Walk (left right : E → V) : V → V → ℕ → Prop where
  | nil (v : V) : Walk left right v v 0
  | forward {a b : V} {n : ℕ} (e : E) (h : b = left e) :
      Walk left right a b n → Walk left right a (right e) (n + 1)
  | backward {a b : V} {n : ℕ} (e : E) (h : b = right e) :
      Walk left right a b n → Walk left right a (left e) (n + 1)

/-- Connectivity means that every two vertices are joined by a finite walk. -/
def Connected (left right : E → V) : Prop :=
  ∀ a b, ∃ n, Walk left right a b n

/-- Bipartiteness as a two-coloring of all endpoints. -/
def Bipartite (left right : E → V) : Prop :=
  ∃ color : V → Bool, ∀ e, color (left e) ≠ color (right e)

/-- A closed edge walk of odd length. -/
def HasOddClosedWalk (left right : E → V) : Prop :=
  ∃ a n, Odd n ∧ Walk left right a a n

/-- Values in the kernel alternate in sign at every step of an edge walk. -/
theorem kernel_along_walk (left right : E → V) (x : V → ℚ)
    (hx : ∀ e, x (left e) + x (right e) = 0)
    {a b : V} {n : ℕ} (p : Walk left right a b n) :
    x b = (-1 : ℚ) ^ n * x a := by
  induction p with
  | nil => simp
  | @forward b n e hb p ih =>
      subst b
      have he := hx e
      rw [pow_succ]
      linarith
  | @backward b n e hb p ih =>
      subst b
      have he := hx e
      rw [pow_succ]
      linarith

/-- An odd closed walk forces a kernel value to be zero; connectivity
propagates that zero to all vertices. -/
theorem kernel_eq_zero_of_odd_closed_walk
    (left right : E → V) (hconn : Connected left right)
    (hodd : HasOddClosedWalk left right)
    (x : V → ℚ) (hx : ∀ e, x (left e) + x (right e) = 0) : x = 0 := by
  obtain ⟨a, n, hn, p⟩ := hodd
  have ha := kernel_along_walk left right x hx p
  rw [hn.neg_one_pow] at ha
  have hzero : x a = 0 := by linarith
  funext b
  obtain ⟨k, q⟩ := hconn a b
  have hb := kernel_along_walk left right x hx q
  simpa [hzero] using hb

/-- A nonzero kernel vector on a connected graph would give a two-coloring
by signs. Therefore connected nonbipartite graphs have trivial kernel. -/
theorem kernel_eq_zero_of_nonbipartite
    (left right : E → V) (hconn : Connected left right)
    (hnot : ¬ Bipartite left right)
    (x : V → ℚ) (hx : ∀ e, x (left e) + x (right e) = 0) : x = 0 := by
  classical
  by_contra hzero
  have hex : ∃ a, x a ≠ 0 := by
    by_contra h
    push Not at h
    exact hzero (funext h)
  obtain ⟨a, ha⟩ := hex
  have hnonzero (b : V) : x b ≠ 0 := by
    obtain ⟨n, p⟩ := hconn a b
    rw [kernel_along_walk left right x hx p]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) ha
  apply hnot
  refine ⟨fun v => decide (0 < x v), ?_⟩
  intro e
  have he := hx e
  have hlne := hnonzero (left e)
  by_cases hl : 0 < x (left e)
  · have hr : ¬ 0 < x (right e) := by linarith
    simp [hl, hr]
  · have hr : 0 < x (right e) := by
      have hlt : x (left e) < 0 := lt_of_le_of_ne (le_of_not_gt hl) hlne
      linarith
    simp [hl, hr]

/-- The actual unsigned edge-by-vertex incidence matrix. -/
def unsigned [DecidableEq V] (left right : E → V) : Matrix E V ℚ :=
  fun e v => (if v = left e then 1 else 0) + (if v = right e then 1 else 0)

@[simp] theorem unsigned_mulVec [Fintype V] [DecidableEq V]
    (left right : E → V) (x : V → ℚ) (e : E) :
    (unsigned left right *ᵥ x) e = x (left e) + x (right e) := by
  simp [unsigned, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]

/-- Every row has total incidence two, as used in the slack equations. -/
theorem unsigned_mulVec_one [Fintype V] [DecidableEq V]
    (left right : E → V) :
    unsigned left right *ᵥ (1 : V → ℚ) = (2 : ℚ) • (1 : E → ℚ) := by
  funext e
  norm_num

/-- Triviality of the matrix kernel for a connected nonbipartite graph. -/
theorem unsigned_ker_eq_bot [Fintype V] [DecidableEq V]
    (left right : E → V) (hconn : Connected left right)
    (hnot : ¬ Bipartite left right) :
    LinearMap.ker (unsigned left right).mulVecLin = ⊥ := by
  rw [Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  apply kernel_eq_zero_of_nonbipartite left right hconn hnot x
  intro e
  simpa using congrFun hx e

/-- The first rank conclusion of manuscript Lemma 6 for an actual connected
nonbipartite endpoint graph, without assuming a rank fact as a premise. -/
theorem unsigned_rank_eq_card [Fintype V] [DecidableEq V]
    (left right : E → V) (hconn : Connected left right)
    (hnot : ¬ Bipartite left right) :
    (unsigned left right).rank = Fintype.card V := by
  rw [Matrix.rank, LinearMap.finrank_range_of_inj]
  · exact Module.finrank_pi ℚ
  · exact LinearMap.ker_eq_bot.mp (unsigned_ker_eq_bot left right hconn hnot)

/-- The same full-rank conclusion using the odd-walk hypothesis employed
in the manuscript's proof. -/
theorem unsigned_rank_eq_card_of_odd_closed_walk [Fintype V] [DecidableEq V]
    (left right : E → V) (hconn : Connected left right)
    (hodd : HasOddClosedWalk left right) :
    (unsigned left right).rank = Fintype.card V := by
  have hker : LinearMap.ker (unsigned left right).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_eq_bot_iff]
    intro x hx
    apply kernel_eq_zero_of_odd_closed_walk left right hconn hodd x
    intro e
    simpa using congrFun hx e
  rw [Matrix.rank, LinearMap.finrank_range_of_inj]
  · exact Module.finrank_pi ℚ
  · exact LinearMap.ker_eq_bot.mp hker

/-- Rank-nullity gives the left-kernel dimension used before the face-row
rank subtraction in manuscript Lemma 6. -/
theorem left_kernel_finrank [Fintype V] [Fintype E] [DecidableEq V]
    (left right : E → V) (hconn : Connected left right)
    (hnot : ¬ Bipartite left right) :
    Module.finrank ℚ (LinearMap.ker (unsigned left right)ᵀ.mulVecLin) =
      Fintype.card E - Fintype.card V := by
  have h := LinearMap.finrank_range_add_finrank_ker (unsigned left right)ᵀ.mulVecLin
  change (unsigned left right)ᵀ.rank +
    Module.finrank ℚ (LinearMap.ker (unsigned left right)ᵀ.mulVecLin) =
      Module.finrank ℚ (E → ℚ) at h
  rw [Matrix.rank_transpose, unsigned_rank_eq_card left right hconn hnot,
    Module.finrank_pi] at h
  omega

end WeightedMIS.Incidence
