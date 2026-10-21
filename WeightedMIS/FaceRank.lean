module

public import WeightedMIS.Incidence
public import Mathlib.Data.Fintype.BigOperators

/-!
# Rank propagation across signed face sides

Each original edge has two specified incident face sides, each with sign `1`
or `-1`. Repeated incidence with the same face is counted twice. A subset of
faces may be retained as matrix rows; coefficients of omitted faces extend by
zero. Connectedness refers to actual walks in the full face-side dual graph.
The construction of these data from a surface embedding is a separate task.
-/

@[expose] public section

namespace WeightedMIS.FaceRank

open Matrix Finset
open WeightedMIS.Incidence

variable {F E : Type*}

/-- A sign attached to every specified face-side occurrence. -/
def Signs (s : E → ℚ) : Prop := ∀ e, s e = 1 ∨ s e = -1

/-- The full face-by-edge matrix counts both incident sides with their signs. -/
def signed [DecidableEq F] (first second : E → F) (s t : E → ℚ) : Matrix F E ℚ :=
  fun f e => (if f = first e then s e else 0) + (if f = second e then t e else 0)

/-- The column equations of a dependence among signed face rows. -/
def Dependence (first second : E → F) (s t : E → ℚ) (c : F → ℚ) : Prop :=
  ∀ e, s e * c (first e) + t e * c (second e) = 0

@[simp] theorem signed_transpose_mulVec [Fintype F] [DecidableEq F]
    (first second : E → F) (s t : E → ℚ) (c : F → ℚ) (e : E) :
    ((signed first second s t)ᵀ *ᵥ c) e =
      s e * c (first e) + t e * c (second e) := by
  simp [signed, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib,
    ite_mul]

/-- Matrix dependence agrees exactly with the two-side column equations. -/
theorem transpose_eq_zero_iff [Fintype F] [DecidableEq F]
    (first second : E → F) (s t : E → ℚ) (c : F → ℚ) :
    (signed first second s t)ᵀ *ᵥ c = 0 ↔ Dependence first second s t c := by
  simp only [funext_iff, signed_transpose_mulVec, Pi.zero_apply, Dependence]

/-- A dependence coefficient propagates along every dual walk up to sign. -/
theorem dependence_along_walk (first second : E → F) (s t : E → ℚ)
    (hs : Signs s) (ht : Signs t) (c : F → ℚ)
    (hc : Dependence first second s t c)
    {a b : F} {n : ℕ} (p : Walk first second a b n) :
    c b = c a ∨ c b = -c a := by
  induction p with
  | nil => exact Or.inl rfl
  | @forward b n e hb p ih =>
      subst b
      have he := hc e
      rcases hs e with h₁ | h₁ <;> rcases ht e with h₂ | h₂ <;>
        rcases ih with hi | hi <;> simp only [h₁, h₂, one_mul, neg_one_mul] at he
      all_goals first | (left; linarith) | (right; linarith)
  | @backward b n e hb p ih =>
      subst b
      have he := hc e
      rcases hs e with h₁ | h₁ <;> rcases ht e with h₂ | h₂ <;>
        rcases ih with hi | hi <;> simp only [h₁, h₂, one_mul, neg_one_mul] at he
      all_goals first | (left; linarith) | (right; linarith)

/-- A zero dependence coefficient at one face forces all coefficients to zero
when the full dual graph is connected. -/
theorem dependence_zero_of_root (first second : E → F) (s t : E → ℚ)
    (hs : Signs s) (ht : Signs t) (hconn : Connected first second)
    (c : F → ℚ) (hc : Dependence first second s t c)
    (root : F) (hroot : c root = 0) : c = 0 := by
  funext f
  obtain ⟨n, p⟩ := hconn root f
  rcases dependence_along_walk first second s t hs ht c hc p with h | h <;>
    simpa [hroot] using h

/-- Evaluation at one face is injective on the full dependence space; hence
that space has dimension at most one. -/
theorem dependence_finrank_le_one [Fintype F] [DecidableEq F]
    (first second : E → F) (s t : E → ℚ)
    (hs : Signs s) (ht : Signs t) (hconn : Connected first second) (root : F) :
    Module.finrank ℚ (LinearMap.ker (signed first second s t)ᵀ.mulVecLin) ≤ 1 := by
  let K := LinearMap.ker (signed first second s t)ᵀ.mulVecLin
  let ev : K →ₗ[ℚ] ℚ := (LinearMap.proj root).comp K.subtype
  have hinj : Function.Injective ev := by
    intro c d hcd
    have hz : (c : F → ℚ) - (d : F → ℚ) ∈ K := K.sub_mem c.property d.property
    have hdep : Dependence first second s t ((c : F → ℚ) - (d : F → ℚ)) :=
      (transpose_eq_zero_iff first second s t _).mp hz
    have hroot : ((c : F → ℚ) - (d : F → ℚ)) root = 0 := by
      change c.val root = d.val root at hcd
      exact sub_eq_zero.mpr hcd
    have hzero := dependence_zero_of_root first second s t hs ht hconn _ hdep root hroot
    exact Subtype.ext (sub_eq_zero.mp hzero)
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [K] using hdim

/-- All rows together have rank at least the number of faces minus one.
This is the all-even rank bound in the signed-dual model. -/
theorem signed_rank_ge_card_sub_one [Fintype F] [Fintype E] [DecidableEq F]
    (first second : E → F) (s t : E → ℚ)
    (hs : Signs s) (ht : Signs t) (hconn : Connected first second) :
    Fintype.card F - 1 ≤ (signed first second s t).rank := by
  classical
  rcases isEmpty_or_nonempty F with hF | hF
  · have : IsEmpty F := hF
    simp
  · let root : F := Classical.choice hF
    have hk := dependence_finrank_le_one first second s t hs ht hconn root
    have hdim := LinearMap.finrank_range_add_finrank_ker (signed first second s t)ᵀ.mulVecLin
    change (signed first second s t)ᵀ.rank +
      Module.finrank ℚ (LinearMap.ker (signed first second s t)ᵀ.mulVecLin) =
        Module.finrank ℚ (F → ℚ) at hdim
    rw [Matrix.rank_transpose, Module.finrank_pi] at hdim
    omega

/-- Keep precisely the selected face rows. -/
def restricted [DecidableEq F] (first second : E → F) (s t : E → ℚ)
    (keep : F → Prop) : Matrix { f // keep f } E ℚ :=
  fun f e => signed first second s t f.val e

/-- Extend dependence coefficients by zero on omitted faces. -/
def extend (keep : F → Prop) [DecidablePred keep] (c : { f // keep f } → ℚ) : F → ℚ :=
  fun f => if h : keep f then c ⟨f, h⟩ else 0

@[simp] theorem extend_kept (keep : F → Prop) [DecidablePred keep]
    (c : { f // keep f } → ℚ) (f : { f // keep f }) : extend keep c f.val = c f := by
  simp [extend, f.property]

@[simp] theorem extend_omitted (keep : F → Prop) [DecidablePred keep]
    (c : { f // keep f } → ℚ) (f : F) (hf : ¬ keep f) : extend keep c f = 0 := by
  simp [extend, hf]

/-- Zero extension preserves exactly the represented linear dependence. -/
theorem transpose_mulVec_extend [Fintype F] [DecidableEq F]
    (first second : E → F) (s t : E → ℚ)
    (keep : F → Prop) [DecidablePred keep] (c : { f // keep f } → ℚ) :
    (signed first second s t)ᵀ *ᵥ extend keep c =
      (restricted first second s t keep)ᵀ *ᵥ c := by
  funext e
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, restricted]
  simp only [extend, mul_dite, mul_zero, Finset.sum_dite,
    Finset.sum_const_zero, add_zero]
  exact (Equiv.subtypeEquivRight <| by simp).sum_comp
    (fun f : { f // keep f } => signed first second s t f.val e * c f)

/-- If at least one face is omitted, the retained rows are independent.
The omitted coefficient is zero and connected dual propagation kills every
coefficient. No face-rank fact is assumed. -/
theorem restricted_kernel_eq_bot [Fintype F] [DecidableEq F]
    (first second : E → F) (s t : E → ℚ)
    (hs : Signs s) (ht : Signs t) (hconn : Connected first second)
    (keep : F → Prop) [DecidablePred keep] (root : F) (hroot : ¬ keep root) :
    LinearMap.ker (restricted first second s t keep)ᵀ.mulVecLin = ⊥ := by
  rw [Matrix.ker_mulVecLin_eq_bot_iff]
  intro c hc
  have hz : (signed first second s t)ᵀ *ᵥ extend keep c = 0 := by
    rw [transpose_mulVec_extend, hc]
  have hdep := (transpose_eq_zero_iff first second s t (extend keep c)).mp hz
  have hext := dependence_zero_of_root first second s t hs ht hconn
    (extend keep c) hdep root (extend_omitted keep c root hroot)
  funext f
  have hf := congrFun hext f.val
  simpa using hf

/-- In the presence of an omitted (odd) face, the retained (even) face matrix
has rank exactly the number of retained rows. -/
theorem restricted_rank_eq_card [Fintype F] [Fintype E] [DecidableEq F]
    (first second : E → F) (s t : E → ℚ)
    (hs : Signs s) (ht : Signs t) (hconn : Connected first second)
    (keep : F → Prop) [DecidablePred keep] (root : F) (hroot : ¬ keep root) :
    (restricted first second s t keep).rank = Fintype.card { f // keep f } := by
  rw [← Matrix.rank_transpose, Matrix.rank, LinearMap.finrank_range_of_inj]
  · exact Module.finrank_pi ℚ
  · exact LinearMap.ker_eq_bot.mp
      (restricted_kernel_eq_bot first second s t hs ht hconn keep root hroot)

/-- Counting the omitted odd faces gives the manuscript's exact `|F|-k`
rank formula whenever that odd-face count is positive. -/
theorem even_face_rank [Fintype F] [Fintype E] [DecidableEq F]
    (first second : E → F) (s t : E → ℚ)
    (hs : Signs s) (ht : Signs t) (hconn : Connected first second)
    (odd : F → Prop) [DecidablePred odd]
    (hodd : 0 < Fintype.card { f // odd f }) :
    (restricted first second s t (fun f => ¬ odd f)).rank =
      Fintype.card F - Fintype.card { f // odd f } := by
  obtain ⟨root⟩ := Fintype.card_pos_iff.mp hodd
  rw [restricted_rank_eq_card first second s t hs ht hconn
    (fun f => ¬ odd f) root.val (not_not.mpr root.property)]
  exact Fintype.card_subtype_compl odd

end WeightedMIS.FaceRank
