module

public import WeightedMIS.ShortestPath
public import Mathlib.Tactic

/-!
# Integral capacitated flows and residual augmentations

Flows are skew-symmetric integer matrices. Directed capacities are natural
numbers, and conservation holds away from the two terminals. This convention
allows reverse residual arcs without doubling the edge-label type.
-/

@[expose] public section

namespace WeightedMIS.MaxFlowCore

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Divergence of a skew-symmetric flow at a vertex. -/
def divergence (f : V → V → ℤ) (u : V) : ℤ := ∑ v, f u v

/-- The source value. -/
def value (f : V → V → ℤ) (s : V) : ℤ := divergence f s

/-- A feasible integral flow with directed natural capacities. -/
def Feasible (c : V → V → ℕ) (s t : V) (f : V → V → ℤ) : Prop :=
  (∀ u v, f u v = -f v u) ∧
  (∀ u v, f u v ≤ (c u v : ℤ)) ∧
  (∀ u, u ≠ s → u ≠ t → divergence f u = 0)

/-- Exact residual capacity, nonnegative for feasible flows. -/
def residual (c : V → V → ℕ) (f : V → V → ℤ) (u v : V) : ℤ :=
  (c u v : ℤ) - f u v

/-- The net signed multiplicity of an ordered pair along a path. -/
def pathFlow (p : List (V × V)) (u v : V) : ℤ :=
  (p.count (u, v) : ℤ) - (p.count (v, u) : ℤ)

/-- Add an integral amount along every path arc and subtract it in reverse. -/
def augment (f : V → V → ℤ) (p : List (V × V)) (d : ℕ) (u v : V) : ℤ :=
  f u v + (d : ℤ) * pathFlow p u v

theorem zero_feasible (c : V → V → ℕ) (s t : V) : Feasible c s t (fun _ _ => 0) := by
  refine ⟨by simp, ?_, by simp [divergence]⟩
  intro u v
  exact Nat.cast_nonneg _

theorem residual_nonnegative (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (u v : V) : 0 ≤ residual c f u v := by
  unfold residual
  exact sub_nonneg.mpr (hf.2.1 u v)

@[simp] theorem pathFlow_nil (u v : V) : pathFlow [] u v = 0 := by
  simp [pathFlow]

theorem pathFlow_cons (a : V × V) (p : List (V × V)) (u v : V) :
    pathFlow (a :: p) u v = pathFlow p u v +
      (if (u, v) = a then 1 else 0) - (if (v, u) = a then 1 else 0) := by
  have hc (x : V × V) : ((a :: p).count x : ℤ) = (p.count x : ℤ) +
      (if x = a then 1 else 0) := by
    by_cases hx : x = a
    · subst x
      simp
    · simp only [List.count_cons_of_ne (Ne.symm hx), ite_eq_right hx, add_zero]
  simp only [pathFlow, hc]
  ring

theorem pathFlow_skew (p : List (V × V)) (u v : V) :
    pathFlow p u v = -pathFlow p v u := by
  simp only [pathFlow]
  ring

/-- A path's signed incidence telescopes to its endpoints. -/
theorem pathFlow_divergence {s t : V} (p : List (V × V))
    (hp : ShortestPath.IsWalk Prod.fst Prod.snd s t p) (u : V) :
    (∑ v, pathFlow p u v) = (if u = s then 1 else 0) - (if u = t then 1 else 0) := by
  induction p generalizing s with
  | nil =>
      have hs : s = t := hp
      simp [hs]
  | cons a p ih =>
      have ha : a.1 = s := hp.1
      simp_rw [pathFlow_cons]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ih hp.2]
      have hf : (∑ v, if (u, v) = a then (1 : ℤ) else 0) =
          if u = a.1 then 1 else 0 := by
        rcases a with ⟨x, y⟩
        by_cases hu : u = x <;> simp [Prod.mk.injEq, hu]
      have hr : (∑ v, if (v, u) = a then (1 : ℤ) else 0) =
          if u = a.2 then 1 else 0 := by
        rcases a with ⟨x, y⟩
        by_cases hu : u = y <;> simp [Prod.mk.injEq, hu]
      rw [hf, hr, ha]
      ring

/-- Simplicity of the visited vertices implies no repeated ordered arc. -/
theorem simple_nodup {s : V} {p : List (V × V)}
    (hp : ShortestPath.IsSimple Prod.snd s p) : p.Nodup := by
  have hmap : (p.map Prod.snd).Nodup := (List.nodup_cons.mp hp).2
  exact List.Nodup.of_map Prod.snd hmap

/-- Augmentation preserves feasibility when every path arc has enough residual
capacity. The path has no repeated arc. -/
theorem augment_feasible (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (p : List (V × V))
    (hp : ShortestPath.IsWalk Prod.fst Prod.snd s t p) (hn : p.Nodup)
    (d : ℕ) (hd : ∀ a ∈ p, (d : ℤ) ≤ residual c f a.1 a.2) :
    Feasible c s t (augment f p d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    unfold augment
    rw [hf.1 u v, pathFlow_skew p u v]
    ring
  · intro u v
    have hcount : (p.count (u, v) : ℤ) ≤ 1 := by
      exact_mod_cast (List.nodup_iff_count_le_one.mp hn (u, v))
    have hrev : (0 : ℤ) ≤ p.count (v, u) := Nat.cast_nonneg _
    have hd0 : (0 : ℤ) ≤ d := Nat.cast_nonneg _
    by_cases hm : (u, v) ∈ p
    · have hres := hd (u, v) hm
      unfold augment pathFlow residual at *
      nlinarith
    · have hz : p.count (u, v) = 0 := List.count_eq_zero.mpr hm
      have hb := hf.2.1 u v
      unfold augment pathFlow
      rw [hz, Nat.cast_zero]
      nlinarith
  · intro u hus hut
    unfold divergence augment
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, pathFlow_divergence p hp]
    change divergence f u + (d : ℤ) * _ = 0
    rw [hf.2.2 u hus hut]
    simp [hus, hut]

/-- Every augmentation raises the source value by its exact amount. -/
theorem augment_value (f : V → V → ℤ) {s t : V} (hst : s ≠ t)
    (p : List (V × V)) (hp : ShortestPath.IsWalk Prod.fst Prod.snd s t p) (d : ℕ) :
    value (augment f p d) s = value f s + (d : ℤ) := by
  unfold value divergence augment
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, pathFlow_divergence p hp]
  simp [hst]

/-- Net flow across the source side of a cut. -/
def boundary (f : V → V → ℤ) (S : Finset V) : ℤ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, f u v

/-- Capacity of a cut in the directed matrix representation. -/
def cutCapacity (c : V → V → ℕ) (S : Finset V) : ℤ :=
  boundary (fun u v => (c u v : ℤ)) S

/-- All internal flow cancels by skew symmetry, including loops. -/
theorem internal_sum_zero (f : V → V → ℤ) (hskew : ∀ u v, f u v = -f v u)
    (S : Finset V) : (∑ u ∈ S, ∑ v ∈ S, f u v) = 0 := by
  have hh : (∑ u ∈ S, ∑ v ∈ S, f u v) = -(∑ u ∈ S, ∑ v ∈ S, f u v) := by
    calc
      _ = ∑ v ∈ S, ∑ u ∈ S, f u v := Finset.sum_comm
      _ = ∑ v ∈ S, ∑ u ∈ S, -f v u := by
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro u _
        exact hskew u v
      _ = -(∑ v ∈ S, ∑ u ∈ S, f v u) := by
        simp only [Finset.sum_neg_distrib]
  omega

/-- Conservation identifies the boundary flow with the source value. -/
theorem boundary_eq_value (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    boundary f S = value f s := by
  have hsum : (∑ u ∈ S, divergence f u) = value f s := by
    rw [Finset.sum_eq_single s]
    · rfl
    · intro u hu hus
      exact hf.2.2 u hus (fun hut => ht (hut ▸ hu))
    · exact fun hn => False.elim (hn hs)
  have hsplit : (∑ u ∈ S, divergence f u) =
      (∑ u ∈ S, ∑ v ∈ S, f u v) + boundary f S := by
    unfold boundary
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    exact (Finset.sum_add_sum_compl S (f u)).symm
  rw [internal_sum_zero f hf.1, zero_add] at hsplit
  exact hsplit.symm.trans hsum

/-- The ordinary weak max-flow/min-cut inequality. -/
theorem value_le_cut (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    value f s ≤ cutCapacity c S := by
  rw [← boundary_eq_value c s t f hf S hs ht]
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact hf.2.1 u v

/-- The exact duality gap is the sum of crossing residual capacities. -/
theorem cut_gap (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    cutCapacity c S - value f s = boundary (residual c f) S := by
  rw [← boundary_eq_value c s t f hf S hs ht]
  simp only [cutCapacity, boundary, residual, Finset.sum_sub_distrib]

/-- A cut with no positive residual crossing is a genuine minimum cut. -/
theorem minimum_cut_of_residual_zero (c : V → V → ℕ) (s t : V)
    (f : V → V → ℤ) (hf : Feasible c s t f) (S : Finset V)
    (hs : s ∈ S) (ht : t ∉ S)
    (hres : ∀ u ∈ S, ∀ v ∈ Sᶜ, residual c f u v = 0) :
    value f s = cutCapacity c S ∧
      ∀ T : Finset V, s ∈ T → t ∉ T → cutCapacity c S ≤ cutCapacity c T := by
  have hgap := cut_gap c s t f hf S hs ht
  have hz : boundary (residual c f) S = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    exact Finset.sum_eq_zero fun v hv => hres u hu v hv
  rw [hz] at hgap
  have heq : value f s = cutCapacity c S := by omega
  refine ⟨heq, ?_⟩
  intro T hsT htT
  rw [← heq]
  exact value_le_cut c s t f hf T hsT htT

/-- A residual-threshold cut gives the quantitative gap bound used by capacity
scaling. The bound is polynomial in the number of vertices. -/
theorem gap_le_card_sq (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (S : Finset V) (hs : s ∈ S) (ht : t ∉ S)
    (d : ℕ) (hd : ∀ u ∈ S, ∀ v ∈ Sᶜ, residual c f u v ≤ (d : ℤ)) :
    cutCapacity c S - value f s ≤ (Fintype.card V : ℤ) ^ 2 * (d : ℤ) := by
  rw [cut_gap c s t f hf S hs ht]
  have hh : boundary (residual c f) S ≤ (S.card : ℤ) * (Sᶜ.card : ℤ) * (d : ℤ) := by
    calc
      _ ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, (d : ℤ) := by
        exact Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => hd u hu v hv
      _ = _ := by simp [mul_assoc]
  have hSc : (S.card : ℤ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ S
  have hTc : (Sᶜ.card : ℤ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ Sᶜ
  have hprod : (S.card : ℤ) * (Sᶜ.card : ℤ) ≤ (Fintype.card V : ℤ)^2 := by
    nlinarith [show (0 : ℤ) ≤ S.card from Nat.cast_nonneg _,
      show (0 : ℤ) ≤ Sᶜ.card from Nat.cast_nonneg _]
  exact hh.trans (mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg d))

end WeightedMIS.MaxFlowCore
