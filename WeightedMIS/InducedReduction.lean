module

public import WeightedMIS.Persistence
public import WeightedMIS.EdgeTransport

/-!
# Induced graphs and recovery from the half-valued vertices

Finite sets and rational objectives are transported through the actual subtype
of retained vertices. In particular, preprocessing supplies an ordinary LP
optimum on the residual graph, and its independent sets lift back to the
original vertex type with exactly the same weight.
-/

@[expose] public section

namespace WeightedMIS.InducedReduction

open Persistence
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem weight_eq_sum (w : V → ℚ) (I : Finset V) :
    weight w I = ∑ v ∈ I, w v := by
  simp [weight, objective, indicator]

def lift {keep : V → Prop} (I : Finset {v // keep v}) : Finset V :=
  I.map (Function.Embedding.subtype keep)

def restrict (keep : V → Prop) [DecidablePred keep] (I : Finset V) :
    Finset {v // keep v} := I.subtype keep

@[simp] theorem mem_lift {keep : V → Prop} (I : Finset {v // keep v}) (v : V) :
    v ∈ lift I ↔ ∃ h : keep v, (⟨v, h⟩ : {v // keep v}) ∈ I := by
  simp [lift, Finset.mem_map, Subtype.exists]

@[simp] theorem mem_restrict (keep : V → Prop) [DecidablePred keep]
    (I : Finset V) (v : {v // keep v}) : v ∈ restrict keep I ↔ v.val ∈ I := by
  simp [restrict]

theorem lift_supported {keep : V → Prop} (I : Finset {v // keep v}) :
    ∀ v ∈ lift I, keep v := by
  intro v hv
  exact (mem_lift I v).mp hv |>.choose

theorem lift_restrict_of_supported (keep : V → Prop) [DecidablePred keep]
    (I : Finset V) (hI : ∀ v ∈ I, keep v) : lift (restrict keep I) = I :=
  Finset.subtype_map_of_mem hI

theorem lift_independent (adj : V → V → Prop) {keep : V → Prop}
    (I : Finset {v // keep v})
    (hI : Independent (fun u v : {v // keep v} => adj u.val v.val) I) :
    Independent adj (lift I) := by
  intro u v huv hu hv
  obtain ⟨hku, hu⟩ := (mem_lift I u).mp hu
  obtain ⟨hkv, hv⟩ := (mem_lift I v).mp hv
  exact hI ⟨u, hku⟩ ⟨v, hkv⟩ huv hu hv

theorem restrict_independent (adj : V → V → Prop) (keep : V → Prop)
    [DecidablePred keep] (I : Finset V) (hI : Independent adj I) :
    Independent (fun u v : {v // keep v} => adj u.val v.val) (restrict keep I) := by
  intro u v huv hu hv
  exact hI u.val v.val huv ((mem_restrict keep I u).mp hu) ((mem_restrict keep I v).mp hv)

theorem weight_lift (w : V → ℚ) {keep : V → Prop} [DecidablePred keep]
    (I : Finset {v // keep v}) :
    weight w (lift I) = weight (fun v : {v // keep v} => w v.val) I := by
  simp only [weight_eq_sum, lift, Finset.sum_map, Function.Embedding.subtype_apply]

/-- Extend a subtype vector by zero outside the retained vertices. -/
def zeroExtend (keep : V → Prop) [DecidablePred keep]
    (x : {v // keep v} → ℚ) (v : V) : ℚ :=
  if h : keep v then x ⟨v, h⟩ else 0

@[simp] theorem zeroExtend_at (keep : V → Prop) [DecidablePred keep]
    (x : {v // keep v} → ℚ) (v : {v // keep v}) : zeroExtend keep x v.val = x v := by
  simp [zeroExtend, v.property]

theorem objective_zeroExtend (w : V → ℚ) (keep : V → Prop) [DecidablePred keep]
    (x : {v // keep v} → ℚ) :
    objective w (zeroExtend keep x) = objective (fun v : {v // keep v} => w v.val) x := by
  unfold objective
  apply Eq.symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro v hv
    have hn : ¬ keep v := by simpa using hv
    simp [zeroExtend, hn]
  · intro v
    simp

/-- The residual optimization statement is an ordinary optimum on its actual
finite induced vertex type, without extraneous coordinates. -/
theorem residual_optimal (adj : V → V → Prop) (w z : V → ℚ)
    (hz : Optimal adj w z) (hh : HalfIntegral z) :
    Optimal (fun u v : {v // z v = 1 / 2} => adj u.val v.val)
      (fun v : {v // z v = 1 / 2} => w v.val) (fun _ => 1 / 2) := by
  have hr := residual_half_optimal adj w z hz hh
  refine ⟨⟨fun _ => by norm_num, fun _ _ _ => by norm_num⟩, ?_⟩
  intro x hx
  let y := zeroExtend (fun v => z v = 1 / 2) x
  have hy : ResidualFeasible adj z y := by
    constructor
    · intro v hv
      simpa [y, zeroExtend, hv] using hx.1 ⟨v, hv⟩
    · intro u v huv hu hv
      simpa [y, zeroExtend, hu, hv] using hx.2 ⟨u, hu⟩ ⟨v, hv⟩ huv
  have hsum (q : {v // z v = 1 / 2} → ℚ) :
      residualObjective w z (zeroExtend (fun v => z v = 1 / 2) q) =
        objective (fun v : {v // z v = 1 / 2} => w v.val) q := by
    rw [← objective_zeroExtend]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : z v = 1 / 2
    · simp only [zeroExtend, dite_eq_left hv, ite_eq_left hv]
    · simp only [zeroExtend, dite_eq_right hv, ite_eq_right hv, mul_zero]
  have hbase : residualObjective w z (fun _ => 1 / 2) =
      residualObjective w z (zeroExtend (fun v => z v = 1 / 2) (fun _ => 1 / 2)) := by
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : z v = 1 / 2
    · simp only [zeroExtend, dite_eq_left hv, ite_eq_left hv]
    · simp only [zeroExtend, dite_eq_right hv, ite_eq_right hv, mul_zero]
  have hb := hr.2 y hy
  rw [hbase] at hb
  simpa only [y, hsum] using hb

/-- A maximum on the actual residual subtype lifts, and weighted persistence
then extends it to an original maximum. -/
theorem residual_maximum (adj : V → V → Prop) (w z : V → ℚ)
    (hz : Optimal adj w z) (hh : HalfIntegral z)
    (J : Finset {v // z v = 1 / 2})
    (hJ : Independent (fun u v : {v // z v = 1 / 2} => adj u.val v.val) J)
    (hm : ∀ K, Independent (fun u v : {v // z v = 1 / 2} => adj u.val v.val) K →
      weight (fun v : {v // z v = 1 / 2} => w v.val) K ≤
        weight (fun v : {v // z v = 1 / 2} => w v.val) J) :
    Independent adj (replacement z (lift J)) ∧
      weight w (replacement z (lift J)) = weight w (fixedSet z) +
        weight (fun v : {v // z v = 1 / 2} => w v.val) J ∧
      ∀ I, Independent adj I → weight w I ≤ weight w (replacement z (lift J)) := by
  have hmax : ∀ K, Independent adj K → (∀ v ∈ K, z v = 1 / 2) →
      weight w K ≤ weight w (lift J) := by
    intro K hK hs
    have hr := hm (restrict (fun v => z v = 1 / 2) K)
      (restrict_independent adj _ K hK)
    rw [← weight_lift, lift_restrict_of_supported _ K hs, ← weight_lift] at hr
    exact hr
  have hr := residual_maximum_extends adj w z hz hh (lift J)
    (lift_independent adj J hJ) (lift_supported J) hmax
  simpa only [weight_lift] using hr

end WeightedMIS.InducedReduction
