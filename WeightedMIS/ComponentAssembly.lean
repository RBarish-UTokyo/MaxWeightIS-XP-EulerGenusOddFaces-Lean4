module

public import WeightedMIS.GraphComponents
public import WeightedMIS.InducedReduction

/-!
# Optimization on the actual connected components

The all-half optimum restricts to each closed component. Independent sets on
those components assemble with exactly additive objective, so componentwise
maxima yield a maximum on the original graph, including isolated vertices.
-/

@[expose] public section

namespace WeightedMIS.ComponentAssembly

open scoped BigOperators
open Persistence InducedReduction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A closed induced subgraph inherits all-half optimality. -/
theorem closed_half_optimal (adj : V → V → Prop) (w : V → ℚ)
    (keep : V → Prop) [DecidablePred keep]
    (hclosed : ∀ u v, adj u v → (keep u ↔ keep v))
    (ho : Optimal adj w (fun _ => 1 / 2)) :
    Optimal (fun u v : {v // keep v} => adj u.val v.val)
      (fun v : {v // keep v} => w v.val) (fun _ => 1 / 2) := by
  refine ⟨⟨fun _ => by norm_num, fun _ _ _ => by norm_num⟩, ?_⟩
  intro x hx
  let y : V → ℚ := fun v => if h : keep v then x ⟨v, h⟩ else 1 / 2
  have hy : Feasible adj y := by
    constructor
    · intro v
      by_cases hv : keep v
      · simpa only [y, dite_eq_left hv] using hx.1 ⟨v, hv⟩
      · simp only [y, dite_eq_right hv]
        norm_num
    · intro u v huv
      by_cases hu : keep u
      · have hv := (hclosed u v huv).mp hu
        simpa only [y, dite_eq_left hu, dite_eq_left hv] using hx.2 ⟨u, hu⟩ ⟨v, hv⟩ huv
      · have hv : ¬ keep v := mt (hclosed u v huv).mpr hu
        simp only [y, dite_eq_right hu, dite_eq_right hv]
        norm_num
  have he : objective w y = objective w (fun _ => 1 / 2) +
      objective (fun v : {v // keep v} => w v.val) x -
      objective (fun v : {v // keep v} => w v.val) (fun _ => 1 / 2) := by
    have hp : y = fun v => 1 / 2 + zeroExtend keep (fun v => x v - 1 / 2) v := by
      funext v
      by_cases hv : keep v <;> simp only [y, zeroExtend, hv, dite_true, dite_false] <;> ring
    rw [hp]
    have hd := objective_zeroExtend w keep (fun v => x v - 1 / 2)
    simp only [objective, mul_add, Finset.sum_add_distrib, mul_sub,
      Finset.sum_sub_distrib] at hd ⊢
    rw [hd]
    ring
  have hh := ho.2 y hy
  rw [he] at hh
  linarith

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Select exactly the set prescribed in each vertex's own fiber. -/
def assemble (part : V → Q) (I : ∀ q, Finset {v // part v = q}) : Finset V :=
  Finset.univ.filter fun v => (⟨v, rfl⟩ : {u // part u = part v}) ∈ I (part v)

theorem mem_assemble (part : V → Q) (I : ∀ q, Finset {v // part v = q})
    (q : Q) (v : {v // part v = q}) : v.val ∈ assemble part I ↔ v ∈ I q := by
  rcases v with ⟨v, hv⟩
  subst q
  simp [assemble]

/-- The original set weight is the exact sum of its fiber restrictions. -/
theorem weight_partition (part : V → Q) (w : V → ℚ) (J : Finset V) :
    weight w J = ∑ q, weight (fun v : {v // part v = q} => w v.val)
      (restrict (fun v => part v = q) J) := by
  unfold weight objective
  rw [← Fintype.sum_fiberwise part (fun v => w v * indicator J v)]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro v _
  simp only [indicator, mem_restrict]

/-- Fiber assembly preserves the additive objective exactly. -/
theorem weight_assemble (part : V → Q) (w : V → ℚ) (I : ∀ q, Finset {v // part v = q}) :
    weight w (assemble part I) = ∑ q, weight (fun v : {v // part v = q} => w v.val) (I q) := by
  unfold weight objective
  rw [← Fintype.sum_fiberwise part (fun v => w v * indicator (assemble part I) v)]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro v _
  simp only [indicator, mem_assemble]

/-- No edge crosses the partition, so independently chosen fiber sets assemble. -/
theorem assemble_independent (adj : V → V → Prop) (part : V → Q)
    (hclosed : ∀ u v, adj u v → part u = part v)
    (I : ∀ q, Finset {v // part v = q})
    (hI : ∀ q, Independent (fun u v : {v // part v = q} => adj u.val v.val) (I q)) :
    Independent adj (assemble part I) := by
  intro u v huv hu hv
  let q := part u
  have hqu : part u = q := rfl
  have hqv : part v = q := (hclosed u v huv).symm
  exact hI q ⟨u, hqu⟩ ⟨v, hqv⟩ huv
    ((mem_assemble part I q ⟨u, hqu⟩).mp hu)
    ((mem_assemble part I q ⟨v, hqv⟩).mp hv)

/-- Actual fiber maxima combine to an original maximum. -/
theorem assemble_maximum (adj : V → V → Prop) (part : V → Q)
    (hclosed : ∀ u v, adj u v → part u = part v) (w : V → ℚ)
    (I : ∀ q, Finset {v // part v = q})
    (hI : ∀ q, Independent (fun u v : {v // part v = q} => adj u.val v.val) (I q))
    (hm : ∀ q J, Independent (fun u v : {v // part v = q} => adj u.val v.val) J →
      weight (fun v : {v // part v = q} => w v.val) J ≤
        weight (fun v : {v // part v = q} => w v.val) (I q)) :
    Independent adj (assemble part I) ∧
      ∀ J, Independent adj J → weight w J ≤ weight w (assemble part I) := by
  refine ⟨assemble_independent adj part hclosed I hI, ?_⟩
  intro J hJ
  rw [weight_partition part w J, weight_assemble]
  exact Finset.sum_le_sum fun q _ => hm q _ (restrict_independent adj _ J hJ)

variable {E : Type*} (left right : E → V)

/-- Actual endpoint adjacency never crosses a walk-connected component. -/
theorem component_closed (u v : V) (huv : EdgeTransport.Adj left right u v) :
    Incidence.componentOf left right u = Incidence.componentOf left right v := by
  obtain ⟨e, ⟨hl, hr⟩ | ⟨hl, hr⟩⟩ := huv
  · simpa only [hl, hr] using Incidence.componentOf_endpoints left right e
  · simpa only [hl, hr] using (Incidence.componentOf_endpoints left right e).symm

/-- Component endpoint adjacency agrees with induced original adjacency. -/
theorem component_adj_iff (q : Incidence.Component left right)
    (u v : Incidence.ComponentVertex left right q) :
    EdgeTransport.Adj (Incidence.componentLeft left right q) (Incidence.componentRight left right q) u v ↔
      EdgeTransport.Adj left right u.val v.val := by
  constructor
  · rintro ⟨e, ⟨hl, hr⟩ | ⟨hl, hr⟩⟩
    · exact ⟨e.val, Or.inl ⟨congrArg Subtype.val hl, congrArg Subtype.val hr⟩⟩
    · exact ⟨e.val, Or.inr ⟨congrArg Subtype.val hl, congrArg Subtype.val hr⟩⟩
  · rintro ⟨e, ⟨hl, hr⟩ | ⟨hl, hr⟩⟩
    · let e' : Incidence.ComponentEdge left right q := ⟨e, by rw [hl]; exact u.property⟩
      exact ⟨e', Or.inl ⟨Subtype.ext hl, Subtype.ext hr⟩⟩
    · let e' : Incidence.ComponentEdge left right q := ⟨e, by rw [hl]; exact v.property⟩
      exact ⟨e', Or.inr ⟨Subtype.ext hl, Subtype.ext hr⟩⟩

/-- The actual connected component inherits the computed all-half optimum. -/
theorem component_half_optimal [DecidableEq (Incidence.Component left right)] (w : V → ℚ)
    (ho : Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2))
    (q : Incidence.Component left right) :
    Optimal (EdgeTransport.Adj (Incidence.componentLeft left right q) (Incidence.componentRight left right q))
      (fun v : Incidence.ComponentVertex left right q => w v.val) (fun _ => 1 / 2) := by
  classical
  have hc : ∀ u v, EdgeTransport.Adj left right u v →
      (Incidence.componentOf left right u = q ↔ Incidence.componentOf left right v = q) := by
    intro u v huv
    rw [component_closed left right u v huv]
  have hh := closed_half_optimal (EdgeTransport.Adj left right) w
    (fun v => Incidence.componentOf left right v = q) hc ho
  simpa only [Optimal, Feasible, component_adj_iff] using hh

end WeightedMIS.ComponentAssembly
