module

public import WeightedMIS.InducedReduction

/-!
# Relabelling actual finite graph optimizations

Vertex equivalences transport feasible vectors, all-half optimality, and
weighted independent sets. The objective is unchanged by actual finite sums.
-/

@[expose] public section

namespace WeightedMIS.GraphRelabeling

open Persistence
open scoped BigOperators

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (e : U ≃ V) (adjU : U → U → Prop) (adjV : V → V → Prop)
    (hadj : ∀ u v, adjU u v ↔ adjV (e u) (e v))

include hadj in
/-- Pull back a feasible vector along an actual vertex relabelling. -/
theorem feasible_pullback (x : V → ℚ) (hx : Feasible adjV x) :
    Feasible adjU (fun u => x (e u)) :=
  ⟨fun u => hx.1 _, fun u v huv => hx.2 _ _ ((hadj u v).mp huv)⟩

include hadj in
/-- Pushing a feasible vector through the inverse relabelling is feasible. -/
theorem feasible_pushforward (x : U → ℚ) (hx : Feasible adjU x) :
    Feasible adjV (fun v => x (e.symm v)) := by
  refine ⟨fun v => hx.1 _, ?_⟩
  intro u v huv
  apply hx.2
  exact (hadj (e.symm u) (e.symm v)).mpr (by simpa only [Equiv.apply_symm_apply] using huv)

/-- Finite objectives are invariant under the same relabelling. -/
theorem objective_relabel (w x : V → ℚ) :
    objective (fun u => w (e u)) (fun u => x (e u)) = objective w x :=
  e.sum_comp (fun v => w v * x v)

include hadj in
/-- Actual all-half LP optimality is preserved by graph relabelling. -/
theorem half_optimal_pullback (w : V → ℚ) (ho : Optimal adjV w (fun _ => 1 / 2)) :
    Optimal adjU (fun u => w (e u)) (fun _ => 1 / 2) := by
  refine ⟨feasible_pullback e adjU adjV hadj _ ho.1, ?_⟩
  intro x hx
  have hh := ho.2 _ (feasible_pushforward e adjU adjV hadj x hx)
  have he := objective_relabel e w (fun v => x (e.symm v))
  simp only [Equiv.symm_apply_apply] at he
  rw [← he, ← objective_relabel e w (fun _ => 1 / 2)] at hh
  exact hh

/-- The actual selected vertices, transported by the equivalence. -/
def mapSet (I : Finset U) : Finset V := I.map e.toEmbedding

@[simp] theorem mem_mapSet (I : Finset U) (v : V) :
    v ∈ mapSet e I ↔ e.symm v ∈ I := by simp [mapSet]

include hadj in
/-- Actual independent sets survive a graph relabelling. -/
theorem map_independent (I : Finset U) (hI : Independent adjU I) :
    Independent adjV (mapSet e I) := by
  intro u v huv hu hv
  apply hI (e.symm u) (e.symm v)
  · exact (hadj _ _).mpr (by simpa only [Equiv.apply_symm_apply] using huv)
  · exact (mem_mapSet e I u).mp hu
  · exact (mem_mapSet e I v).mp hv

/-- The weight of the transported selected vertices is exactly unchanged. -/
theorem weight_map (w : V → ℚ) (I : Finset U) :
    weight w (mapSet e I) = weight (fun u => w (e u)) I := by
  rw [InducedReduction.weight_eq_sum, InducedReduction.weight_eq_sum]
  simp [mapSet]

include hadj in
/-- A component optimum remains an optimum after actual vertex relabelling. -/
theorem maximum_map (w : V → ℚ) (I : Finset U) (hI : Independent adjU I)
    (hm : ∀ J, Independent adjU J → weight (fun u => w (e u)) J ≤
      weight (fun u => w (e u)) I) :
    Independent adjV (mapSet e I) ∧
      ∀ J, Independent adjV J → weight w J ≤ weight w (mapSet e I) := by
  refine ⟨map_independent e adjU adjV hadj I hI, ?_⟩
  intro J hJ
  have hadj' : ∀ u v, adjV u v ↔ adjU (e.symm u) (e.symm v) := by
    intro u v
    simpa only [Equiv.apply_symm_apply] using (hadj (e.symm u) (e.symm v)).symm
  have hj := map_independent e.symm adjV adjU hadj' J hJ
  have h := hm (mapSet e.symm J) hj
  have hw := weight_map e.symm (fun u => w (e u)) J
  simp only [Equiv.apply_symm_apply] at hw
  rw [hw, ← weight_map e w I] at h
  exact h

end WeightedMIS.GraphRelabeling
