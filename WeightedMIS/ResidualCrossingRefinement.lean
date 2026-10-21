module

public import WeightedMIS.RegisterResidualCrossing
public import WeightedMIS.MaxFlowResidual

/-! # The compiled residual scan agrees with the maximum-flow search -/

@[expose] public section

namespace WeightedMIS.ResidualCrossingRefinement

open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords

variable {V : Type*} [Fintype V] [DecidableEq V] {n b : ℕ}

def encodeArc (enc : V → Bits n) (caps : V → V → Bits b) (a : V × V) : Arc n b :=
  ⟨enc a.1, enc a.2, caps a.1 a.2⟩

theorem encoded_membership (enc : V → Bits n) (hinj : Function.Injective (fun v => (enc v).value))
    (S : Finset V) (u : V) :
    (∃ key ∈ S.toList.map enc, key.value = (enc u).value) ↔ u ∈ S := by
  constructor
  · rintro ⟨key, hkey, he⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hkey
    have hu : v = u := hinj he
    simpa [hu] using hv
  · intro hu
    exact ⟨enc u, List.mem_map.mpr ⟨u, by simpa using hu, rfl⟩, rfl⟩

theorem predicate_exact (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (caps : V → V → Bits b) (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : MaxFlowCore.Feasible c s t f)
    (hcap : ∀ u v, (caps u v).value = MaxFlowResidual.matrix c f u v)
    (S : Finset V) (d : Bits b) (a : V × V) :
    RegisterResidualPredicate.accepts (S.toList.map enc) d (encodeArc enc caps a) =
      decide (a.1 ∈ S ∧ a.2 ∉ S ∧ MaxFlowScaling.relation c f d.value a.1 a.2) := by
  apply Bool.eq_iff_iff.mpr
  rw [RegisterResidualPredicate.accepts_iff, decide_eq_true_eq]
  simp only [encodeArc, encoded_membership enc hinj, hcap,
    MaxFlowResidual.matrix_relation c s t f hf]

theorem crossing_exact (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (caps : V → V → Bits b) (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : MaxFlowCore.Feasible c s t f)
    (hcap : ∀ u v, (caps u v).value = MaxFlowResidual.matrix c f u v)
    (nodes : List V) (S : Finset V) (d : Bits b) :
    RegisterResidualCrossing.crossing (S.toList.map enc) d
      ((nodes.product nodes).map (encodeArc enc caps)) =
      (MaxFlowReach.crossing (MaxFlowScaling.relation c f d.value) nodes S).map
        (encodeArc enc caps) := by
  unfold RegisterResidualCrossing.crossing MaxFlowReach.crossing
  rw [List.find?_map]
  congr 1
  apply congrArg (fun pred => (nodes.product nodes).find? pred)
  funext a
  exact predicate_exact enc hinj caps c s t f hf hcap S d a


theorem encoded_list_membership (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value)) (seen : List V) (u : V) :
    (∃ key ∈ seen.map enc, key.value = (enc u).value) ↔ u ∈ seen := by
  constructor
  · rintro ⟨key, hkey, he⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hkey
    simpa [hinj he] using hv
  · intro hu
    exact ⟨enc u, List.mem_map.mpr ⟨u, hu, rfl⟩, rfl⟩

theorem crossing_list_exact (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (caps : V → V → Bits b) (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : MaxFlowCore.Feasible c s t f)
    (hcap : ∀ u v, (caps u v).value = MaxFlowResidual.matrix c f u v)
    (nodes seen : List V) (d : Bits b) :
    RegisterResidualCrossing.crossing (seen.map enc) d
      ((nodes.product nodes).map (encodeArc enc caps)) =
      (MaxFlowReach.crossing (MaxFlowScaling.relation c f d.value) nodes seen.toFinset).map
        (encodeArc enc caps) := by
  unfold RegisterResidualCrossing.crossing MaxFlowReach.crossing
  rw [List.find?_map]
  congr 1
  apply congrArg (fun pred => (nodes.product nodes).find? pred)
  funext a
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply]
  rw [RegisterResidualPredicate.accepts_iff, decide_eq_true_eq]
  simp only [encodeArc, encoded_list_membership enc hinj,
    List.mem_toFinset, hcap, MaxFlowResidual.matrix_relation c s t f hf]

end WeightedMIS.ResidualCrossingRefinement
