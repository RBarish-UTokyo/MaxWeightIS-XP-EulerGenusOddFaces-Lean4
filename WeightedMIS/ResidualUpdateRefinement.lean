module

public import WeightedMIS.RegisterResidualTableUpdate
public import WeightedMIS.ResidualCrossingRefinement

/-!
# The compiled residual update refines integer flow augmentation

Endpoint membership is proved exact from the injective binary vertex encoding.
A simple supported path discharges subtraction underflow, and the two directed
input capacities discharge every addition-width premise. No separate numerical
oracle is required for the represented update.
-/

@[expose] public section

namespace WeightedMIS.ResidualUpdateRefinement

open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords
open WeightedMIS.ResidualCrossingRefinement

variable {V : Type*} [Fintype V] [DecidableEq V] {n b pb : ℕ}

theorem encoded_membership (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (pathCaps : V → V → Bits pb) (path : List (V × V)) (u v : V) :
    RegisterArcMembership.found (enc u) (enc v) (path.map (encodeArc enc pathCaps)) = true ↔
      (u, v) ∈ path := by
  rw [RegisterArcMembership.found_iff]
  constructor
  · rintro ⟨arc, hm, hs, ht⟩
    obtain ⟨⟨a, b⟩, ha, rfl⟩ := List.mem_map.mp hm
    have hau : a = u := hinj hs
    have hbv : b = v := hinj ht
    simpa [hau, hbv] using ha
  · intro hm
    exact ⟨encodeArc enc pathCaps (u, v), List.mem_map.mpr ⟨(u, v), hm, rfl⟩, rfl, rfl⟩

theorem encoded_membership_eq (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (pathCaps : V → V → Bits pb) (path : List (V × V)) (u v : V) :
    RegisterArcMembership.found (enc u) (enc v) (path.map (encodeArc enc pathCaps)) =
      decide ((u, v) ∈ path) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using encoded_membership enc hinj pathCaps path u v

theorem count_eq_indicator (path : List (V × V)) (hn : path.Nodup) (a : V × V) :
    path.count a = if a ∈ path then 1 else 0 := by
  by_cases hm : a ∈ path
  · have hp := List.count_pos_iff.mpr hm
    have hb := List.nodup_iff_count_le_one.mp hn a
    simp only [hm, ↓reduceIte]
    omega
  · simp [hm, List.count_eq_zero.mpr hm]

/-- The exact arithmetic used by the machine is the natural residual update. -/
theorem arithmetic_eq (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (pathCaps : V → V → Bits pb) (path : List (V × V)) (hn : path.Nodup)
    (residual : V → V → ℕ) (delta : ℕ) (u v : V) :
    (residual u v - if RegisterArcMembership.found (enc u) (enc v)
        (path.map (encodeArc enc pathCaps)) then delta else 0) +
      (if RegisterArcMembership.found (enc v) (enc u)
        (path.map (encodeArc enc pathCaps)) then delta else 0) =
      MaxFlowResidual.update residual path delta u v := by
  rw [encoded_membership_eq enc hinj, encoded_membership_eq enc hinj]
  simp only [MaxFlowResidual.update, count_eq_indicator path hn, decide_eq_true_eq]
  split_ifs <;> simp

/-- Both endpoint words remain shared, and the capacity value equals the
residual of the actual augmented integer flow. -/
theorem update_value (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (caps : V → V → Bits b) (pathCaps : V → V → Bits pb)
    (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : MaxFlowCore.Feasible c s t f)
    (hcap : ∀ u v, (caps u v).value = MaxFlowResidual.matrix c f u v)
    (path : List (V × V)) (hw : ShortestPath.IsWalk Prod.fst Prod.snd s t path)
    (hn : path.Nodup) (delta : Bits b)
    (hd : ∀ a ∈ path, (delta.value : ℤ) ≤ MaxFlowCore.residual c f a.1 a.2)
    (hwidth : ∀ u v, c u v + c v u < 2 ^ b) (u v : V) :
    (RegisterResidualUpdate.update (encodeArc enc caps (u, v))
      (path.map (encodeArc enc pathCaps)) delta).source = enc u ∧
    (RegisterResidualUpdate.update (encodeArc enc caps (u, v))
      (path.map (encodeArc enc pathCaps)) delta).target = enc v ∧
    (RegisterResidualUpdate.update (encodeArc enc caps (u, v))
      (path.map (encodeArc enc pathCaps)) delta).capacity.value =
        MaxFlowResidual.matrix c (MaxFlowCore.augment f path delta.value) u v := by
  refine ⟨rfl, rfl, ?_⟩
  have hsub : RegisterArcMembership.found (enc u) (enc v)
      (path.map (encodeArc enc pathCaps)) = true → delta.value ≤ (caps u v).value := by
    intro hm
    have hp := (encoded_membership enc hinj pathCaps path u v).mp hm
    rw [hcap]
    exact (MaxFlowResidual.matrix_relation c s t f hf delta.value u v).mpr (hd (u, v) hp)
  have hbound : (caps u v).value -
      (if RegisterArcMembership.found (enc u) (enc v) (path.map (encodeArc enc pathCaps)) then delta.value else 0) +
      (if RegisterArcMembership.found (enc v) (enc u) (path.map (encodeArc enc pathCaps)) then delta.value else 0) < 2 ^ b := by
    rw [hcap, arithmetic_eq enc hinj pathCaps path hn]
    exact lt_of_le_of_lt (MaxFlowResidual.update_le c s t f hf path hw hn delta.value hd u v) (hwidth u v)
  rw [RegisterResidualUpdate.update_capacity_value _ _ _ hsub hbound]
  change (caps u v).value -
    (if RegisterArcMembership.found (enc u) (enc v) (path.map (encodeArc enc pathCaps)) then delta.value else 0) +
    (if RegisterArcMembership.found (enc v) (enc u) (path.map (encodeArc enc pathCaps)) then delta.value else 0) = _
  rw [hcap, arithmetic_eq enc hinj pathCaps path hn, MaxFlowResidual.update_matrix c s t f hf path hw hn delta.value hd]

/-- The new capacity words are those actually constructed by the binary
update; this definition introduces no fresh choice of an encoding. -/
def updatedCaps (enc : V → Bits n) (caps : V → V → Bits b) (pathCaps : V → V → Bits pb)
    (path : List (V × V)) (delta : Bits b) (u v : V) : Bits b :=
  (RegisterResidualUpdate.update (encodeArc enc caps (u, v))
    (path.map (encodeArc enc pathCaps)) delta).capacity

/-- The compiled table map remains an encoded matrix in exactly the original
pair order. The preceding theorem identifies every one of its natural values. -/
theorem table_map (enc : V → Bits n) (caps : V → V → Bits b) (pathCaps : V → V → Bits pb)
    (path entries : List (V × V)) (delta : Bits b) :
    (entries.map (encodeArc enc caps)).map
        (fun arc => RegisterResidualUpdate.update arc (path.map (encodeArc enc pathCaps)) delta) =
      entries.map (encodeArc enc (updatedCaps enc caps pathCaps path delta)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  cases a
  rfl

theorem updatedCaps_value (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (caps : V → V → Bits b) (pathCaps : V → V → Bits pb)
    (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : MaxFlowCore.Feasible c s t f)
    (hcap : ∀ u v, (caps u v).value = MaxFlowResidual.matrix c f u v)
    (path : List (V × V)) (hw : ShortestPath.IsWalk Prod.fst Prod.snd s t path)
    (hn : path.Nodup) (delta : Bits b)
    (hd : ∀ a ∈ path, (delta.value : ℤ) ≤ MaxFlowCore.residual c f a.1 a.2)
    (hwidth : ∀ u v, c u v + c v u < 2 ^ b) (u v : V) :
    (updatedCaps enc caps pathCaps path delta u v).value =
      MaxFlowResidual.matrix c (MaxFlowCore.augment f path delta.value) u v :=
  (update_value enc hinj caps pathCaps c s t f hf hcap path hw hn delta hd hwidth u v).2.2

end WeightedMIS.ResidualUpdateRefinement
