module

public import WeightedMIS.MaxFlowCached

/-!
# Capacity scaling from an explicit sufficient exponent

A binary representation may supply a convenient exponent larger than the
minimum one. Its additional empty phases preserve the flow and cut, and all
phase and matrix-size bounds remain explicit.
-/

@[expose] public section

namespace WeightedMIS.MaxFlowScaling

open scoped BigOperators
open WeightedMIS.MaxFlowCore

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem capacity_entry_le_sum (c : V → V → ℕ) (u v : V) : c u v ≤ capacitySum c := by
  unfold capacitySum
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, c a b)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ u))

def solveFromExponent (c : V → V → ℕ) (nodes : List V) (s t : V) (k : ℕ) : Result V :=
  scales c nodes s t k (fun _ _ => 0)

theorem solveFromExponent_closed_of_entries (c : V → V → ℕ) (nodes : List V)
    (complete : ∀ v, v ∈ nodes) (s t : V) (hst : s ≠ t) (k : ℕ)
    (hcapacity : ∀ u v, c u v ≤ 2 ^ (k + 1)) :
    Closed c s t 1 (solveFromExponent c nodes s t k) := by
  apply scales_closed c nodes complete s t hst k _ (zero_feasible c s t)
    {s} (by simp) (by simpa using Ne.symm hst)
  intro u _ v _
  change (c u v : ℤ) - 0 ≤ ((2 ^ (k + 1) : ℕ) : ℤ)
  simp only [sub_zero]
  exact_mod_cast hcapacity u v

theorem solveFromExponent_closed (c : V → V → ℕ) (nodes : List V)
    (complete : ∀ v, v ∈ nodes) (s t : V) (hst : s ≠ t) (k : ℕ)
    (hcapacity : capacitySum c ≤ 2 ^ (k + 1)) :
    Closed c s t 1 (solveFromExponent c nodes s t k) := by
  apply scales_closed c nodes complete s t hst k _ (zero_feasible c s t)
    {s} (by simp) (by simpa using Ne.symm hst)
  intro u _ v _
  have hc := (capacity_entry_le_sum c u v).trans hcapacity
  change (c u v : ℤ) - 0 ≤ ((2 ^ (k + 1) : ℕ) : ℤ)
  simpa only [sub_zero] using (show (c u v : ℤ) ≤ (2 ^ (k + 1) : ℕ) by exact_mod_cast hc)

theorem solveFromExponent_correct (c : V → V → ℕ) (nodes : List V)
    (complete : ∀ v, v ∈ nodes) (s t : V) (hst : s ≠ t) (k : ℕ)
    (hcapacity : capacitySum c ≤ 2 ^ (k + 1)) :
    let r := solveFromExponent c nodes s t k
    Feasible c s t r.flow ∧ s ∈ r.cut ∧ t ∉ r.cut ∧
      value r.flow s = cutCapacity c r.cut ∧
      ∀ S : Finset V, s ∈ S → t ∉ S → cutCapacity c r.cut ≤ cutCapacity c S := by
  have hc := solveFromExponent_closed c nodes complete s t hst k hcapacity
  have hm := minimum_cut_of_residual_zero c s t _ hc.1 _ hc.2.1 hc.2.2.1
    (fun u hu v hv => by
      have hlo := residual_nonnegative c s t _ hc.1 u v
      have hhi := hc.2.2.2 u hu v (Finset.mem_compl.mp hv)
      omega)
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hm.1, hm.2⟩

theorem solveFromExponent_correct_of_entries (c : V → V → ℕ) (nodes : List V)
    (complete : ∀ v, v ∈ nodes) (s t : V) (hst : s ≠ t) (k : ℕ)
    (hcapacity : ∀ u v, c u v ≤ 2 ^ (k + 1)) :
    let r := solveFromExponent c nodes s t k
    Feasible c s t r.flow ∧ s ∈ r.cut ∧ t ∉ r.cut ∧
      value r.flow s = cutCapacity c r.cut ∧
      ∀ S : Finset V, s ∈ S → t ∉ S → cutCapacity c r.cut ≤ cutCapacity c S := by
  have hc := solveFromExponent_closed_of_entries c nodes complete s t hst k hcapacity
  have hm := minimum_cut_of_residual_zero c s t _ hc.1 _ hc.2.1 hc.2.2.1
    (fun u hu v hv => by
      have hlo := residual_nonnegative c s t _ hc.1 u v
      have hhi := hc.2.2.2 u hu v (Finset.mem_compl.mp hv)
      omega)
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hm.1, hm.2⟩

theorem solveFromExponent_counts (c : V → V → ℕ) (nodes : List V) (s t : V) (k : ℕ) :
    (solveFromExponent c nodes s t k).searches ≤ (k + 1) * (2 * Fintype.card V ^ 2 + 2) ∧
      (solveFromExponent c nodes s t k).augmentations ≤ (k + 1) * (2 * Fintype.card V ^ 2 + 1) := by
  simpa only [solveFromExponent, phaseFuel, Nat.add_assoc] using
    scales_counts c nodes s t k (fun _ _ => 0)

/-- At a threshold above every capacity, the actual scan finds no arc. -/
theorem zero_search_of_entries (c : V → V → ℕ) (nodes : List V) (s : V) (d : ℕ)
    (hd : ∀ u v, c u v < d) : search c nodes s d (fun _ _ => 0) = MaxFlowReach.initial s := by
  have hcross (S : Finset V) : MaxFlowReach.crossing (relation c (fun _ _ => 0) d) nodes S = none := by
    apply List.find?_eq_none.mpr
    intro a _
    have hc := hd a.1 a.2
    have hn : ¬relation c (fun _ _ => 0) d a.1 a.2 := by
      unfold relation MaxFlowCore.residual
      simp only [sub_zero]
      exact_mod_cast (show ¬d ≤ c a.1 a.2 by omega)
    simp [hn]
  unfold search
  cases Fintype.card V <;> simp only [MaxFlowReach.explore, hcross]

theorem zero_search (c : V → V → ℕ) (nodes : List V) (s : V) (d : ℕ)
    (hd : capacitySum c < d) : search c nodes s d (fun _ _ => 0) = MaxFlowReach.initial s :=
  zero_search_of_entries c nodes s d (fun u v => (capacity_entry_le_sum c u v).trans_lt hd)

theorem zero_phase_of_entries (c : V → V → ℕ) (nodes : List V) (s t : V) (hst : s ≠ t)
    (d fuel : ℕ) (hd : ∀ u v, c u v < d) :
    phase c nodes s t d fuel (fun _ _ => 0) = ⟨(fun _ _ => 0), {s}, 1, 0⟩ := by
  cases fuel <;> simp [phase, zero_search_of_entries c nodes s d hd, MaxFlowReach.initial, Ne.symm hst]

theorem zero_phase (c : V → V → ℕ) (nodes : List V) (s t : V) (hst : s ≠ t)
    (d fuel : ℕ) (hd : capacitySum c < d) :
    phase c nodes s t d fuel (fun _ _ => 0) = ⟨(fun _ _ => 0), {s}, 1, 0⟩ := by
  cases fuel <;> simp [phase, zero_search c nodes s d hd, MaxFlowReach.initial, Ne.symm hst]

/-- Padding the initial exponent changes only the counters, not the flow or cut. -/
theorem solveFromExponent_output_eq (c : V → V → ℕ) (nodes : List V)
    (s t : V) (hst : s ≠ t) (k : ℕ) (hk : initialScale c ≤ k) :
    (solveFromExponent c nodes s t k).flow = (solve c nodes s t).flow ∧
      (solveFromExponent c nodes s t k).cut = (solve c nodes s t).cut := by
  induction k, hk using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ k hk ih =>
    have hd : capacitySum c < 2 ^ (k + 1) :=
      (Nat.lt_log2_self (n := capacitySum c)).trans_le
        (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hk 1))
    change (scales c nodes s t (k + 1) (fun _ _ => 0)).flow = _ ∧
      (scales c nodes s t (k + 1) (fun _ _ => 0)).cut = _
    simp only [scales, zero_phase c nodes s t hst _ _ hd]
    exact ih

theorem solveFromExponent_padding (c : V → V → ℕ) (nodes : List V)
    (s t : V) (hst : s ≠ t) (base : ℕ) (hbase : ∀ u v, c u v < 2 ^ (base + 1))
    (k : ℕ) (hk : base ≤ k) :
    (solveFromExponent c nodes s t k).flow = (solveFromExponent c nodes s t base).flow ∧
      (solveFromExponent c nodes s t k).cut = (solveFromExponent c nodes s t base).cut := by
  induction k, hk using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ k hk ih =>
    have hd (u v : V) : c u v < 2 ^ (k + 1) :=
      (hbase u v).trans_le (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hk 1))
    change (scales c nodes s t (k + 1) (fun _ _ => 0)).flow = _ ∧
      (scales c nodes s t (k + 1) (fun _ _ => 0)).cut = _
    simp only [scales, zero_phase_of_entries c nodes s t hst _ _ hd]
    exact ih

/-- An entry-width exponent gives exactly the same final flow and cut as the
capacity-sum exponent, even when it is smaller. -/
theorem solveFromExponent_output_eq_of_entries (c : V → V → ℕ) (nodes : List V)
    (s t : V) (hst : s ≠ t) (k : ℕ) (hcapacity : ∀ u v, c u v < 2 ^ (k + 1)) :
    (solveFromExponent c nodes s t k).flow = (solve c nodes s t).flow ∧
      (solveFromExponent c nodes s t k).cut = (solve c nodes s t).cut := by
  have hnew := solveFromExponent_padding c nodes s t hst k hcapacity
    (max k (initialScale c)) (le_max_left _ _)
  have hold := solveFromExponent_output_eq c nodes s t hst
    (max k (initialScale c)) (le_max_right _ _)
  exact ⟨hnew.1.symm.trans hold.1, hnew.2.symm.trans hold.2⟩

end WeightedMIS.MaxFlowScaling

namespace WeightedMIS.MaxFlowCached

variable {V : Type*} [Fintype V] [DecidableEq V]

def solveFromExponent (c : V → V → ℕ) (nodes : List V) (s t : V) (k : ℕ) : Result V :=
  scales c nodes s t k (freeze nodes (fun _ _ => 0))

theorem solveFromExponent_refines (c : V → V → ℕ) (nodes : List V)
    (complete : ∀ v, v ∈ nodes) (s t : V) (k : ℕ) :
    decode (solveFromExponent c nodes s t k) = MaxFlowScaling.solveFromExponent c nodes s t k := by
  unfold solveFromExponent MaxFlowScaling.solveFromExponent
  rw [scales_refines c nodes complete, get_freeze nodes complete]

theorem solveFromExponent_table_length (c : V → V → ℕ) (nodes : List V) (s t : V) (k : ℕ) :
    (solveFromExponent c nodes s t k).table.length = nodes.length ^ 2 :=
  scales_table_length c nodes s t _ _ (freeze_length _ _)

end WeightedMIS.MaxFlowCached
