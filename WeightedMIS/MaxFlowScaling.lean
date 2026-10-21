module

public import WeightedMIS.MaxFlowCore
public import WeightedMIS.MaxFlowReach

/-!
# Executable capacity-scaling maximum flow

At scale d, each augmentation adds exactly d units along a residual path.
The cut retained from the preceding scale bounds the remaining flow gap by
2 n² d, so 2 n² + 1 attempts suffice. There is one phase per binary capacity
bit. All residual paths and cuts are obtained by the concrete finite search.
-/

@[expose] public section

namespace WeightedMIS.MaxFlowScaling

open scoped BigOperators
open MaxFlowCore

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Result (V : Type*) where
  flow : V → V → ℤ
  cut : Finset V
  searches : ℕ
  augmentations : ℕ

/-- Residual arcs capable of carrying the current scaling amount. -/
def relation (c : V → V → ℕ) (f : V → V → ℤ) (d : ℕ) (u v : V) : Prop :=
  (d : ℤ) ≤ residual c f u v

instance (c : V → V → ℕ) (f : V → V → ℤ) (d : ℕ) : DecidableRel (relation c f d) :=
  fun _ _ => inferInstanceAs (Decidable (_ ≤ _))

def search (c : V → V → ℕ) (nodes : List V) (s : V) (d : ℕ) (f : V → V → ℤ) :
    MaxFlowReach.State V :=
  MaxFlowReach.explore (relation c f d) nodes (Fintype.card V) (MaxFlowReach.initial s)

/-- A fuel-bounded scaling phase, stopping as soon as the sink is unreachable. -/
def phase (c : V → V → ℕ) (nodes : List V) (s t : V) (d : ℕ) :
    ℕ → (V → V → ℤ) → Result V
  | 0, f => ⟨f, (search c nodes s d f).seen, 1, 0⟩
  | fuel + 1, f =>
      let q := search c nodes s d f
      if t ∈ q.seen then
        let r := phase c nodes s t d fuel (augment f (q.route t) d)
        { r with searches := r.searches + 1, augmentations := r.augmentations + 1 }
      else ⟨f, q.seen, 1, 0⟩

/-- What it means for a phase to have exhausted its residual threshold. -/
def Closed (c : V → V → ℕ) (s t : V) (d : ℕ) (r : Result V) : Prop :=
  Feasible c s t r.flow ∧ s ∈ r.cut ∧ t ∉ r.cut ∧
    ∀ u ∈ r.cut, ∀ v ∉ r.cut, residual c r.flow u v < (d : ℤ)

/-- A strict cut-gap potential proves that the explicit fuel cannot expire
while another augmentation is possible. -/
theorem phase_closed (c : V → V → ℕ) (nodes : List V)
    (complete : ∀ v, v ∈ nodes) (s t : V) (hst : s ≠ t) (d fuel : ℕ)
    (f : V → V → ℤ) (hf : Feasible c s t f) (S : Finset V)
    (hs : s ∈ S) (ht : t ∉ S)
    (hgap : cutCapacity c S - value f s < (fuel : ℤ) * (d : ℤ)) :
    Closed c s t d (phase c nodes s t d fuel f) := by
  induction fuel generalizing f with
  | zero =>
      have hh := value_le_cut c s t f hf S hs ht
      simp only [Nat.cast_zero, zero_mul] at hgap
      omega
  | succ fuel ih =>
      have hsearch := MaxFlowReach.search_spec (relation c f d) nodes complete s t
      change s ∈ (search c nodes s d f).seen ∧ _ at hsearch
      simp only [phase]
      split
      · rename_i hreach
        have hp := hsearch.2.1 hreach
        have hf' := augment_feasible c s t f hf _ hp.1 (simple_nodup hp.2.1) d hp.2.2
        have hval := augment_value f hst _ hp.1 d
        change value (augment f ((search c nodes s d f).route t) d) s = value f s + (d : ℤ) at hval
        have hgap' : cutCapacity c S - value (augment f ((search c nodes s d f).route t) d) s <
            (fuel : ℤ) * (d : ℤ) := by
          rw [hval]
          push_cast at hgap
          nlinarith
        exact ih _ hf' hgap'
      · rename_i hnot
        refine ⟨hf, hsearch.1, hnot, ?_⟩
        intro u hu v hv
        exact lt_of_not_ge (hsearch.2.2 u hu v hv)

/-- The exact program counters are bounded by the explicit phase fuel. -/
theorem phase_counts (c : V → V → ℕ) (nodes : List V) (s t : V) (d fuel : ℕ)
    (f : V → V → ℤ) :
    (phase c nodes s t d fuel f).searches ≤ fuel + 1 ∧
      (phase c nodes s t d fuel f).augmentations ≤ fuel := by
  induction fuel generalizing f with
  | zero => simp [phase]
  | succ fuel ih =>
      simp only [phase]
      split
      · have hh := ih (augment f ((search c nodes s d f).route t) d)
        dsimp only
        omega
      · simp

/-- The phase budget is independent of capacity magnitudes. -/
def phaseFuel (V : Type*) [Fintype V] : ℕ := 2 * Fintype.card V ^ 2 + 1

/-- The cut inherited from the previous scale validates the fixed phase budget. -/
theorem phase_closed_of_previous_cut (c : V → V → ℕ) (nodes : List V)
    (complete : ∀ v, v ∈ nodes) (s t : V) (hst : s ≠ t) (d : ℕ) (hd : 0 < d)
    (f : V → V → ℤ) (hf : Feasible c s t f) (S : Finset V)
    (hs : s ∈ S) (ht : t ∉ S)
    (hres : ∀ u ∈ S, ∀ v ∉ S, residual c f u v ≤ (2 * d : ℕ)) :
    Closed c s t d (phase c nodes s t d (phaseFuel V) f) := by
  apply phase_closed c nodes complete s t hst d (phaseFuel V) f hf S hs ht
  have hb := gap_le_card_sq c s t f hf S hs ht (2 * d)
    (fun u hu v hv => hres u hu v (Finset.mem_compl.mp hv))
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  unfold phaseFuel
  push_cast at hb ⊢
  nlinarith

/-- Run descending powers of two, ending with unit residual capacity. -/
def scales (c : V → V → ℕ) (nodes : List V) (s t : V) :
    ℕ → (V → V → ℤ) → Result V
  | 0, f => phase c nodes s t 1 (phaseFuel V) f
  | k + 1, f =>
      let r := phase c nodes s t (2 ^ (k + 1)) (phaseFuel V) f
      let r' := scales c nodes s t k r.flow
      ⟨r'.flow, r'.cut, r.searches + r'.searches, r.augmentations + r'.augmentations⟩

/-- All phases terminate within their fixed budgets, producing a unit-threshold cut. -/
theorem scales_closed (c : V → V → ℕ) (nodes : List V)
    (complete : ∀ v, v ∈ nodes) (s t : V) (hst : s ≠ t) (k : ℕ)
    (f : V → V → ℤ) (hf : Feasible c s t f) (S : Finset V)
    (hs : s ∈ S) (ht : t ∉ S)
    (hres : ∀ u ∈ S, ∀ v ∉ S, residual c f u v ≤ (2 ^ (k + 1) : ℕ)) :
    Closed c s t 1 (scales c nodes s t k f) := by
  induction k generalizing f S with
  | zero =>
      exact phase_closed_of_previous_cut c nodes complete s t hst 1 (by omega)
        f hf S hs ht (by simpa using hres)
  | succ k ih =>
      have hp : Closed c s t (2 ^ (k + 1))
          (phase c nodes s t (2 ^ (k + 1)) (phaseFuel V) f) := by
        apply phase_closed_of_previous_cut c nodes complete s t hst _ (by positivity) f hf S hs ht
        intro u hu v hv
        simpa [pow_succ, Nat.mul_comm] using hres u hu v hv
      have hr := ih _ hp.1 _ hp.2.1 hp.2.2.1
        (fun u hu v hv => (hp.2.2.2 u hu v hv).le)
      exact hr

/-- Total search and augmentation counts are polynomial in n and the number
of binary capacity scales. -/
theorem scales_counts (c : V → V → ℕ) (nodes : List V) (s t : V) (k : ℕ)
    (f : V → V → ℤ) :
    (scales c nodes s t k f).searches ≤ (k + 1) * (phaseFuel V + 1) ∧
      (scales c nodes s t k f).augmentations ≤ (k + 1) * phaseFuel V := by
  induction k generalizing f with
  | zero => simpa [scales] using phase_counts c nodes s t 1 (phaseFuel V) f
  | succ k ih =>
      have hp := phase_counts c nodes s t (2 ^ (k + 1)) (phaseFuel V) f
      have hr := ih (phase c nodes s t (2 ^ (k + 1)) (phaseFuel V) f).flow
      simp only [scales]
      constructor <;> nlinarith [hp.1, hp.2, hr.1, hr.2]

/-- Maximum capacity is bounded by the sum of input capacities. -/
def capacitySum (c : V → V → ℕ) : ℕ := ∑ u, ∑ v, c u v

/-- A binary-length initial exponent. -/
def initialScale (c : V → V → ℕ) : ℕ := (capacitySum c).log2

/-- The explicit capacity-scaling maximum-flow program. -/
def solve (c : V → V → ℕ) (nodes : List V) (s t : V) : Result V :=
  scales c nodes s t (initialScale c) (fun _ _ => 0)

/-- The program returns a feasible maximum flow and a minimum source-to-sink cut. -/
theorem solve_correct (c : V → V → ℕ) (nodes : List V)
    (complete : ∀ v, v ∈ nodes) (s t : V) (hst : s ≠ t) :
    let r := solve c nodes s t
    Feasible c s t r.flow ∧ s ∈ r.cut ∧ t ∉ r.cut ∧
      value r.flow s = cutCapacity c r.cut ∧
      ∀ S : Finset V, s ∈ S → t ∉ S → cutCapacity c r.cut ≤ cutCapacity c S := by
  have hc (u v : V) : c u v ≤ capacitySum c := by
    calc
      c u v ≤ ∑ v, c u v := Finset.single_le_sum (by intros; omega) (Finset.mem_univ v)
      _ ≤ capacitySum c := by
        unfold capacitySum
        exact Finset.single_le_sum (f := fun a => ∑ v, c a v)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
  have hclosed : Closed c s t 1 (solve c nodes s t) := by
    apply scales_closed c nodes complete s t hst (initialScale c) _ (zero_feasible c s t)
      {s} (by simp) (by simpa using Ne.symm hst)
    intro u _ v _
    have hh := (hc u v).trans (Nat.lt_log2_self (n := capacitySum c)).le
    change (c u v : ℤ) - 0 ≤ ((2 ^ ((capacitySum c).log2 + 1) : ℕ) : ℤ)
    simp only [sub_zero]
    exact_mod_cast hh
  have hm := minimum_cut_of_residual_zero c s t _ hclosed.1 _ hclosed.2.1 hclosed.2.2.1
    (fun u hu v hv => by
      have hlow := residual_nonnegative c s t _ hclosed.1 u v
      have hhigh := hclosed.2.2.2 u hu v (Finset.mem_compl.mp hv)
      omega)
  exact ⟨hclosed.1, hclosed.2.1, hclosed.2.2.1, hm.1, hm.2⟩

/-- The executable solver's counters depend on capacity bit length, never on
the magnitude itself. -/
theorem solve_counts (c : V → V → ℕ) (nodes : List V) (s t : V) :
    (solve c nodes s t).searches ≤ ((capacitySum c).log2 + 1) *
      (2 * Fintype.card V ^ 2 + 2) ∧
    (solve c nodes s t).augmentations ≤ ((capacitySum c).log2 + 1) *
      (2 * Fintype.card V ^ 2 + 1) := by
  simpa only [solve, initialScale, phaseFuel, Nat.add_assoc] using
    scales_counts c nodes s t (initialScale c) (fun _ _ => 0)

/-- Every feasible flow entry fits in the signed range determined by the input
capacity sum. This applies to every intermediate augmentation. -/
theorem feasible_entry_bound (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (u v : V) : |f u v| ≤ (capacitySum c : ℤ) := by
  have hc (a b : V) : c a b ≤ capacitySum c := by
    unfold capacitySum
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, c a b)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))
  have hupper := hf.2.1 u v
  have hlower := hf.2.1 v u
  rw [hf.1 v u] at hlower
  have hu : (c u v : ℤ) ≤ capacitySum c := by exact_mod_cast hc u v
  have hv : (c v u : ℤ) ≤ capacitySum c := by exact_mod_cast hc v u
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- Residual values require at most one additional capacity bit. -/
theorem feasible_residual_bound (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (u v : V) :
    0 ≤ residual c f u v ∧ residual c f u v ≤ 2 * (capacitySum c : ℤ) := by
  refine ⟨residual_nonnegative c s t f hf u v, ?_⟩
  have hab := feasible_entry_bound c s t f hf u v
  have hc : c u v ≤ capacitySum c := by
    unfold capacitySum
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, c a b)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ u))
  have hc' : (c u v : ℤ) ≤ capacitySum c := by exact_mod_cast hc
  have hlo := (abs_le.mp hab).1
  unfold MaxFlowCore.residual
  omega

end WeightedMIS.MaxFlowScaling
