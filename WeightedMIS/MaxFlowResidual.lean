module

public import WeightedMIS.MaxFlowScaling

/-!
# Nonnegative residual matrices for the finite register implementation

A feasible skew flow is stored by its nonnegative residual capacities. Updating
these natural entries by subtraction and addition agrees exactly with the
integer augmentation already proved correct.
-/

@[expose] public section

namespace WeightedMIS.MaxFlowResidual

open WeightedMIS.MaxFlowCore

variable {V : Type*} [Fintype V] [DecidableEq V]

def matrix (c : V → V → ℕ) (f : V → V → ℤ) (u v : V) : ℕ :=
  (residual c f u v).toNat

def decode (c : V → V → ℕ) (r : V → V → ℕ) (u v : V) : ℤ :=
  (c u v : ℤ) - r u v

theorem matrix_cast (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (u v : V) :
    (matrix c f u v : ℤ) = residual c f u v :=
  Int.toNat_of_nonneg (residual_nonnegative c s t f hf u v)

theorem decode_matrix (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) : decode c (matrix c f) = f := by
  funext u v
  rw [decode, matrix_cast c s t f hf, MaxFlowCore.residual]
  ring

theorem matrix_relation (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (d : ℕ) (u v : V) :
    d ≤ matrix c f u v ↔ MaxFlowScaling.relation c f d u v := by
  change d ≤ matrix c f u v ↔ (d : ℤ) ≤ residual c f u v
  rw [← matrix_cast c s t f hf u v]
  exact Int.ofNat_le.symm

/-- Residual entries are bounded by the two directed capacities. -/
theorem matrix_le (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (u v : V) : matrix c f u v ≤ c u v + c v u := by
  have lower := hf.2.1 v u
  have skew := hf.1 u v
  have hz := matrix_cast c s t f hf u v
  unfold MaxFlowCore.residual at hz
  have hb : (matrix c f u v : ℤ) ≤ (c u v : ℤ) + c v u := by omega
  exact_mod_cast hb

/-- Each subtraction is executed before the reverse-arc addition. -/
def update (r : V → V → ℕ) (path : List (V × V)) (d : ℕ) (u v : V) : ℕ :=
  r u v - d * path.count (u, v) + d * path.count (v, u)

theorem decrease_le (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (path : List (V × V)) (hn : path.Nodup)
    (d : ℕ) (hd : ∀ a ∈ path, (d : ℤ) ≤ residual c f a.1 a.2) (u v : V) :
    d * path.count (u, v) ≤ matrix c f u v := by
  by_cases hm : (u, v) ∈ path
  · have hc : path.count (u, v) = 1 := by
      have hlo := List.count_pos_iff.mpr hm
      have hhi := List.nodup_iff_count_le_one.mp hn (u, v)
      omega
    rw [hc, Nat.mul_one]
    exact (matrix_relation c s t f hf d u v).mpr (hd (u, v) hm)
  · simp [List.count_eq_zero.mpr hm]

/-- Natural subtraction is exact, and the stored residual table refines the
actual integer-flow augmentation pointwise. -/
theorem update_matrix (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (path : List (V × V))
    (hw : ShortestPath.IsWalk Prod.fst Prod.snd s t path) (hn : path.Nodup)
    (d : ℕ) (hd : ∀ a ∈ path, (d : ℤ) ≤ residual c f a.1 a.2) :
    update (matrix c f) path d = matrix c (augment f path d) := by
  have hnew := augment_feasible c s t f hf path hw hn d hd
  funext u v
  have hle := decrease_le c s t f hf path hn d hd u v
  apply Int.ofNat_inj.mp
  rw [update, Nat.cast_add, Nat.cast_sub hle, Nat.cast_mul, Nat.cast_mul,
    matrix_cast c s t f hf, matrix_cast c s t _ hnew]
  unfold MaxFlowCore.residual augment pathFlow
  push_cast
  ring

theorem update_le (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : Feasible c s t f) (path : List (V × V))
    (hw : ShortestPath.IsWalk Prod.fst Prod.snd s t path) (hn : path.Nodup)
    (d : ℕ) (hd : ∀ a ∈ path, (d : ℤ) ≤ residual c f a.1 a.2) (u v : V) :
    update (matrix c f) path d u v ≤ c u v + c v u := by
  rw [update_matrix c s t f hf path hw hn d hd]
  exact matrix_le c s t _ (augment_feasible c s t f hf path hw hn d hd) u v

end WeightedMIS.MaxFlowResidual
