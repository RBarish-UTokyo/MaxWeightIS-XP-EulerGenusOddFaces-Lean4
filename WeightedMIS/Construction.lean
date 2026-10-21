module

public import WeightedMIS.Decomposition
public import WeightedMIS.Lift

/-!
# Binary flow witnesses occur in the finite search graph

This combines the proved signed-walk decomposition and the proved bounded lift.
The resulting path has precisely the input flow's edge multiplicities and cost.
No decomposition oracle or path-existence assumption is used.
-/

@[expose] public section

namespace WeightedMIS.Construction

open WeightedMIS.Walks WeightedMIS.Expanded WeightedMIS.Decomposition WeightedMIS.Lift

/-- Every nonnegative integral local flow using at most m edge copies, with
zero W-signature and odd parity, is realized by a path in the radius-2m graph. -/
theorem bounded_flow_has_path {Row Edge Coord : Type*}
    [Fintype Row] [DecidableEq Row] [Fintype Edge] [DecidableEq Edge]
    (C : Edge → Column Row) (W : Edge → Coord → ℤ) (π : Edge → ZMod 2)
    (m : ℕ) (y : Edge → ℕ) (hW : ∀ e r, |W e r| ≤ 2)
    (hmass : (∑ e, y e) ≤ m)
    (hB : ∀ r, (∑ e, columnVector (C e) r * (y e : ℤ)) = 0)
    (hSig : ∀ r, (∑ e, W e r * (y e : ℤ)) = 0)
    (hParity : (∑ e, π e * (y e : ZMod 2)) = 1) :
    ∃ path : Path C W π m (start m) (finish m),
      ∀ e, projection path.labels e = y e := by
  obtain ⟨ws, hp, _⟩ := decompose_flow C y hB
  have hlen : (ws.flatMap (fun w => w.2.labels)).length ≤ m := by
    rw [← sum_projection_eq_length]
    simp_rw [hp]
    exact hmass
  have hsig : ∀ r, accumulated W (ws.flatMap (fun w => w.2.labels)) r = 0 := by
    intro r
    unfold accumulated
    rw [← sum_mul_projection]
    simp_rw [hp]
    exact hSig r
  have hpar : traceParity π (ws.flatMap (fun w => w.2.labels)) = 1 := by
    unfold traceParity
    rw [← sum_mul_projection]
    simp_rw [hp]
    exact hParity
  obtain ⟨path, hlabels⟩ := source_target_of_closed_walks C W π m hW ws hlen hsig hpar
  exact ⟨path, fun e => by rw [hlabels]; exact hp e⟩

/-- The binary witness required by Lemma 10 always fits the fixed radius-2m
search graph, where m is the number of original edges. -/
theorem binary_flow_has_path {Row Edge Coord : Type*}
    [Fintype Row] [DecidableEq Row] [Fintype Edge] [DecidableEq Edge]
    (C : Edge → Column Row) (W : Edge → Coord → ℤ) (π : Edge → ZMod 2)
    (y : Edge → ℕ) (hW : ∀ e r, |W e r| ≤ 2) (hy : ∀ e, y e ≤ 1)
    (hB : ∀ r, (∑ e, columnVector (C e) r * (y e : ℤ)) = 0)
    (hSig : ∀ r, (∑ e, W e r * (y e : ℤ)) = 0)
    (hParity : (∑ e, π e * (y e : ZMod 2)) = 1) :
    ∃ path : Path C W π (Fintype.card Edge)
        (start (Fintype.card Edge)) (finish (Fintype.card Edge)),
      ∀ e, projection path.labels e = y e := by
  apply bounded_flow_has_path C W π (Fintype.card Edge) y hW ?_ hB hSig hParity
  calc
    (∑ e, y e) ≤ ∑ _ : Edge, 1 := Finset.sum_le_sum (fun e _ => hy e)
    _ = Fintype.card Edge := by simp

/-- Binary witness completeness with the exact rational objective value. -/
theorem binary_flow_has_path_with_cost {Row Edge Coord : Type*}
    [Fintype Row] [DecidableEq Row] [Fintype Edge] [DecidableEq Edge]
    (C : Edge → Column Row) (W : Edge → Coord → ℤ) (π : Edge → ZMod 2)
    (costs : Edge → ℚ) (y : Edge → ℕ)
    (hW : ∀ e r, |W e r| ≤ 2) (hy : ∀ e, y e ≤ 1)
    (hB : ∀ r, (∑ e, columnVector (C e) r * (y e : ℤ)) = 0)
    (hSig : ∀ r, (∑ e, W e r * (y e : ℤ)) = 0)
    (hParity : (∑ e, π e * (y e : ZMod 2)) = 1) :
    ∃ path : Path C W π (Fintype.card Edge)
        (start (Fintype.card Edge)) (finish (Fintype.card Edge)),
      (∀ e, projection path.labels e = y e) ∧ path.cost costs = ∑ e, costs e * (y e : ℚ) := by
  obtain ⟨path, hp⟩ := binary_flow_has_path C W π y hW hy hB hSig hParity
  refine ⟨path, hp, ?_⟩
  rw [Path.cost_projection]
  simp_rw [hp]

end WeightedMIS.Construction
