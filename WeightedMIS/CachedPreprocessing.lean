module

public import WeightedMIS.MaxFlowCached
public import WeightedMIS.MaxFlowDual

/-!
# Materialized preprocessing and dual extraction

These executable entry points evaluate the finite-table maximum-flow solver
once, then recover either the half-integral vector or the rational transport
from its stored cut and matrix.
-/

@[expose] public section

namespace WeightedMIS.CachedPreprocessing

open scoped BigOperators
open DoubleCoverNetwork MaxFlowPreprocessing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Materialized integer-network result. -/
def networkResult (adj : V → V → Prop) [DecidableRel adj] (nodes : List V) (w : V → ℚ) :
    MaxFlowCached.Result (Node V) :=
  MaxFlowCached.solve (matrix adj (scaledWeight w)) (networkNodes nodes) sourceNode sinkNode

theorem networkResult_refines (adj : V → V → Prop) [DecidableRel adj]
    (nodes : List V) (complete : ∀ v, v ∈ nodes) (w : V → ℚ) :
    MaxFlowCached.decode (networkResult adj nodes w) =
      MaxFlowPreprocessing.networkResult adj nodes w :=
  MaxFlowCached.solve_refines _ _ (networkNodes_complete nodes complete) _ _

/-- Compute the cut once and return the recovered half-integral point. -/
def lpPoint (adj : V → V → Prop) [DecidableRel adj] (nodes : List V) (w : V → ℚ) : V → ℚ :=
  let r := networkResult adj nodes w
  let X := membership r.cut
  DoubleCover.rounded (leftCover X) (rightCover X)

theorem lpPoint_eq (adj : V → V → Prop) [DecidableRel adj]
    (nodes : List V) (complete : ∀ v, v ∈ nodes) (w : V → ℚ) :
    lpPoint adj nodes w = MaxFlowPreprocessing.lpPoint adj nodes w := by
  have hh := congrArg MaxFlowScaling.Result.cut (networkResult_refines adj nodes complete w)
  change (networkResult adj nodes w).cut = (MaxFlowPreprocessing.networkResult adj nodes w).cut at hh
  simp only [lpPoint, MaxFlowPreprocessing.lpPoint, hh]

theorem lpPoint_correct (adj : V → V → Prop) [DecidableRel adj]
    (hsym : Symmetric adj) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) :
    Persistence.HalfIntegral (lpPoint adj nodes w) ∧
      Persistence.Optimal adj w (lpPoint adj nodes w) := by
  rw [lpPoint_eq adj nodes complete w]
  exact MaxFlowPreprocessing.lpPoint_correct adj hsym nodes complete w hw

/-- Compute and retain the flow table before reading its internal entries. -/
def rationalTransport (adj : V → V → Prop) [DecidableRel adj]
    (nodes : List V) (w : V → ℚ) : V → V → ℚ :=
  let tab := (networkResult adj nodes w).table
  fun u v => ((MaxFlowCached.get tab (MaxFlowDual.leftNode u) (MaxFlowDual.rightNode v) : ℤ) : ℚ) /
    denominator w

theorem rationalTransport_eq (adj : V → V → Prop) [DecidableRel adj]
    (nodes : List V) (complete : ∀ v, v ∈ nodes) (w : V → ℚ) :
    rationalTransport adj nodes w = MaxFlowDual.rationalTransport adj nodes w := by
  have hh := congrArg MaxFlowScaling.Result.flow (networkResult_refines adj nodes complete w)
  change MaxFlowCached.get (networkResult adj nodes w).table =
    (MaxFlowPreprocessing.networkResult adj nodes w).flow at hh
  funext u v
  simp only [rationalTransport, MaxFlowDual.rationalTransport, hh]

theorem rationalTransport_correct (adj : V → V → Prop) [DecidableRel adj]
    (hsym : Symmetric adj) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal adj w (fun _ => 1 / 2)) :
    (∀ u v, 0 ≤ rationalTransport adj nodes w u v) ∧
      (∀ u v, ¬ adj u v → rationalTransport adj nodes w u v = 0) ∧
      (∀ u, (∑ v, rationalTransport adj nodes w u v) = w u) ∧
      (∀ v, (∑ u, rationalTransport adj nodes w u v) = w v) := by
  rw [rationalTransport_eq adj nodes complete w]
  exact MaxFlowDual.rationalTransport_correct adj hsym nodes complete w hw ho

end WeightedMIS.CachedPreprocessing
