module

public import WeightedMIS.ComputedRecovery
public import WeightedMIS.Reduction
public import WeightedMIS.OriginalReduction

/-!
# Deterministic recovery from an actual minimum search path

The finite route-table propagation, integer root division, and threshold
operation recover a maximum set from the actual path labels. Existential
integer realizations are used only to prove that computed output correct.
-/

@[expose] public section

namespace WeightedMIS.ComputedRecovery

open scoped BigOperators
open Matrix Walks Reduction

variable {V E Row Coord : Type*} [Fintype V] [Fintype E] [Fintype Row]
    [DecidableEq V] [DecidableEq E] [DecidableEq Row]

/-- The computed integer vector and its threshold maximize the original
weights whenever the supplied actual search path is minimum. -/
theorem minimum_path_maximum (left right : E → V)
    (edges : List E) (hedges : ∀ e, e ∈ edges)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (root : V)
    (hc : Incidence.Connected left right)
    (C : E → Column Row) (W : E → Coord → ℤ)
    (hspan : Submodule.span ℚ (Set.range (localMatrix C) ∪ Set.range (globalMatrix W)) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (hW : ∀ e r, |W e r| ≤ 2)
    (π : E → ℤ) (hπ : IntegerSlacks.OddRow left right root π)
    (cost : E → ℚ) (hcost : ∀ e, 0 ≤ cost e) (w : V → ℚ)
    (hweights : ∀ v, Slack.vertexWeight left right cost v = w v)
    (path : SearchPath C W π)
    (hmin : ∀ q : SearchPath C W π, path.cost cost ≤ q.cost cost) :
    let I := Slack.threshold (recover left right edges nodes root π
      (fun e => (projection path.labels e : ℤ)))
    Persistence.Independent (EdgeTransport.Adj left right) I ∧
      ∀ J, Persistence.Independent (EdgeTransport.Adj left right) J →
        Persistence.weight w J ≤ Persistence.weight w I := by
  obtain ⟨x, hf, hs, hi, hm, _⟩ := Reduction.minimum_path_recovers left right root hc
    C W hspan hW π hπ cost hcost path hmin
  have hz (e) : x (left e) + x (right e) = 1 - (projection path.labels e : ℤ) := by
    have hh := hs e
    unfold Slack.slack at hh
    omega
  have he := recover_eq left right edges hedges nodes hnodes root hc π _ hπ x hz
  simp only [he]
  refine ⟨(OriginalReduction.independent_iff _).mp hi, ?_⟩
  intro J hJ
  have hh := hm J ((OriginalReduction.independent_iff _).mpr hJ)
  simpa only [Slack.setWeight, hweights, InducedReduction.weight_eq_sum] using hh

end WeightedMIS.ComputedRecovery
