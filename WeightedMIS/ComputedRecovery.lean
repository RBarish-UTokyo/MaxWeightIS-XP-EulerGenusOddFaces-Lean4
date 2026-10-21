module

public import WeightedMIS.GraphSearch
public import WeightedMIS.IntegerSlacks

/-!
# Executable integer-potential recovery

The root value is computed by the odd row and exact integer division by two.
All other values are propagated along the deterministic route table. The
kernel equations are used only in the correctness proof, not to choose an
output vector.
-/

@[expose] public section

namespace WeightedMIS.ComputedRecovery

open scoped BigOperators
open Matrix

variable {V E R S : Type*} [Fintype V] [Fintype E] [DecidableEq V]

def rootValue (π y : E → ℤ) : ℤ := (1 - ∑ e, π e * y e) / 2

/-- Integer division is exact when the slack is realized by an integer vector. -/
theorem rootValue_eq (left right : E → V) (root : V) (π y : E → ℤ)
    (hπ : IntegerSlacks.OddRow left right root π) (z : V → ℤ)
    (hz : ∀ e, z (left e) + z (right e) = 1 - y e) : rootValue π y = z root := by
  have hq := hπ (fun v => (z v : ℚ))
  have he : (∑ e, π e * (z (left e) + z (right e))) = 2 * z root := by
    exact_mod_cast hq
  simp_rw [hz, mul_sub, mul_one] at he
  rw [Finset.sum_sub_distrib, IntegerSlacks.odd_row_sum left right root π hπ] at he
  unfold rootValue
  omega

/-- The actual route table and integer arithmetic determine every vertex value. -/
def recover (left right : E → V) (edges : List E) (nodes : List V)
    (root : V) (π y : E → ℤ) : V → ℤ :=
  let routes := GraphSearch.search left right edges nodes root
  fun v => GraphSearch.propagate left right edges y (routes.route v) (rootValue π y)

/-- The executable recovery equals any realizing vector. -/
theorem recover_eq (left right : E → V) (edges : List E) (hedges : ∀ e, e ∈ edges)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (root : V)
    (hc : Incidence.Connected left right) (π y : E → ℤ)
    (hπ : IntegerSlacks.OddRow left right root π) (z : V → ℤ)
    (hz : ∀ e, z (left e) + z (right e) = 1 - y e) :
    recover left right edges nodes root π y = z := by
  funext v
  have hs := GraphSearch.search_correct left right edges hedges nodes hnodes root hc v
  unfold recover
  rw [rootValue_eq left right root π y hπ z hz]
  exact GraphSearch.propagate_eq left right edges y z hz _ hs.2.1 hs.2.2.2.1

/-- Kernel equations and the odd parity bit certify the actual computed
integer vector, without an existential recovery operation. -/
theorem recover_correct (left right : E → V) (edges : List E) (hedges : ∀ e, e ∈ edges)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (root : V)
    (hc : Incidence.Connected left right)
    (B : Matrix R E ℚ) (W : Matrix S E ℚ)
    (hspan : Submodule.span ℚ (Set.range B ∪ Set.range W) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (π y : E → ℤ) (hπ : IntegerSlacks.OddRow left right root π)
    (hB : B *ᵥ (fun e => (y e : ℚ)) = 0)
    (hW : W *ᵥ (fun e => (y e : ℚ)) = 0)
    (hp : ∃ t : ℤ, ∑ e, π e * y e = 2 * t + 1) :
    ∀ e, recover left right edges nodes root π y (left e) +
      recover left right edges nodes root π y (right e) = 1 - y e := by
  obtain ⟨z, hz⟩ := (IntegerSlacks.integer_slack_criterion left right root hc B W hspan π hπ y).mpr
    ⟨hB, hW, hp⟩
  rw [recover_eq left right edges hedges nodes hnodes root hc π y hπ z hz]
  exact hz

/-- Nonnegative slack produces the actual feasible vector and its independent
threshold set. -/
theorem recover_nonnegative (left right : E → V) (edges : List E) (hedges : ∀ e, e ∈ edges)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (root : V)
    (hc : Incidence.Connected left right)
    (B : Matrix R E ℚ) (W : Matrix S E ℚ)
    (hspan : Submodule.span ℚ (Set.range B ∪ Set.range W) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (π y : E → ℤ) (hπ : IntegerSlacks.OddRow left right root π)
    (hB : B *ᵥ (fun e => (y e : ℚ)) = 0)
    (hW : W *ᵥ (fun e => (y e : ℚ)) = 0)
    (hp : ∃ t : ℤ, ∑ e, π e * y e = 2 * t + 1) (hy : ∀ e, 0 ≤ y e) :
    Slack.Feasible left right (recover left right edges nodes root π y) ∧
      (∀ e, Slack.slack left right (recover left right edges nodes root π y) e = y e) ∧
      Slack.Independent left right (Slack.threshold (recover left right edges nodes root π y)) := by
  have he := recover_correct left right edges hedges nodes hnodes root hc B W hspan π y hπ hB hW hp
  have hf : Slack.Feasible left right (recover left right edges nodes root π y) := by
    intro e
    have hh := he e
    have hn := hy e
    omega
  refine ⟨hf, ?_, Slack.threshold_independent left right _ hf⟩
  intro e
  unfold Slack.slack
  have hh := he e
  omega

end WeightedMIS.ComputedRecovery
