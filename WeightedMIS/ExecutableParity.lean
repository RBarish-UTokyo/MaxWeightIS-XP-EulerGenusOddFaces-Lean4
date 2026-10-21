module

public import WeightedMIS.BipartiteRecovery

/-!
# Certifying both outcomes of the actual parity search

A positive reachability result directly yields the computed odd row. Its
identity rules out a two-coloring. The negative outcome is already certified
by the computed coloring, so the test chooses the appropriate solver branch.
-/

@[expose] public section

namespace WeightedMIS.ComputedOddRow

open scoped BigOperators
open GraphSearch MaxFlowReach

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Observed opposite-root reachability certifies the actual computed odd row. -/
theorem oddRow_of_seen (left right : E → V) (edges : List E)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (root : V)
    (hseen : (root, true) ∈ (paritySearch left right edges nodes root).seen) :
    IntegerSlacks.OddRow left right root (oddRow left right edges nodes root) := by
  have hs := search_spec (AdjacentParity left right edges) (parityNodes nodes)
    (parityNodes_complete nodes hnodes) (root, false) (root, true)
  have hp := hs.2.1 hseen
  intro x
  have hr := row_telescopes left right edges _ hp.1 hp.2.2 x
  simpa [oddRow, paritySearch, sign, two_mul] using hr

/-- The positive test result rules out every actual two-coloring. -/
theorem nonbipartite_of_seen (left right : E → V) (edges : List E)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (root : V)
    (hseen : (root, true) ∈ (paritySearch left right edges nodes root).seen) :
    ¬Incidence.Bipartite left right := by
  rintro ⟨color, hc⟩
  let x : V → ℚ := fun v => if color v then 1 else -1
  have he (e : E) : x (left e) + x (right e) = 0 := by
    have hh := hc e
    cases hl : color (left e) <;> cases hr : color (right e) <;> simp_all [x]
  have hh := oddRow_of_seen left right edges nodes hnodes root hseen x
  simp only [he, mul_zero, Finset.sum_const_zero] at hh
  cases hroot : color root <;> norm_num [x, hroot] at hh

end WeightedMIS.ComputedOddRow
