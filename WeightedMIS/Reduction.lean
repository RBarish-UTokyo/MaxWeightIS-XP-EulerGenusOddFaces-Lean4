module

public import WeightedMIS.Construction
public import WeightedMIS.IntegerSlacks
public import WeightedMIS.SearchOptimum

/-!
# Correctness of the finite search reduction

For a finite connected nonbipartite endpoint graph, concrete signed columns,
and bounded integer supplementary rows spanning the actual incidence kernel,
minimum paths in the constructed finite graph recover maximum-weight
independent sets. Vertex weights are induced by the specified nonnegative
rational edge costs. No embedding or running-time assertion is made here.
-/

@[expose] public section

namespace WeightedMIS.Reduction

open Matrix WeightedMIS.Walks WeightedMIS.Expanded

variable {V E Row Coord : Type*}

/-- The rational matrix of the actual signed-stub columns. -/
def localMatrix [DecidableEq Row] (C : E → Column Row) : Matrix Row E ℚ :=
  fun r e => (columnVector (C e) r : ℚ)

/-- Supplementary integer column labels, viewed as a rational row matrix. -/
def globalMatrix (W : E → Coord → ℤ) : Matrix Coord E ℚ :=
  fun r e => (W e r : ℚ)

/-- The actual source-to-target paths of the radius-2m search graph, m=|E|. -/
abbrev SearchPath [Fintype E] (C : E → Column Row) (W : E → Coord → ℤ)
    (π : E → ℤ) :=
  Path C W (fun e => (π e : ZMod 2)) (Fintype.card E)
    (start (Fintype.card E)) (finish (Fintype.card E))

private theorem cast_matrix_zero_iff [Fintype E]
    (M : Row → E → ℤ) (y : E → ℤ) :
    (fun r e => (M r e : ℚ)) *ᵥ (fun e => (y e : ℚ)) = 0 ↔
      ∀ r, (∑ e, M r e * y e) = 0 := by
  constructor
  · intro h r
    have hr := congrFun h r
    change (∑ e, (M r e : ℚ) * (y e : ℚ)) = 0 at hr
    exact_mod_cast hr
  · intro h
    ext r
    change (∑ e, (M r e : ℚ) * (y e : ℚ)) = 0
    exact_mod_cast h r

/-- The parity bit is exactly the oddness condition on the integer scalar. -/
theorem parity_iff_odd [Fintype E] (π : E → ℤ) (y : E → ℕ) :
    (∑ e, (π e : ZMod 2) * (y e : ZMod 2)) = 1 ↔
      ∃ t : ℤ, (∑ e, π e * (y e : ℤ)) = 2 * t + 1 := by
  have hc : ((∑ e, π e * (y e : ℤ) : ℤ) : ZMod 2) =
      ∑ e, (π e : ZMod 2) * (y e : ZMod 2) := by push_cast; rfl
  rw [← hc, ZMod.intCast_eq_one_iff_odd]
  rfl

/-- Every independent set supplies a binary witness path with the exact
complementary objective value. The kernel and parity equations are derived
from its characteristic vector. -/
theorem independent_set_has_path
    [Fintype V] [Fintype E] [Fintype Row]
    [DecidableEq V] [DecidableEq E] [DecidableEq Row]
    (left right : E → V) (root : V) (hc : Incidence.Connected left right)
    (C : E → Column Row) (W : E → Coord → ℤ)
    (hspan : Submodule.span ℚ (Set.range (localMatrix C) ∪ Set.range (globalMatrix W)) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (hW : ∀ e r, |W e r| ≤ 2)
    (π : E → ℤ) (hπ : IntegerSlacks.OddRow left right root π)
    (cost : E → ℚ) (I : Finset V) (hI : Slack.Independent left right I) :
    ∃ path : SearchPath C W π,
      (∀ e, (projection path.labels e : ℤ) =
        Slack.slack left right (Slack.indicator I) e) ∧
      path.cost cost = Slack.totalCost cost - Slack.setWeight left right cost I := by
  let y : E → ℕ := fun e => (Slack.slack left right (Slack.indicator I) e).toNat
  have hyint : ∀ e, (y e : ℤ) = Slack.slack left right (Slack.indicator I) e := by
    intro e
    rcases Slack.independent_binary_slack left right I hI e with h | h <;> simp [y, h]
  have hy : ∀ e, y e ≤ 1 := by
    intro e
    rcases Slack.independent_binary_slack left right I hI e with h | h <;> simp [y, h]
  have hint : ∃ z : V → ℤ, ∀ e, z (left e) + z (right e) =
      1 - Slack.slack left right (Slack.indicator I) e := by
    refine ⟨Slack.indicator I, ?_⟩
    intro e
    unfold Slack.slack
    omega
  obtain ⟨hB, hSig, hp⟩ := (IntegerSlacks.integer_slack_criterion left right root hc
    (localMatrix C) (globalMatrix W) hspan π hπ
    (Slack.slack left right (Slack.indicator I))).mp hint
  have hb : ∀ r, (∑ e, columnVector (C e) r * (y e : ℤ)) = 0 := by
    have hb := (cast_matrix_zero_iff (fun r e => columnVector (C e) r)
      (Slack.slack left right (Slack.indicator I))).mp hB
    simpa only [hyint] using hb
  have hs : ∀ r, (∑ e, W e r * (y e : ℤ)) = 0 := by
    have hs := (cast_matrix_zero_iff (fun r e => W e r)
      (Slack.slack left right (Slack.indicator I))).mp hSig
    simpa only [hyint] using hs
  have hp' : (∑ e, (π e : ZMod 2) * (y e : ZMod 2)) = 1 := by
    rw [parity_iff_odd]
    simpa only [hyint] using hp
  obtain ⟨path, hproj, hcost⟩ := Construction.binary_flow_has_path_with_cost
    C W (fun e => (π e : ZMod 2)) cost y hW hy hb hs hp'
  refine ⟨path, fun e => by rw [hproj]; exact hyint e, ?_⟩
  rw [hcost, ← Slack.independent_cost_identity]
  unfold Slack.slackCost
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  exact_mod_cast hyint e

/-- Every actual search path projects to the slack of a feasible integer
vertex vector, with exactly the same rational objective. -/
theorem path_has_integer_slack
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [DecidableEq Row]
    (left right : E → V) (root : V) (hc : Incidence.Connected left right)
    (C : E → Column Row) (W : E → Coord → ℤ)
    (hspan : Submodule.span ℚ (Set.range (localMatrix C) ∪ Set.range (globalMatrix W)) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (π : E → ℤ) (hπ : IntegerSlacks.OddRow left right root π)
    (cost : E → ℚ) (path : SearchPath C W π) :
    ∃ x : V → ℤ, Slack.Feasible left right x ∧
      (∀ e, Slack.slack left right x e = (projection path.labels e : ℤ)) ∧
      Slack.slackCost left right cost x = path.cost cost := by
  let y : E → ℤ := fun e => (projection path.labels e : ℤ)
  have hB : localMatrix C *ᵥ (fun e => (y e : ℚ)) = 0 := by
    apply (cast_matrix_zero_iff (fun r e => columnVector (C e) r) y).mpr
    exact fun r => path.local_soundness r
  have hSig : globalMatrix W *ᵥ (fun e => (y e : ℚ)) = 0 := by
    apply (cast_matrix_zero_iff (fun r e => W e r) y).mpr
    exact fun r => path.signature_soundness r
  have hp : ∃ t : ℤ, (∑ e, π e * y e) = 2 * t + 1 :=
    (parity_iff_odd π (projection path.labels)).mp path.parity_soundness
  obtain ⟨x, hx, hs⟩ := (IntegerSlacks.nonnegative_integer_slack_criterion left right root hc
    (localMatrix C) (globalMatrix W) hspan π hπ y (fun e => Int.natCast_nonneg _)).mpr
    ⟨hB, hSig, hp⟩
  refine ⟨x, hx, hs, ?_⟩
  rw [Path.cost_projection]
  unfold Slack.slackCost
  apply Finset.sum_congr rfl
  intro e _
  rw [hs]
  simp [y]

/-- Any actual global minimum path recovers a maximum-weight independent set
by thresholding its integral vertex realization. Its cost is exactly the
complement of the recovered optimum weight. -/
theorem minimum_path_recovers
    [Fintype V] [Fintype E] [Fintype Row]
    [DecidableEq V] [DecidableEq E] [DecidableEq Row]
    (left right : E → V) (root : V) (hc : Incidence.Connected left right)
    (C : E → Column Row) (W : E → Coord → ℤ)
    (hspan : Submodule.span ℚ (Set.range (localMatrix C) ∪ Set.range (globalMatrix W)) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (hW : ∀ e r, |W e r| ≤ 2)
    (π : E → ℤ) (hπ : IntegerSlacks.OddRow left right root π)
    (cost : E → ℚ) (hcost : ∀ e, 0 ≤ cost e)
    (path : SearchPath C W π)
    (hmin : ∀ q : SearchPath C W π, path.cost cost ≤ q.cost cost) :
    ∃ x : V → ℤ, Slack.Feasible left right x ∧
      (∀ e, Slack.slack left right x e = (projection path.labels e : ℤ)) ∧
      Slack.Independent left right (Slack.threshold x) ∧
      (∀ J : Finset V, Slack.Independent left right J →
        Slack.setWeight left right cost J ≤ Slack.setWeight left right cost (Slack.threshold x)) ∧
      Slack.setWeight left right cost (Slack.threshold x) =
        Slack.totalCost cost - path.cost cost := by
  obtain ⟨x, hx, hs, hxCost⟩ := path_has_integer_slack left right root hc C W hspan π hπ cost path
  have hI := Slack.threshold_independent left right x hx
  have hround := Slack.threshold_weight_domination left right cost hcost x hx
  rw [hxCost] at hround
  refine ⟨x, hx, hs, hI, ?_, ?_⟩
  · intro J hJ
    obtain ⟨q, _, hq⟩ := independent_set_has_path left right root hc C W hspan hW π hπ cost J hJ
    have hm := hmin q
    rw [hq] at hm
    linarith
  · obtain ⟨q, _, hq⟩ := independent_set_has_path left right root hc C W hspan hW π hπ
      cost (Slack.threshold x) hI
    have hm := hmin q
    rw [hq] at hm
    linarith

/-- Correctness and attainment of the reduced finite-search problem.

All input hypotheses concern the given graph, concrete matrices, and costs.
The parity row, source-to-target reachability, minimum path, integral recovery,
and optimal independent set are derived. The matrix spanning hypothesis is
explicit; establishing it with the required row count from a surface embedding
is a separate theorem. This result makes no complexity claim.
-/
theorem exists_optimal_search_recovery
    [Fintype V] [Fintype E] [Fintype Row] [Fintype Coord]
    [DecidableEq V] [DecidableEq E] [DecidableEq Row]
    (left right : E → V) (hc : Incidence.Connected left right)
    (hnb : ¬ Incidence.Bipartite left right)
    (C : E → Column Row) (W : E → Coord → ℤ)
    (hspan : Submodule.span ℚ (Set.range (localMatrix C) ∪ Set.range (globalMatrix W)) =
      LinearMap.ker (Incidence.unsigned left right)ᵀ.mulVecLin)
    (hW : ∀ e r, |W e r| ≤ 2)
    (cost : E → ℚ) (hcost : ∀ e, 0 ≤ cost e) :
    ∃ root : V, ∃ π : E → ℤ, IntegerSlacks.OddRow left right root π ∧
      ∃ path : SearchPath C W π,
        SearchOptimum.pathLength path <
          2 * (4 * Fintype.card E + 1) ^ Fintype.card Coord *
            (1 + (2 * Fintype.card Row + 1) ^ 2) ∧
        (∀ q : SearchPath C W π, path.cost cost ≤ q.cost cost) ∧
        ∃ x : V → ℤ, Slack.Feasible left right x ∧
          (∀ e, Slack.slack left right x e = (projection path.labels e : ℤ)) ∧
          Slack.Independent left right (Slack.threshold x) ∧
          (∀ J : Finset V, Slack.Independent left right J →
            Slack.setWeight left right cost J ≤
              Slack.setWeight left right cost (Slack.threshold x)) ∧
          Slack.setWeight left right cost (Slack.threshold x) =
            Slack.totalCost cost - path.cost cost := by
  obtain ⟨root, π, _, hπ⟩ := OddRow.exists_odd_row_of_nonbipartite left right hc hnb
  have hempty : Slack.Independent left right (∅ : Finset V) := by
    intro e
    simp
  obtain ⟨witness, _, _⟩ := independent_set_has_path left right root hc C W hspan hW π hπ
    cost ∅ hempty
  obtain ⟨path, hlen, hmin⟩ := SearchOptimum.exists_minimum_source_target
    (C := C) (W := W) (π := fun e => (π e : ZMod 2)) (m := Fintype.card E)
    cost hcost ⟨witness⟩
  obtain ⟨x, hx, hs, hI, hmax, heq⟩ := minimum_path_recovers left right root hc C W hspan hW
    π hπ cost hcost path hmin
  exact ⟨root, π, hπ, path, hlen, hmin, x, hx, hs, hI, hmax, heq⟩

end WeightedMIS.Reduction
