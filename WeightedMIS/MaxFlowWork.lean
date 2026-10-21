module

public import WeightedMIS.MaxFlowCached
public import WeightedMIS.MaxFlowSize

/-!
# Concrete scan counts for the materialized maximum-flow program

These counters follow the same branches as the cached program. They count
predicate evaluations of its residual search and equality tests of table
updates. Integer magnitudes and input exponents are bounded in MaxFlowSize.
-/

@[expose] public section

namespace WeightedMIS.MaxFlowWork

open MaxFlowCore MaxFlowCached

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual predicate scans made by one residual search. -/
def searchQueries (c : V → V → ℕ) (nodes : List V) (s : V) (d : ℕ) (tab : Table V) : ℕ :=
  MaxFlowReach.exploreQueries (MaxFlowScaling.relation c (get tab) d) nodes
    (Fintype.card V) (MaxFlowReach.initial s)

theorem searchQueries_le (c : V → V → ℕ) (nodes : List V) (s : V) (d : ℕ) (tab : Table V) :
    searchQueries c nodes s d tab ≤ Fintype.card V * nodes.length ^ 2 :=
  MaxFlowReach.exploreQueries_le _ _ _ _

/-- Follow exactly the table phase's branches, counting its residual scans. -/
def phaseQueries (c : V → V → ℕ) (nodes : List V) (s t : V) (d : ℕ) :
    ℕ → Table V → ℕ
  | 0, tab => searchQueries c nodes s d tab
  | fuel + 1, tab =>
      let q := MaxFlowScaling.search c nodes s d (get tab)
      if t ∈ q.seen then
        searchQueries c nodes s d tab + phaseQueries c nodes s t d fuel
          (freeze nodes (augment (get tab) (q.route t) d))
      else searchQueries c nodes s d tab

theorem phaseQueries_le (c : V → V → ℕ) (nodes : List V) (s t : V) (d fuel : ℕ)
    (tab : Table V) : phaseQueries c nodes s t d fuel tab ≤
      (fuel + 1) * (Fintype.card V * nodes.length ^ 2) := by
  induction fuel generalizing tab with
  | zero => simpa [phaseQueries] using searchQueries_le c nodes s d tab
  | succ fuel ih =>
      have hs := searchQueries_le c nodes s d tab
      simp only [phaseQueries]
      split
      · have hr := ih (freeze nodes
          (augment (get tab) ((MaxFlowScaling.search c nodes s d (get tab)).route t) d))
        nlinarith
      · nlinarith

/-- Total predicate scans over the actual sequence of materialized phases. -/
def scalesQueries (c : V → V → ℕ) (nodes : List V) (s t : V) : ℕ → Table V → ℕ
  | 0, tab => phaseQueries c nodes s t 1 (MaxFlowScaling.phaseFuel V) tab
  | k + 1, tab =>
      let r := MaxFlowCached.phase c nodes s t (2 ^ (k + 1)) (MaxFlowScaling.phaseFuel V) tab
      phaseQueries c nodes s t (2 ^ (k + 1)) (MaxFlowScaling.phaseFuel V) tab +
        scalesQueries c nodes s t k r.table

theorem scalesQueries_le (c : V → V → ℕ) (nodes : List V) (s t : V) (k : ℕ)
    (tab : Table V) : scalesQueries c nodes s t k tab ≤
      (k + 1) * (MaxFlowScaling.phaseFuel V + 1) *
        (Fintype.card V * nodes.length ^ 2) := by
  induction k generalizing tab with
  | zero => simpa [scalesQueries] using
      phaseQueries_le c nodes s t 1 (MaxFlowScaling.phaseFuel V) tab
  | succ k ih =>
      have hp := phaseQueries_le c nodes s t (2 ^ (k + 1)) (MaxFlowScaling.phaseFuel V) tab
      have hr := ih (MaxFlowCached.phase c nodes s t (2 ^ (k + 1))
        (MaxFlowScaling.phaseFuel V) tab).table
      simp only [scalesQueries]
      nlinarith

/-- Entry inspections of the materialized augmentation. Each entry reads one
old flow value and scans the path twice to count its two orientations. -/
def updateQueries (nodes : List V) (tab : Table V) (p : List (V × V)) : ℕ :=
  ((nodes.product nodes).map fun a => lookupQueries tab a + 2 * p.length + 1).sum

theorem updateQueries_le (nodes : List V) (tab : Table V) (p : List (V × V)) :
    updateQueries nodes tab p ≤ nodes.length ^ 2 * (tab.length + 2 * p.length + 1) := by
  have hh : ∀ a ∈ nodes.product nodes,
      lookupQueries tab a + 2 * p.length + 1 ≤ tab.length + 2 * p.length + 1 := by
    intro a _
    have h := lookupQueries_le tab a
    omega
  have hs := List.sum_le_length_nsmul
    ((nodes.product nodes).map fun a => lookupQueries tab a + 2 * p.length + 1)
    (tab.length + 2 * p.length + 1) (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact hh a ha)
  change updateQueries nodes tab p ≤ _ at hs
  have hlen : (nodes.product nodes).length = nodes.length ^ 2 :=
    (List.length_product nodes nodes).trans (by ring)
  simpa only [List.length_map, hlen, nsmul_eq_mul, Nat.cast_id] using hs

/-- A valid residual route bounds every materialized update by a polynomial
in the explicit enumeration length and vertex count. -/
theorem updateQueries_simple_le (nodes : List V) (tab : Table V)
    (hlen : tab.length = nodes.length ^ 2) (s : V) (p : List (V × V))
    (hp : ShortestPath.IsSimple Prod.snd s p) :
    updateQueries nodes tab p ≤ nodes.length ^ 2 *
      (nodes.length ^ 2 + 2 * Fintype.card V + 1) := by
  have hl := hp.length_le_card
  have hpl : p.length ≤ Fintype.card V := by
    simp only [ShortestPath.vertices, List.length_cons, List.length_map] at hl
    omega
  have hu := updateQueries_le nodes tab p
  rw [hlen] at hu
  exact hu.trans (Nat.mul_le_mul_left _ (by omega))

/-- Count entry inspections along exactly the executed augmentation branches. -/
def phaseUpdates (c : V → V → ℕ) (nodes : List V) (s t : V) (d : ℕ) :
    ℕ → Table V → ℕ
  | 0, _ => 0
  | fuel + 1, tab =>
      let q := MaxFlowScaling.search c nodes s d (get tab)
      if t ∈ q.seen then
        updateQueries nodes tab (q.route t) + phaseUpdates c nodes s t d fuel
          (freeze nodes (augment (get tab) (q.route t) d))
      else 0

theorem phaseUpdates_le (c : V → V → ℕ) (nodes : List V) (s t : V) (d fuel : ℕ)
    (tab : Table V) (hlen : tab.length = nodes.length ^ 2) :
    phaseUpdates c nodes s t d fuel tab ≤ fuel *
      (nodes.length ^ 2 * (nodes.length ^ 2 + 2 * Fintype.card V + 1)) := by
  induction fuel generalizing tab with
  | zero => simp [phaseUpdates]
  | succ fuel ih =>
      simp only [phaseUpdates]
      split
      · rename_i ht
        have hi := MaxFlowReach.explore_invariant (MaxFlowScaling.relation c (get tab) d)
          nodes s (Fintype.card V) (MaxFlowReach.initial s)
          (MaxFlowReach.initial_invariant _ s)
        have hp := hi.simple t ht
        have hu := updateQueries_simple_le nodes tab hlen s _ hp
        have hr := ih (freeze nodes
          (augment (get tab) ((MaxFlowScaling.search c nodes s d (get tab)).route t) d))
          (freeze_length _ _)
        change updateQueries nodes tab ((MaxFlowScaling.search c nodes s d (get tab)).route t) ≤ _ at hu
        nlinarith
      · omega

/-- All matrix-update inspections over the descending scales. -/
def scalesUpdates (c : V → V → ℕ) (nodes : List V) (s t : V) : ℕ → Table V → ℕ
  | 0, tab => phaseUpdates c nodes s t 1 (MaxFlowScaling.phaseFuel V) tab
  | k + 1, tab =>
      let r := MaxFlowCached.phase c nodes s t (2 ^ (k + 1)) (MaxFlowScaling.phaseFuel V) tab
      phaseUpdates c nodes s t (2 ^ (k + 1)) (MaxFlowScaling.phaseFuel V) tab +
        scalesUpdates c nodes s t k r.table

theorem scalesUpdates_le (c : V → V → ℕ) (nodes : List V) (s t : V) (k : ℕ)
    (tab : Table V) (hlen : tab.length = nodes.length ^ 2) :
    scalesUpdates c nodes s t k tab ≤ (k + 1) * MaxFlowScaling.phaseFuel V *
      (nodes.length ^ 2 * (nodes.length ^ 2 + 2 * Fintype.card V + 1)) := by
  induction k generalizing tab with
  | zero => simpa [scalesUpdates] using
      phaseUpdates_le c nodes s t 1 (MaxFlowScaling.phaseFuel V) tab hlen
  | succ k ih =>
      have hp := phaseUpdates_le c nodes s t (2 ^ (k + 1))
        (MaxFlowScaling.phaseFuel V) tab hlen
      have hr := ih (MaxFlowCached.phase c nodes s t (2 ^ (k + 1))
        (MaxFlowScaling.phaseFuel V) tab).table
        (phase_table_length c nodes s t _ _ tab hlen)
      simp only [scalesUpdates]
      nlinarith

/-- Residual search scans of the whole integer-network solver. -/
def solveQueries (c : V → V → ℕ) (nodes : List V) (s t : V) : ℕ :=
  scalesQueries c nodes s t (MaxFlowScaling.initialScale c) (freeze nodes (fun _ _ => 0))

/-- Matrix-update inspections of the whole integer-network solver. -/
def solveUpdates (c : V → V → ℕ) (nodes : List V) (s t : V) : ℕ :=
  scalesUpdates c nodes s t (MaxFlowScaling.initialScale c) (freeze nodes (fun _ _ => 0))

theorem solveQueries_le (c : V → V → ℕ) (nodes : List V) (s t : V) :
    solveQueries c nodes s t ≤ ((MaxFlowScaling.capacitySum c).log2 + 1) *
      (2 * Fintype.card V ^ 2 + 2) * (Fintype.card V * nodes.length ^ 2) := by
  simpa only [solveQueries, MaxFlowScaling.initialScale, MaxFlowScaling.phaseFuel, Nat.add_assoc] using
    scalesQueries_le c nodes s t (MaxFlowScaling.initialScale c) (freeze nodes (fun _ _ => 0))

theorem solveUpdates_le (c : V → V → ℕ) (nodes : List V) (s t : V) :
    solveUpdates c nodes s t ≤ ((MaxFlowScaling.capacitySum c).log2 + 1) *
      (2 * Fintype.card V ^ 2 + 1) *
      (nodes.length ^ 2 * (nodes.length ^ 2 + 2 * Fintype.card V + 1)) := by
  exact scalesUpdates_le c nodes s t (MaxFlowScaling.initialScale c)
    (freeze nodes (fun _ _ => 0)) (freeze_length _ _)

end WeightedMIS.MaxFlowWork
