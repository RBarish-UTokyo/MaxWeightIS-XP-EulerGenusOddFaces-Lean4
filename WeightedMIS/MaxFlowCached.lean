module

public import WeightedMIS.MaxFlowScaling

/-!
# Materialized finite-matrix refinement of capacity scaling

Each augmentation is written to a fresh finite table. Lookup therefore scans
only the current n² entries; it never recursively evaluates the history of
past augmentations. Decoding the tables gives exactly the proven flow program.
-/

@[expose] public section

namespace WeightedMIS.MaxFlowCached

open MaxFlowCore

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Table (V : Type*) := List ((V × V) × ℤ)

/-- A concrete sequential lookup in the current finite table. -/
def lookup : Table V → (V × V) → ℤ
  | [], _ => 0
  | (a, z) :: rest, x => if x = a then z else lookup rest x

def get (tab : Table V) (u v : V) : ℤ := lookup tab (u, v)

/-- Evaluate every entry now, storing all n² integer values. -/
def freeze (nodes : List V) (f : V → V → ℤ) : Table V :=
  (nodes.product nodes).map fun p => (p, f p.1 p.2)

theorem lookup_map (pairs : List (V × V)) (f : V → V → ℤ) (x : V × V)
    (hx : x ∈ pairs) : lookup (pairs.map fun p => (p, f p.1 p.2)) x = f x.1 x.2 := by
  induction pairs with
  | nil => simp at hx
  | cons a rest ih =>
      by_cases he : x = a
      · simp [lookup, he]
      · have hr : x ∈ rest := (List.mem_cons.mp hx).resolve_left he
        simpa [lookup, he] using ih hr

theorem get_freeze (nodes : List V) (complete : ∀ v, v ∈ nodes) (f : V → V → ℤ) :
    get (freeze nodes f) = f := by
  funext u v
  exact lookup_map (nodes.product nodes) f (u, v)
    (List.mem_product.mpr ⟨complete u, complete v⟩)

@[simp] theorem freeze_length (nodes : List V) (f : V → V → ℤ) :
    (freeze nodes f).length = nodes.length ^ 2 := by
  rw [freeze, List.length_map]
  exact (List.length_product nodes nodes).trans (by ring)

structure Result (V : Type*) where
  table : Table V
  cut : Finset V
  searches : ℕ
  augmentations : ℕ

def decode (r : Result V) : MaxFlowScaling.Result V :=
  ⟨get r.table, r.cut, r.searches, r.augmentations⟩

/-- The same phase, with each augmented flow fully materialized. -/
def phase (c : V → V → ℕ) (nodes : List V) (s t : V) (d : ℕ) :
    ℕ → Table V → Result V
  | 0, tab => ⟨tab, (MaxFlowScaling.search c nodes s d (get tab)).seen, 1, 0⟩
  | fuel + 1, tab =>
      let q := MaxFlowScaling.search c nodes s d (get tab)
      if t ∈ q.seen then
        let next := freeze nodes (augment (get tab) (q.route t) d)
        let r := phase c nodes s t d fuel next
        { r with searches := r.searches + 1, augmentations := r.augmentations + 1 }
      else ⟨tab, q.seen, 1, 0⟩

/-- The table implementation is an exact refinement, including both counters. -/
theorem phase_refines (c : V → V → ℕ) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (s t : V) (d fuel : ℕ) (tab : Table V) :
    decode (phase c nodes s t d fuel tab) =
      MaxFlowScaling.phase c nodes s t d fuel (get tab) := by
  induction fuel generalizing tab with
  | zero => rfl
  | succ fuel ih =>
      simp only [phase, MaxFlowScaling.phase]
      split
      · have hh := ih (freeze nodes
          (augment (get tab) ((MaxFlowScaling.search c nodes s d (get tab)).route t) d))
        rw [get_freeze nodes complete] at hh
        cases he : phase c nodes s t d fuel
            (freeze nodes (augment (get tab) ((MaxFlowScaling.search c nodes s d (get tab)).route t) d))
        simp only [he, decode] at hh ⊢
        rw [← hh]
      · rfl

/-- Descending scales with a materialized table at each phase boundary. -/
def scales (c : V → V → ℕ) (nodes : List V) (s t : V) : ℕ → Table V → Result V
  | 0, tab => phase c nodes s t 1 (MaxFlowScaling.phaseFuel V) tab
  | k + 1, tab =>
      let r := phase c nodes s t (2 ^ (k + 1)) (MaxFlowScaling.phaseFuel V) tab
      let r' := scales c nodes s t k r.table
      ⟨r'.table, r'.cut, r.searches + r'.searches, r.augmentations + r'.augmentations⟩

theorem scales_refines (c : V → V → ℕ) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (s t : V) (k : ℕ) (tab : Table V) :
    decode (scales c nodes s t k tab) = MaxFlowScaling.scales c nodes s t k (get tab) := by
  induction k generalizing tab with
  | zero => exact phase_refines c nodes complete s t 1 (MaxFlowScaling.phaseFuel V) tab
  | succ k ih =>
      have hp := phase_refines c nodes complete s t (2 ^ (k + 1)) (MaxFlowScaling.phaseFuel V) tab
      have hr := ih (phase c nodes s t (2 ^ (k + 1)) (MaxFlowScaling.phaseFuel V) tab).table
      simp only [scales, MaxFlowScaling.scales]
      rw [← hp]
      simp only [decode]
      rw [← hr]
      rfl

/-- The executable solver with bounded-size stored matrices. -/
def solve (c : V → V → ℕ) (nodes : List V) (s t : V) : Result V :=
  scales c nodes s t (MaxFlowScaling.initialScale c) (freeze nodes (fun _ _ => 0))

theorem solve_refines (c : V → V → ℕ) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (s t : V) : decode (solve c nodes s t) = MaxFlowScaling.solve c nodes s t := by
  unfold solve MaxFlowScaling.solve
  rw [scales_refines c nodes complete, get_freeze nodes complete]

/-- Materialization preserves the fixed table length through every phase. -/
theorem phase_table_length (c : V → V → ℕ) (nodes : List V) (s t : V)
    (d fuel : ℕ) (tab : Table V) (hlen : tab.length = nodes.length ^ 2) :
    (phase c nodes s t d fuel tab).table.length = nodes.length ^ 2 := by
  induction fuel generalizing tab with
  | zero => exact hlen
  | succ fuel ih =>
      simp only [phase]
      split
      · apply ih
        exact freeze_length _ _
      · exact hlen

theorem scales_table_length (c : V → V → ℕ) (nodes : List V) (s t : V)
    (k : ℕ) (tab : Table V) (hlen : tab.length = nodes.length ^ 2) :
    (scales c nodes s t k tab).table.length = nodes.length ^ 2 := by
  induction k generalizing tab with
  | zero => exact phase_table_length c nodes s t 1 (MaxFlowScaling.phaseFuel V) tab hlen
  | succ k ih =>
      exact ih _ (phase_table_length c nodes s t _ _ tab hlen)

theorem solve_table_length (c : V → V → ℕ) (nodes : List V) (s t : V) :
    (solve c nodes s t).table.length = nodes.length ^ 2 :=
  scales_table_length c nodes s t _ _ (freeze_length _ _)

/-- Count the equality tests performed by the actual table lookup. -/
def lookupQueries : Table V → (V × V) → ℕ
  | [], _ => 0
  | (a, _) :: rest, x => if x = a then 1 else lookupQueries rest x + 1

theorem lookupQueries_le (tab : Table V) (x : V × V) :
    lookupQueries tab x ≤ tab.length := by
  induction tab with
  | nil => simp [lookupQueries]
  | cons a rest ih =>
      by_cases he : x = a.1 <;> simp [lookupQueries, he] <;> omega

end WeightedMIS.MaxFlowCached
