module

public import WeightedMIS.ResidualListReach
public import WeightedMIS.RegisterResidualTableUpdate

/-! # Capacity-scaling phases on stored binary residual matrices -/

@[expose] public section

namespace WeightedMIS.ResidualListPhase

open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords

structure Result (n b : ℕ) where
  table : List (Arc n b)
  seen : List (Bits n)

def search {n b : ℕ} (table : List (Arc n b)) (d : Bits b) (nodes : List (Bits n))
    (source : Bits n) : ResidualListReach.State n b :=
  ResidualListReach.explore table d nodes.length (ResidualListReach.initial source)

/-- A phase makes a fresh complete residual search before every augmentation.
Its explicit attempt-list will have the proved quadratic number of entries. -/
def phase {n b : ℕ} (d : Bits b) (nodes : List (Bits n)) (source sink : Bits n) :
    ℕ → List (Arc n b) → Result n b
  | 0, table => ⟨table, (search table d nodes source).seen⟩
  | fuel + 1, table =>
    let q := search table d nodes source
    if RegisterMembership.found sink q.seen then
      let path := RegisterRouteLookup.lookup sink q.routes
      let updated := table.map (fun a => RegisterResidualUpdate.update a path d)
      phase d nodes source sink fuel updated
    else ⟨table, q.seen⟩

theorem phase_table_length {n b : ℕ} (d : Bits b) (nodes : List (Bits n))
    (source sink : Bits n) (fuel : ℕ) (table : List (Arc n b)) :
    (phase d nodes source sink fuel table).table.length = table.length := by
  induction fuel generalizing table with
  | zero => rfl
  | succ fuel ih =>
    simp only [phase]
    split
    · rw [ih, List.length_map]
    · rfl

theorem phase_seen_length {n b : ℕ} (d : Bits b) (nodes : List (Bits n))
    (source sink : Bits n) (fuel : ℕ) (table : List (Arc n b)) :
    (phase d nodes source sink fuel table).seen.length ≤ nodes.length + 1 := by
  have hl (table : List (Arc n b)) : (search table d nodes source).seen.length ≤ nodes.length + 1 := by
    have hh := (ResidualListReach.explore_lengths table d nodes.length (ResidualListReach.initial source)).1
    simpa [search, ResidualListReach.initial, Nat.add_comm] using hh
  induction fuel generalizing table with
  | zero => exact hl table
  | succ fuel ih =>
    simp only [phase]
    split
    · exact ih _
    · exact hl table

end WeightedMIS.ResidualListPhase
