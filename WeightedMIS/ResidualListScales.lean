module

public import WeightedMIS.ResidualListPhase
public import WeightedMIS.RegisterHalve

/-! # Descending binary scales for materialized residual matrices -/

@[expose] public section

namespace WeightedMIS.ResidualListScales

open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords

/-- The shape traversal performs a fixed number of halvings, carrying the
last closed cut to the return branch. -/
def scales {n b : ℕ} (nodes : List (Bits n)) (source sink : Bits n) (attempts : ℕ) :
    ℕ → Bits b → List (Arc n b) → List (Bits n) → ResidualListPhase.Result n b
  | 0, _, table, seen => ⟨table, seen⟩
  | rounds + 1, delta, table, _ =>
    let r := ResidualListPhase.phase delta nodes source sink attempts table
    scales nodes source sink attempts rounds (RegisterHalve.halve delta) r.table r.seen

theorem scales_table_length {n b : ℕ} (nodes : List (Bits n)) (source sink : Bits n)
    (attempts rounds : ℕ) (d : Bits b) (table : List (Arc n b)) (seen : List (Bits n)) :
    (scales nodes source sink attempts rounds d table seen).table.length = table.length := by
  induction rounds generalizing d table seen with
  | zero => rfl
  | succ rounds ih =>
    simp only [scales]
    rw [ih, ResidualListPhase.phase_table_length]

def solve {n b : ℕ} (nodes : List (Bits n)) (source sink : Bits n) (attempts : ℕ)
    (table : List (Arc n b)) : ResidualListPhase.Result n b :=
  scales nodes source sink attempts b (RegisterHalve.powerTop b) table []

end WeightedMIS.ResidualListScales
