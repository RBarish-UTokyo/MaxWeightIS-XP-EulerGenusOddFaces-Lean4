module

public import WeightedMIS.DoubleCover

/-!
# The explicit capacitated network for half-integral preprocessing

The network has two terminals and two copies of the vertex set. Arcs go from
the source to the first copy, across the two copies, and from the second copy
to the sink. Nonadjacent internal arcs have capacity zero.
-/

@[expose] public section

namespace WeightedMIS.DoubleCoverNetwork

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two terminals and two copies of the vertex set. -/
abbrev Node (V : Type*) := Bool ⊕ (Bool × V)

/-- Terminal and internal arcs; zero-capacity internal arcs are retained. -/
abbrev Arc (V : Type*) := V ⊕ ((V × V) ⊕ V)

def sourceNode : Node V := Sum.inl false
def sinkNode : Node V := Sum.inl true

def source : Arc V → Node V
  | .inl _ => sourceNode
  | .inr (.inl p) => .inr (false, p.1)
  | .inr (.inr v) => .inr (true, v)

def target : Arc V → Node V
  | .inl v => .inr (false, v)
  | .inr (.inl p) => .inr (true, p.2)
  | .inr (.inr _) => sinkNode

def capacity (adj : V → V → Prop) [DecidableRel adj] (w : V → ℚ) : Arc V → ℚ
  | .inl v => w v
  | .inr (.inl p) => if adj p.1 p.2 then DoubleCover.largeCapacity w else 0
  | .inr (.inr v) => w v

/-- A source side contains the source and excludes the sink. -/
def IsCut (X : Node V → Bool) : Prop := X sourceNode = true ∧ X sinkNode = false

/-- Sum the capacities of all arcs leaving the specified source side. -/
def cutValue (adj : V → V → Prop) [DecidableRel adj] (w : V → ℚ)
    (X : Node V → Bool) : ℚ :=
  ∑ a, if X (source a) = true ∧ X (target a) = false then capacity adj w a else 0

/-- Every cut is parametrized by its left vertices outside and right vertices inside. -/
def side (A B : Finset V) : Node V → Bool
  | .inl b => !b
  | .inr (false, v) => decide (v ∉ A)
  | .inr (true, v) => decide (v ∈ B)

theorem side_isCut (A B : Finset V) : IsCut (side A B) := by
  simp [IsCut, side, sourceNode, sinkNode]

theorem capacity_nonnegative (adj : V → V → Prop) [DecidableRel adj]
    (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) (a : Arc V) : 0 ≤ capacity adj w a := by
  have ht : 0 ≤ DoubleCover.largeCapacity w := by
    unfold DoubleCover.largeCapacity
    exact add_nonneg (by norm_num) (Finset.sum_nonneg fun v _ => hw v)
  rcases a with v | (p | v)
  · exact hw v
  · dsimp [capacity]
    split_ifs <;> positivity
  · exact hw v

/-- The standard cut sum equals the explicit terminal-plus-internal formula. -/
theorem cutValue_side (adj : V → V → Prop) [DecidableRel adj] (w : V → ℚ)
    (A B : Finset V) :
    cutValue adj w (side A B) = DoubleCover.cutCapacity adj w A B := by
  simp only [cutValue, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [source, target, sourceNode, sinkNode, side, capacity,
    Bool.not_false, Bool.not_true, Bool.true_eq, Bool.false_eq, true_and, and_true,
    decide_eq_true_eq, decide_eq_false_iff_not, not_not]
  unfold DoubleCover.cutCapacity DoubleCover.coverCost DoubleCover.violations
  simp only [Persistence.objective, Persistence.indicator, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  have hi (u v : V) :
      (if u ∉ A ∧ v ∉ B then if adj u v then DoubleCover.largeCapacity w else 0 else 0) =
      (if adj u v ∧ u ∉ A ∧ v ∉ B then DoubleCover.largeCapacity w else 0) := by
    by_cases ha : adj u v <;> by_cases hu : u ∈ A <;> by_cases hv : v ∈ B <;>
      simp [ha, hu, hv]
  simp_rw [hi]
  ring

/-- Recover the pair of vertex sets from an arbitrary source side. -/
def leftCover (X : Node V → Bool) : Finset V :=
  Finset.univ.filter fun v => X (.inr (false, v)) = false

def rightCover (X : Node V → Bool) : Finset V :=
  Finset.univ.filter fun v => X (.inr (true, v)) = true

theorem side_recovery (X : Node V → Bool) (hX : IsCut X) :
    side (leftCover X) (rightCover X) = X := by
  funext n
  rcases n with b | ⟨b, v⟩
  · cases b
    · exact hX.1.symm
    · exact hX.2.symm
  · cases b <;> simp [side, leftCover, rightCover]

/-- A genuine minimum source-to-sink cut gives a half-integral LP optimum. -/
theorem optimal_of_minimum_network_cut (adj : V → V → Prop) [DecidableRel adj]
    (hsym : Symmetric adj) (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (X : Node V → Bool) (hX : IsCut X)
    (hmin : ∀ Y, IsCut Y → cutValue adj w X ≤ cutValue adj w Y) :
    Persistence.HalfIntegral (DoubleCover.rounded (leftCover X) (rightCover X)) ∧
    Persistence.Optimal adj w (DoubleCover.rounded (leftCover X) (rightCover X)) := by
  apply DoubleCover.optimal_of_minimum_cut adj hsym w hw
  intro C D
  have hh := hmin (side C D) (side_isCut C D)
  rw [← side_recovery X hX, cutValue_side, cutValue_side] at hh
  exact hh

end WeightedMIS.DoubleCoverNetwork
