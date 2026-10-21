module

public import WeightedMIS.Expanded
public import WeightedMIS.ShortestPath

/-!
# Minimum-cost witnesses in the expanded graph

The expanded graph's actual finite source/label/target triples instantiate the
directed multigraph shortest-path theorem.  Expanded paths and valid lists of
those arcs are equivalent; the translation preserves exact rational cost.
Reachability therefore implies attainment of a global minimum by a path with
fewer arcs than the number of expanded states.  This is an existence and
recovery theorem, with no claim about the time needed to find the witness.
-/

@[expose] public section

namespace WeightedMIS.SearchOptimum

open WeightedMIS.Walks WeightedMIS.Expanded

variable {Row Edge Coord : Type*} {C : Edge → Column Row}
  {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}

/-- Source of an actual expanded-graph arc. -/
abbrev arcSource (a : GraphArc C W π m) : Node Row Coord m := a.val.1

/-- Target of an actual expanded-graph arc. -/
abbrev arcTarget (a : GraphArc C W π m) : Node Row Coord m := a.val.2.2

/-- An expanded arc carries either an original-edge label or a hub transition. -/
abbrev arcLabel (a : GraphArc C W π m) : Option Edge := a.val.2.1

/-- Original-edge cost, or zero for entering and leaving a hub. -/
def arcCost (cost : Edge → ℚ) (a : GraphArc C W π m) : ℚ :=
  labelValue cost (arcLabel a)

/-- Package a verified expanded step as its source/label/target triple. -/
def packArc {s t : Node Row Coord m} (e : Option Edge) (h : Step C W π m s e t) :
    GraphArc C W π m := ⟨(s, e, t), h⟩

/-- List every expanded arc, including the zero-cost hub arcs. -/
def toArcs {s t : Node Row Coord m} : Path C W π m s t → List (GraphArc C W π m)
  | .nil _ => []
  | .cons e h tail => packArc e h :: toArcs tail

/-- The length of an expanded path counts all arcs, including hub arcs. -/
def pathLength {s t : Node Row Coord m} (p : Path C W π m s t) : ℕ :=
  (toArcs p).length

theorem toArcs_isWalk {s t : Node Row Coord m} (p : Path C W π m s t) :
    ShortestPath.IsWalk arcSource arcTarget s t (toArcs p) := by
  induction p with
  | nil => rfl
  | cons e h tail ih => exact ⟨rfl, ih⟩

/-- Construct an expanded path from a valid list of actual expanded arcs. -/
def ofArcs {s t : Node Row Coord m} (arcs : List (GraphArc C W π m))
    (h : ShortestPath.IsWalk arcSource arcTarget s t arcs) : Path C W π m s t :=
  match arcs with
  | [] => h ▸ Path.nil s
  | a :: tail =>
      Path.cons (arcLabel a)
        (by simpa only [← h.1] using a.property)
        (ofArcs tail h.2)

theorem toArcs_ofArcs {s t : Node Row Coord m} (arcs : List (GraphArc C W π m))
    (h : ShortestPath.IsWalk arcSource arcTarget s t arcs) :
    toArcs (ofArcs arcs h) = arcs := by
  induction arcs generalizing s with
  | nil =>
    change s = t at h
    subst t
    rfl
  | cons a tail ih =>
    obtain ⟨⟨u, e, v⟩, ha⟩ := a
    change u = s ∧ ShortestPath.IsWalk arcSource arcTarget v t tail at h
    obtain ⟨rfl, ht⟩ := h
    simp only [ofArcs, toArcs]
    congr 1
    exact ih ht

theorem ofArcs_toArcs {s t : Node Row Coord m} (p : Path C W π m s t) :
    ofArcs (toArcs p) (toArcs_isWalk p) = p := by
  induction p with
  | nil => rfl
  | cons e h tail ih =>
    change Path.cons e h (ofArcs (toArcs tail) (toArcs_isWalk tail)) = Path.cons e h tail
    rw [ih]

/-- The two directed-path representations are in bijection, without changing
their endpoints or dropping hub arcs. -/
def pathEquiv (s t : Node Row Coord m) :
    Path C W π m s t ≃
      {arcs : List (GraphArc C W π m) // ShortestPath.IsWalk arcSource arcTarget s t arcs} where
  toFun p := ⟨toArcs p, toArcs_isWalk p⟩
  invFun a := ofArcs a.val a.property
  left_inv := ofArcs_toArcs
  right_inv a := Subtype.ext (toArcs_ofArcs a.val a.property)

theorem toArcs_cost {s t : Node Row Coord m} (p : Path C W π m s t) (cost : Edge → ℚ) :
    ShortestPath.pathCost (arcCost cost) (toArcs p) = p.cost cost := by
  induction p with
  | nil => rfl
  | cons e h tail ih =>
    cases e <;> simpa [toArcs, packArc, arcCost, arcLabel, labelValue,
      ShortestPath.pathCost, Path.cost, Path.labels] using ih

theorem ofArcs_cost {s t : Node Row Coord m} (arcs : List (GraphArc C W π m))
    (h : ShortestPath.IsWalk arcSource arcTarget s t arcs) (cost : Edge → ℚ) :
    (ofArcs arcs h).cost cost = ShortestPath.pathCost (arcCost cost) arcs := by
  rw [← toArcs_cost, toArcs_ofArcs]

theorem arcCost_nonnegative (cost : Edge → ℚ) (hcost : ∀ e, 0 ≤ cost e)
    (a : GraphArc C W π m) : 0 ≤ arcCost cost a := by
  unfold arcCost
  cases arcLabel a with
  | none => exact le_rfl
  | some e => exact hcost e

/-- Original-edge labels occupy at most the total number of expanded arcs. -/
theorem labels_length_le {s t : Node Row Coord m} (p : Path C W π m s t) :
    p.labels.length ≤ pathLength p := by
  induction p with
  | nil => exact le_rfl
  | cons e h tail ih =>
    cases e <;> simp_all [Path.labels, pathLength, toArcs]
    omega

/-- Every reachable pair of expanded states admits a true global cost minimizer
whose total arc count is strictly below the number of expanded states. -/
theorem exists_minimum_path [Fintype Row] [Fintype Edge] [Fintype Coord]
    (cost : Edge → ℚ) (hcost : ∀ e, 0 ≤ cost e) {s t : Node Row Coord m}
    (hreachable : Nonempty (Path C W π m s t)) :
    ∃ p : Path C W π m s t,
      pathLength p < Fintype.card (Node Row Coord m) ∧
      ShortestPath.IsSimple arcTarget s (toArcs p) ∧
      ∀ q : Path C W π m s t, p.cost cost ≤ q.cost cost := by
  obtain ⟨witness⟩ := hreachable
  obtain ⟨arcs, hwalk, hsimple, hlength, hmin⟩ :=
    ShortestPath.exists_minimum_cost_path arcSource arcTarget (arcCost cost)
      (arcCost_nonnegative cost hcost) s t ⟨toArcs witness, toArcs_isWalk witness⟩
  refine ⟨ofArcs arcs hwalk, ?_, ?_, ?_⟩
  · simpa [pathLength, toArcs_ofArcs] using hlength
  · simpa [toArcs_ofArcs] using hsimple
  · intro q
    rw [ofArcs_cost, ← toArcs_cost]
    exact hmin (toArcs q) (toArcs_isWalk q)

/-- The manuscript's expanded graph has a minimum path with the explicit
state-count bound `2(4m+1)^d(1+(2r+1)^2)` whenever its target is reachable. -/
theorem exists_minimum_source_target [Fintype Row] [Fintype Edge] [Fintype Coord]
    (cost : Edge → ℚ) (hcost : ∀ e, 0 ≤ cost e)
    (hreachable : Nonempty (Path C W π m (start m) (finish m))) :
    ∃ p : Path C W π m (start m) (finish m),
      pathLength p <
        2 * (4 * m + 1) ^ Fintype.card Coord * (1 + (2 * Fintype.card Row + 1) ^ 2) ∧
      ∀ q : Path C W π m (start m) (finish m), p.cost cost ≤ q.cost cost := by
  obtain ⟨p, hlength, _, hmin⟩ := exists_minimum_path cost hcost hreachable
  exact ⟨p, by simpa only [node_card] using hlength, hmin⟩

end WeightedMIS.SearchOptimum
