module

public import WeightedMIS.Walks

/-!
# Soundness of the finite expanded graph

This file implements the finite signature box and the hub/working states from
Section 6. It proves that every source-to-target walk gives a nonnegative
integral local flow with zero global signature and odd parity, at exactly the
projected edge cost. It does not assert existence of a source-to-target walk,
a shortest-path algorithm, or the converse flow decomposition.
-/

@[expose] public section

namespace WeightedMIS.Expanded

open WeightedMIS.Walks

/-- Coordinates in the finite box are represented by integers shifted by 2m. -/
abbrev Box (Coord : Type*) (m : ℕ) := Coord → Fin (4 * m + 1)

/-- Decode a finite coordinate as an integer in [-2m,2m]. -/
def coordinate {Coord : Type*} {m : ℕ} (z : Box Coord m) (r : Coord) : ℤ :=
  ((z r).val : ℤ) - 2 * (m : ℤ)

/-- The origin of the signature box. -/
def zeroBox (Coord : Type*) (m : ℕ) : Box Coord m :=
  fun _ => ⟨2 * m, by omega⟩

@[simp] theorem coordinate_zeroBox {Coord : Type*} {m : ℕ} (r : Coord) :
    coordinate (zeroBox Coord m) r = 0 := by
  simp [coordinate, zeroBox]

/-- The finite coordinate encoding has exactly the required range. -/
theorem coordinate_bound {Coord : Type*} {m : ℕ} (z : Box Coord m) (r : Coord) :
    |coordinate z r| ≤ 2 * (m : ℤ) := by
  have h := (z r).isLt
  rw [abs_le]
  dsimp [coordinate]
  constructor <;> omega

/-- A hub or a working state, with its anchor, current signed state, signature,
and one parity bit. -/
inductive Node (Row Coord : Type*) (m : ℕ) where
  | hub (z : Box Coord m) (p : ZMod 2) : Node Row Coord m
  | work (anchor current : State Row) (z : Box Coord m) (p : ZMod 2) : Node Row Coord m

noncomputable instance {Row Coord : Type*} [Fintype Row] [Fintype Coord] (m : ℕ) :
    Fintype (Node Row Coord m) := by
  classical
  exact Fintype.ofEquiv
    ((Box Coord m × ZMod 2) ⊕ (State Row × State Row × Box Coord m × ZMod 2))
    { toFun := fun x => match x with
        | .inl (z, p) => .hub z p
        | .inr (a, v, z, p) => .work a v z p
      invFun := fun x => match x with
        | .hub z p => .inl (z, p)
        | .work a v z p => .inr (a, v, z, p)
      left_inv := by intro x; cases x <;> rfl
      right_inv := by intro x; cases x <;> rfl }

/-- The expanded graph has exactly 2(4m+1)^d(1+q²) vertices, including
when d=0. Here q=2r+1 is the number of signed states. -/
theorem node_card (Row Coord : Type*) [Fintype Row] [Fintype Coord] (m : ℕ) :
    Fintype.card (Node Row Coord m) =
      2 * (4 * m + 1) ^ Fintype.card Coord * (1 + (2 * Fintype.card Row + 1) ^ 2) := by
  classical
  let e : ((Box Coord m × ZMod 2) ⊕ (State Row × State Row × Box Coord m × ZMod 2)) ≃
      Node Row Coord m :=
    { toFun := fun x => match x with
        | .inl (z, p) => .hub z p
        | .inr (a, v, z, p) => .work a v z p
      invFun := fun x => match x with
        | .hub z p => .inl (z, p)
        | .work a v z p => .inr (a, v, z, p)
      left_inv := by intro x; cases x <;> rfl
      right_inv := by intro x; cases x <;> rfl }
  rw [← Fintype.card_congr e]
  simp only [Fintype.card_sum, Fintype.card_prod, ZMod.card, state_card, Box, Fintype.card_fun,
    Fintype.card_fin]
  ring

/-- The integer signature stored in either kind of state. -/
def signature {Row Coord : Type*} {m : ℕ} : Node Row Coord m → Coord → ℤ
  | .hub z _, r => coordinate z r
  | .work _ _ z _, r => coordinate z r

/-- The parity bit stored in either kind of state. -/
def parity {Row Coord : Type*} {m : ℕ} : Node Row Coord m → ZMod 2
  | .hub _ p => p
  | .work _ _ _ p => p

/-- Local potential relative to the anchor; zero on hubs. -/
def localPotential {Row Coord : Type*} [DecidableEq Row] {m : ℕ} :
    Node Row Coord m → Row → ℤ
  | .hub _ _, _ => 0
  | .work a v _ _, r => potential v r - potential a r

/-- An original-edge label contributes its weight; a zero-cost hub edge
contributes zero. -/
def labelValue {Edge A : Type*} [Zero A] (f : Edge → A) : Option Edge → A
  | none => 0
  | some e => f e

/-- The three kinds of arcs in the expanded graph. The move constructor is
available exactly when the updated signature is represented inside the box. -/
inductive Step {Row Edge Coord : Type*} (C : Edge → Column Row)
    (W : Edge → Coord → ℤ) (π : Edge → ZMod 2) (m : ℕ) :
    Node Row Coord m → Option Edge → Node Row Coord m → Prop
  | enter (a : State Row) (z : Box Coord m) (p : ZMod 2) :
      Step C W π m (.hub z p) none (.work a a z p)
  | exit (a : State Row) (z : Box Coord m) (p : ZMod 2) :
      Step C W π m (.work a a z p) none (.hub z p)
  | move (a : State Row) (e : Arc C) (z z' : Box Coord m) (p : ZMod 2)
      (hz : ∀ r, coordinate z' r = coordinate z r + W e.val.1 r) :
      Step C W π m (.work a (source C e) z p) (some e.val.1)
        (.work a (target C e) z' (p + π e.val.1))

/-- The actual arcs form a finite subtype of source/label/target triples. -/
abbrev GraphArc {Row Edge Coord : Type*} (C : Edge → Column Row)
    (W : Edge → Coord → ℤ) (π : Edge → ZMod 2) (m : ℕ) :=
  { t : Node Row Coord m × Option Edge × Node Row Coord m // Step C W π m t.1 t.2.1 t.2.2 }

noncomputable instance {Row Edge Coord : Type*} [Fintype Row] [Fintype Edge]
    [Fintype Coord] (C : Edge → Column Row) (W : Edge → Coord → ℤ)
    (π : Edge → ZMod 2) (m : ℕ) : Fintype (GraphArc C W π m) := Fintype.ofFinite _

/-- Each expanded-graph step has the correct local column increment. -/
theorem Step.local_increment {Row Edge Coord : Type*} [DecidableEq Row]
    {C : Edge → Column Row} {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}
    {s t : Node Row Coord m} {e : Option Edge} (h : Step C W π m s e t) (r : Row) :
    labelValue (fun e => columnVector (C e) r) e = localPotential t r - localPotential s r := by
  cases h with
  | enter a z p => simp [labelValue, localPotential]
  | exit a z p => simp [labelValue, localPotential]
  | move a e z z' p hz =>
      dsimp [labelValue, localPotential]
      rw [arc_potential]
      omega

/-- Each expanded-graph step has the recorded signature increment. -/
theorem Step.signature_increment {Row Edge Coord : Type*}
    {C : Edge → Column Row} {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}
    {s t : Node Row Coord m} {e : Option Edge} (h : Step C W π m s e t) (r : Coord) :
    labelValue (fun e => W e r) e = signature t r - signature s r := by
  cases h with
  | enter a z p => simp [labelValue, signature]
  | exit a z p => simp [labelValue, signature]
  | move a e z z' p hz =>
      dsimp [labelValue, signature]
      rw [hz]
      omega

/-- Each expanded-graph step has the recorded parity increment. -/
theorem Step.parity_increment {Row Edge Coord : Type*}
    {C : Edge → Column Row} {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}
    {s t : Node Row Coord m} {e : Option Edge} (h : Step C W π m s e t) :
    labelValue π e = parity t - parity s := by
  cases h <;> simp only [labelValue, parity] <;> abel

/-- A finite directed walk in the expanded graph. -/
inductive Path {Row Edge Coord : Type*} (C : Edge → Column Row)
    (W : Edge → Coord → ℤ) (π : Edge → ZMod 2) (m : ℕ) :
    Node Row Coord m → Node Row Coord m → Type _
  | nil (s : Node Row Coord m) : Path C W π m s s
  | cons {s t u : Node Row Coord m} (e : Option Edge)
      (step : Step C W π m s e t) (tail : Path C W π m t u) : Path C W π m s u

/-- The path's original-edge labels; entering/exiting a hub adds no label. -/
def Path.labels {Row Edge Coord : Type*} {C : Edge → Column Row}
    {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}
    {s t : Node Row Coord m} : Path C W π m s t → List Edge
  | .nil _ => []
  | .cons none _ tail => tail.labels
  | .cons (some e) _ tail => e :: tail.labels

/-- Concatenate two expanded-graph walks with a common endpoint. -/
def Path.append {Row Edge Coord : Type*} {C : Edge → Column Row}
    {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}
    {s t u : Node Row Coord m} (p : Path C W π m s t) (q : Path C W π m t u) :
    Path C W π m s u :=
  match p with
  | .nil _ => q
  | .cons e step tail => .cons e step (tail.append q)

@[simp] theorem Path.labels_append {Row Edge Coord : Type*} {C : Edge → Column Row}
    {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}
    {s t u : Node Row Coord m} (p : Path C W π m s t) (q : Path C W π m t u) :
    (p.append q).labels = p.labels ++ q.labels := by
  induction p with
  | nil => rfl
  | cons e step tail ih => cases e <;> simp [Path.append, Path.labels, ih]

/-- A generic telescoping principle for the actual expanded graph. -/
theorem Path.telescope {Row Edge Coord A : Type*} [AddCommGroup A]
    {C : Edge → Column Row} {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}
    {s t : Node Row Coord m} (path : Path C W π m s t)
    (f : Edge → A) (P : Node Row Coord m → A)
    (h : ∀ {u v e}, Step C W π m u e v → labelValue f e = P v - P u) :
    (path.labels.map f).sum = P t - P s := by
  induction path with
  | nil s => simp [Path.labels]
  | @cons s t u e step tail ih =>
      have hs := h step
      cases e with
      | none =>
          simp only [labelValue] at hs
          simp only [Path.labels]
          rw [ih]
          have he : P t = P s := sub_eq_zero.mp hs.symm
          rw [he]
      | some e =>
          simp only [labelValue] at hs
          simp only [Path.labels, List.map_cons, List.sum_cons]
          rw [hs, ih]
          abel

/-- Source and target of the shortest-path instance in the manuscript. -/
def start {Row Coord : Type*} (m : ℕ) : Node Row Coord m := .hub (zeroBox Coord m) 0

def finish {Row Coord : Type*} (m : ℕ) : Node Row Coord m := .hub (zeroBox Coord m) 1

/-- Every source-to-target path satisfies all local B-flow equations. -/
theorem Path.local_soundness {Row Edge Coord : Type*} [DecidableEq Row]
    [Fintype Edge] [DecidableEq Edge] {C : Edge → Column Row}
    {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}
    (path : Path C W π m (start m) (finish m)) (r : Row) :
    (∑ e, columnVector (C e) r * (projection path.labels e : ℤ)) = 0 := by
  rw [sum_mul_projection]
  have h := path.telescope (fun e => columnVector (C e) r) (fun v => localPotential v r)
    (fun hs => hs.local_increment r)
  simpa [start, finish, localPotential] using h

/-- Every source-to-target path has total W-signature zero. -/
theorem Path.signature_soundness {Row Edge Coord : Type*}
    [Fintype Edge] [DecidableEq Edge] {C : Edge → Column Row}
    {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}
    (path : Path C W π m (start m) (finish m)) (r : Coord) :
    (∑ e, W e r * (projection path.labels e : ℤ)) = 0 := by
  rw [sum_mul_projection]
  have h := path.telescope (fun e => W e r) (fun v => signature v r)
    (fun hs => hs.signature_increment r)
  simpa [start, finish, signature] using h

/-- Every source-to-target path has odd total parity. -/
theorem Path.parity_soundness {Row Edge Coord : Type*}
    [Fintype Edge] [DecidableEq Edge] {C : Edge → Column Row}
    {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}
    (path : Path C W π m (start m) (finish m)) :
    (∑ e, π e * (projection path.labels e : ZMod 2)) = 1 := by
  rw [sum_mul_projection]
  have h := path.telescope π parity (fun hs => hs.parity_increment)
  exact h.trans (by change (1 : ZMod 2) - 0 = 1; decide)

/-- The exact rational cost of a path, with zero cost at hub transitions. -/
def Path.cost {Row Edge Coord : Type*} {C : Edge → Column Row}
    {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}
    {s t : Node Row Coord m} (path : Path C W π m s t) (costs : Edge → ℚ) : ℚ :=
  (path.labels.map costs).sum

/-- Path cost equals the cost of its possibly nonbinary slack projection. -/
theorem Path.cost_projection {Row Edge Coord : Type*}
    [Fintype Edge] [DecidableEq Edge] {C : Edge → Column Row}
    {W : Edge → Coord → ℤ} {π : Edge → ZMod 2} {m : ℕ}
    {s t : Node Row Coord m} (path : Path C W π m s t) (costs : Edge → ℚ) :
    path.cost costs = ∑ e, costs e * (projection path.labels e : ℚ) := by
  exact (sum_mul_projection path.labels costs).symm

end WeightedMIS.Expanded
