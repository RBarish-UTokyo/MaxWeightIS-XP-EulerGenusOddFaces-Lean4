module

public import Mathlib

/-!
# Signed-stub walks and the finite signature bound

This file formalizes the soundness direction of manuscript Lemma 9 for the actual
zero-, one-, and two-stub construction, including repeated rows and equal signs.
It also proves the prefix bound used in Lemma 10. It does not prove the converse
port-pair decomposition or the shortest-path optimization theorem.
-/

@[expose] public section

namespace WeightedMIS.Walks

/-- A signed stub is a row and a sign: `true` means +1, `false` means -1. -/
abbrev Stub (Row : Type*) := Row × Bool

/-- The extra `none` state is the paper's hub `⋆`. -/
abbrev State (Row : Type*) := Option (Stub Row)

/-- A column specified by its zero, one, or two signed stubs. -/
inductive Column (Row : Type*) where
  | zero : Column Row
  | one : Stub Row → Column Row
  | two : Stub Row → Stub Row → Column Row
  deriving DecidableEq

/-- The integer value of a sign. -/
def signValue (s : Bool) : ℤ := if s then 1 else -1

/-- Change the sign of a stub. -/
def opposite {Row : Type*} (s : Stub Row) : Stub Row := (s.1, !s.2)

/-- The potential vector of a signed state, and zero at `⋆`. -/
def potential {Row : Type*} [DecidableEq Row] : State Row → Row → ℤ
  | none, _ => 0
  | some (v, s), r => if r = v then signValue s else 0

/-- The integer column vector, counting repeated stubs with multiplicity. -/
def columnVector {Row : Type*} [DecidableEq Row] : Column Row → Row → ℤ
  | .zero, _ => 0
  | .one s, r => potential (some s) r
  | .two s t, r => potential (some s) r + potential (some t) r

/-- Each nonzero column has two arcs; a zero column has just its forward loop. -/
abbrev Arc {Row Edge : Type*} (C : Edge → Column Row) :=
  { a : Edge × Bool // C a.1 ≠ .zero ∨ a.2 = false }

instance {Row Edge : Type*} [DecidableEq Row] [Fintype Edge]
    (C : Edge → Column Row) : Fintype (Arc C) :=
  inferInstanceAs (Fintype { a : Edge × Bool // C a.1 ≠ .zero ∨ a.2 = false })

/-- The signed-state graph has exactly 2r+1 vertices. -/
theorem state_card (Row : Type*) [Fintype Row] :
    Fintype.card (State Row) = 2 * Fintype.card Row + 1 := by
  simp [State, Stub, Fintype.card_prod, Nat.mul_comm]

/-- There are at most two directed arcs per original edge. -/
theorem arc_card_le {Row Edge : Type*} [DecidableEq Row] [Fintype Edge]
    (C : Edge → Column Row) : Fintype.card (Arc C) ≤ 2 * Fintype.card Edge := by
  simpa [Arc, Fintype.card_prod, Nat.mul_comm] using
    Fintype.card_subtype_le (fun a : Edge × Bool => C a.1 ≠ .zero ∨ a.2 = false)

/-- Source of an arc. `false` selects the forward orientation. -/
def source {Row Edge : Type*} (C : Edge → Column Row) (a : Arc C) : State Row :=
  match C a.val.1 with
  | .zero => none
  | .one s => if a.val.2 then some (opposite s) else none
  | .two s t => if a.val.2 then some (opposite t) else some (opposite s)

/-- Target of an arc in the signed-stub construction. -/
def target {Row Edge : Type*} (C : Edge → Column Row) (a : Arc C) : State Row :=
  match C a.val.1 with
  | .zero => none
  | .one s => if a.val.2 then none else some s
  | .two s t => if a.val.2 then some s else some t

@[simp] theorem potential_opposite {Row : Type*} [DecidableEq Row]
    (s : Stub Row) (r : Row) :
    potential (some (opposite s)) r = -potential (some s) r := by
  rcases s with ⟨v, s⟩
  cases s <;> by_cases h : r = v <;> simp [potential, opposite, signValue, h]

/-- Each actual arc has column equal to target potential minus source potential. -/
theorem arc_potential {Row Edge : Type*} [DecidableEq Row]
    (C : Edge → Column Row) (a : Arc C) (r : Row) :
    columnVector (C a.val.1) r = potential (target C a) r - potential (source C a) r := by
  cases h : C a.val.1 with
  | zero => simp [source, target, h, columnVector, potential]
  | one s =>
      cases hb : a.val.2 <;> simp [source, target, h, hb, columnVector] <;> simp [potential]
  | two s t =>
      cases hb : a.val.2 <;>
        simp [source, target, h, hb, columnVector, add_comm]

/-- A finite directed walk; its endpoints enforce that adjacent arcs meet. -/
inductive Walk {Row Edge : Type*} (C : Edge → Column Row) : State Row → State Row → Type _
  | nil (v : State Row) : Walk C v v
  | cons (a : Arc C) {v : State Row} (tail : Walk C (target C a) v) :
      Walk C (source C a) v

/-- The ordered original-edge labels of a directed walk. -/
def Walk.labels {Row Edge : Type*} {C : Edge → Column Row}
    {u v : State Row} : Walk C u v → List Edge
  | .nil _ => []
  | .cons a tail => a.val.1 :: tail.labels

/-- Summing columns along any directed walk telescopes. -/
theorem Walk.telescope {Row Edge : Type*} [DecidableEq Row] {C : Edge → Column Row}
    {u v : State Row} (w : Walk C u v) (r : Row) :
    (w.labels.map (fun e => columnVector (C e) r)).sum = potential v r - potential u r := by
  induction w with
  | nil u => simp [Walk.labels]
  | cons a tail ih =>
      simp only [Walk.labels, List.map_cons, List.sum_cons]
      rw [arc_potential, ih]
      omega

/-- Every closed walk has zero total column vector. -/
theorem Walk.closed_sum_zero {Row Edge : Type*} [DecidableEq Row]
    {C : Edge → Column Row} {u : State Row} (w : Walk C u u) (r : Row) :
    (w.labels.map (fun e => columnVector (C e) r)).sum = 0 := by
  simpa using w.telescope r

/-- Count the multiplicity of each edge label, as a nonnegative integer. -/
def projection {Edge : Type*} [DecidableEq Edge] (l : List Edge) (e : Edge) : ℕ :=
  l.count e

/-- Counting labels and summing by edge equals summing along the list. -/
theorem sum_mul_projection {Edge R : Type*} [Fintype Edge] [DecidableEq Edge]
    [Semiring R] (l : List Edge) (f : Edge → R) :
    (∑ e, f e * (projection l e : R)) = (l.map f).sum := by
  induction l with
  | nil => simp [projection]
  | cons a l ih =>
      have hc (e : Edge) :
          (projection (a :: l) e : R) = (projection l e : R) +
            (if e = a then 1 else 0) := by
        by_cases he : e = a
        · subst e; simp [projection]
        · simp [projection, he, Ne.symm he]
      simp only [List.map_cons, List.sum_cons]
      simp_rw [hc, mul_add]
      rw [Finset.sum_add_distrib, ih]
      have hs : (∑ e, f e * (if e = a then 1 else 0)) = f a := by
        simp [mul_ite]
      rw [hs, add_comm]

/-- Soundness direction of Lemma 9: the walk projection is a nonnegative
integral solution of every local row equation. -/
theorem Walk.closed_projection_kernel {Row Edge : Type*} [DecidableEq Row]
    [Fintype Edge] [DecidableEq Edge] {C : Edge → Column Row}
    {u : State Row} (w : Walk C u u) (r : Row) :
    (∑ e, columnVector (C e) r * (projection w.labels e : ℤ)) = 0 := by
  rw [sum_mul_projection]
  exact w.closed_sum_zero r

/-- A closed walk with its chosen anchor. -/
abbrev ClosedWalk {Row Edge : Type*} (C : Edge → Column Row) :=
  Σ u : State Row, Walk C u u

/-- Concatenating the labels of closed working portions preserves every local
row equation, even if labels occur repeatedly and the anchors differ. -/
theorem closed_walks_projection_kernel {Row Edge : Type*} [DecidableEq Row]
    [Fintype Edge] [DecidableEq Edge] {C : Edge → Column Row}
    (ws : List (ClosedWalk C)) (r : Row) :
    (∑ e, columnVector (C e) r *
      (projection (ws.flatMap (fun w => w.2.labels)) e : ℤ)) = 0 := by
  rw [sum_mul_projection]
  induction ws with
  | nil => simp
  | cons w ws ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append]
      rw [w.2.closed_sum_zero r, ih]
      simp

/-- The projection uses exactly one edge copy per arc. -/
theorem sum_projection_eq_length {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (l : List Edge) : (∑ e, projection l e) = l.length := by
  have h := sum_mul_projection l (fun _ => (1 : ℕ))
  have hs : (l.map (fun _ => (1 : ℕ))).sum = l.length := by
    induction l with
    | nil => simp
    | cons a l ih => simp [Nat.add_comm]
  simpa [hs] using h

/-- A binary projection guarantees that the witness uses at most m arcs,
where m is the number of original edges. -/
theorem length_le_card_of_binary_projection {Edge : Type*}
    [Fintype Edge] [DecidableEq Edge] (l : List Edge)
    (h : ∀ e, projection l e ≤ 1) : l.length ≤ Fintype.card Edge := by
  rw [← sum_projection_eq_length]
  calc
    (∑ e, projection l e) ≤ ∑ _ : Edge, 1 := Finset.sum_le_sum (fun e _ => h e)
    _ = Fintype.card Edge := by simp

/-- A sequence of coordinate changes of absolute value at most two has total
absolute value at most twice its length. -/
theorem abs_sum_le_two_length {Edge : Type*} (l : List Edge) (f : Edge → ℤ)
    (h : ∀ e ∈ l, |f e| ≤ 2) :
    |(l.map f).sum| ≤ 2 * (l.length : ℤ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := h a List.mem_cons_self
      have ht : ∀ e ∈ l, |f e| ≤ 2 := fun e he => h e (List.mem_cons_of_mem a he)
      have hi := ih ht
      calc
        |((a :: l).map f).sum| = |f a + (l.map f).sum| := by simp
        _ ≤ |f a| + |(l.map f).sum| := abs_add_le _ _
        _ ≤ 2 + 2 * (l.length : ℤ) := add_le_add ha hi
        _ = 2 * ((a :: l).length : ℤ) := by simp; omega

/-- Every prefix is in the search box [-2m,2m] if the complete witness uses at
most m original-edge arcs and each coordinate change has absolute value at most 2.
This also covers the empty prefix and the case of no signature coordinates. -/
theorem prefix_signature_bound {Edge Coord : Type*} (l : List Edge)
    (W : Edge → Coord → ℤ) (m j : ℕ) (r : Coord)
    (hlen : l.length ≤ m) (hW : ∀ e ∈ l, |W e r| ≤ 2) :
    |((l.take j).map (fun e => W e r)).sum| ≤ 2 * (m : ℤ) := by
  have htake : ∀ e ∈ l.take j, |W e r| ≤ 2 :=
    fun e he => hW e (List.mem_of_mem_take he)
  have hbound := abs_sum_le_two_length (l.take j) (fun e => W e r) htake
  have hlength : (l.take j).length ≤ m := le_trans (List.length_take_le' _ _) hlen
  have hcast : ((l.take j).length : ℤ) ≤ (m : ℤ) := by exact_mod_cast hlength
  omega

end WeightedMIS.Walks
