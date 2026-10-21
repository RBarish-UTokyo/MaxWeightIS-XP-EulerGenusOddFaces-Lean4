module

public import WeightedMIS.GraphSearch
public import WeightedMIS.IntegerSlacks

/-!
# An executable bounded odd row

Reachability in the parity double cover finds a route from a root at parity
zero to the same root at parity one. Scanning original edge labels and summing
its signed traversals produces the odd row used by the search algorithm.
-/

@[expose] public section

namespace WeightedMIS.ComputedOddRow

open scoped BigOperators
open GraphSearch MaxFlowReach ShortestPath

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def phase (n : ℕ) (b : Bool) : Bool := if n % 2 = 0 then b else !b

@[simp] theorem phase_zero (b : Bool) : phase 0 b = b := by simp [phase]

theorem phase_succ (n : ℕ) (b : Bool) : phase (n + 1) b = !(phase n b) := by
  have hn := Nat.mod_lt n (by decide : 0 < 2)
  by_cases h : n % 2 = 0
  · have hh : (n + 1) % 2 ≠ 0 := by omega
    simp [phase, h, hh]
  · have hh : (n + 1) % 2 = 0 := by omega
    simp [phase, h, hh]

def AdjacentParity (left right : E → V) (edges : List E) (u v : V × Bool) : Prop :=
  Adjacent left right edges u.1 v.1 ∧ v.2 = !u.2

instance (left right : E → V) (edges : List E) :
    DecidableRel (AdjacentParity left right edges) := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

def parityNodes (nodes : List V) : List (V × Bool) := nodes.product [false, true]

theorem parityNodes_complete (nodes : List V) (complete : ∀ v, v ∈ nodes) :
    ∀ v, v ∈ parityNodes nodes := by
  rintro ⟨v, b⟩
  cases b <;> simp [parityNodes, complete]

/-- Graph walks lift to parity walks in every closed reached set. -/
theorem closed_walk_phase (left right : E → V) (edges : List E) (complete : ∀ e, e ∈ edges)
    (S : Finset (V × Bool))
    (hclosed : ∀ u ∈ S, ∀ v ∉ S, ¬ AdjacentParity left right edges u v)
    {a b : V} {n : ℕ} (p : Incidence.Walk left right a b n) (start : Bool)
    (ha : (a, start) ∈ S) : (b, phase n start) ∈ S := by
  induction p with
  | nil => simpa using ha
  | @forward b n e hb p ih =>
    by_contra hn
    apply hclosed (b, phase n start) ih (right e, phase (n + 1) start) hn
    refine ⟨?_, phase_succ n start⟩
    apply (adjacent_iff left right edges complete b (right e)).mpr
    exact ⟨e, Or.inl ⟨hb.symm, rfl⟩⟩
  | @backward b n e hb p ih =>
    by_contra hn
    apply hclosed (b, phase n start) ih (left e, phase (n + 1) start) hn
    refine ⟨?_, phase_succ n start⟩
    apply (adjacent_iff left right edges complete b (left e)).mpr
    exact ⟨e, Or.inr ⟨rfl, hb.symm⟩⟩

/-- Any chosen root of a connected nonbipartite graph has an odd closed walk. -/
theorem odd_walk_at_root (left right : E → V) (root : V)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    ∃ n, Odd n ∧ Incidence.Walk left right root root n := by
  obtain ⟨a, n, hn, p⟩ := OddRow.exists_odd_closed_walk left right hc hnb
  obtain ⟨m, q⟩ := hc root a
  refine ⟨m + n + m, ?_, OddRow.walk_append left right
    (OddRow.walk_append left right q p) (OddRow.walk_reverse left right q)⟩
  rw [Nat.odd_iff] at hn ⊢
  omega

def paritySearch (left right : E → V) (edges : List E) (nodes : List V) (root : V) : State (V × Bool) :=
  explore (AdjacentParity left right edges) (parityNodes nodes) (Fintype.card (V × Bool)) (initial (root, false))

theorem paritySearch_correct (left right : E → V) (edges : List E) (hedges : ∀ e, e ∈ edges)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (root : V)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    IsWalk Prod.fst Prod.snd (root, false) (root, true)
      ((paritySearch left right edges nodes root).route (root, true)) ∧
      (∀ a ∈ (paritySearch left right edges nodes root).route (root, true),
        AdjacentParity left right edges a.1 a.2) ∧
      ((paritySearch left right edges nodes root).route (root, true)).length + 1 ≤
        2 * Fintype.card V := by
  have hs := search_spec (AdjacentParity left right edges) (parityNodes nodes)
    (parityNodes_complete nodes hnodes) (root, false) (root, true)
  change (root, false) ∈ (paritySearch left right edges nodes root).seen ∧ _ at hs
  obtain ⟨n, hn, p⟩ := odd_walk_at_root left right root hc hnb
  have hv := closed_walk_phase left right edges hedges _ hs.2.2 p false hs.1
  have hphase : phase n false = true := by
    have hn' := Nat.odd_iff.mp hn
    simp [phase, hn']
  rw [hphase] at hv
  have hw := hs.2.1 hv
  refine ⟨hw.1, hw.2.2, ?_⟩
  have hi := explore_invariant (AdjacentParity left right edges) (parityNodes nodes)
    (root, false) (Fintype.card (V × Bool)) (initial (root, false))
    (initial_invariant (AdjacentParity left right edges) (root, false))
  have hl := invariant_route_length _ _ _ hi (root, true) hv
  simpa only [paritySearch, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using hl

/-- The direction sign, determined by the actual parity bit. -/
def sign (b : Bool) : ℤ := if b then -1 else 1

/-- Sum the signed original-edge occurrences along the stored parity route. -/
def row (left right : E → V) (edges : List E) : List ((V × Bool) × (V × Bool)) → E → ℤ
  | [], _ => 0
  | a :: rest, e =>
      (if edgeBetween left right edges a.1.1 a.2.1 = some e then sign a.1.2 else 0) +
        row left right edges rest e

/-- The computed row telescopes to the signed endpoint difference. -/
theorem row_telescopes (left right : E → V) (edges : List E)
    {s t : V × Bool} (p : List ((V × Bool) × (V × Bool)))
    (hp : IsWalk Prod.fst Prod.snd s t p)
    (hs : ∀ a ∈ p, AdjacentParity left right edges a.1 a.2) (x : V → ℚ) :
    (∑ e, (row left right edges p e : ℚ) * (x (left e) + x (right e))) =
      (sign s.2 : ℚ) * x s.1 - (sign t.2 : ℚ) * x t.1 := by
  induction p generalizing s with
  | nil =>
    change s = t at hp
    subst t
    simp [row]
  | cons a p ih =>
    have ha := hs a (by simp)
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp ha.1
    have hend := edgeBetween_some left right edges a.1.1 a.2.1 e he
    have htail : ∀ b ∈ p, AdjacentParity left right edges b.1 b.2 :=
      fun b hb => hs b (by simp [hb])
    have hr := ih hp.2 htail
    have hedges : x (left e) + x (right e) = x a.1.1 + x a.2.1 := by
      rcases hend with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> simp [hl, hr, add_comm]
    have hsign : (sign a.2.2 : ℚ) = -(sign a.1.2 : ℚ) := by
      rw [ha.2]
      cases a.1.2 <;> norm_num [sign]
    simp only [row, Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [hr]
    have hfirst : (∑ f, ((if edgeBetween left right edges a.1.1 a.2.1 = some f then
        sign a.1.2 else 0 : ℤ) : ℚ) * (x (left f) + x (right f))) =
          (sign a.1.2 : ℚ) * (x (left e) + x (right e)) := by
      simp [he, eq_comm]
    rw [hfirst, hedges, hsign]
    have hstart : a.1 = s := hp.1
    rw [← hstart]
    ring

/-- The parity row generated by the deterministic search. -/
def oddRow (left right : E → V) (edges : List E) (nodes : List V) (root : V) : E → ℤ :=
  row left right edges ((paritySearch left right edges nodes root).route (root, true))

theorem oddRow_correct (left right : E → V) (edges : List E) (hedges : ∀ e, e ∈ edges)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (root : V)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) :
    IntegerSlacks.OddRow left right root (oddRow left right edges nodes root) := by
  intro x
  have hs := paritySearch_correct left right edges hedges nodes hnodes root hc hnb
  have hr := row_telescopes left right edges _ hs.1 hs.2.1 x
  simpa [oddRow, sign, two_mul] using hr

/-- No coefficient exceeds the number of executed edge traversals. -/
theorem row_natAbs_le (left right : E → V) (edges : List E)
    (p : List ((V × Bool) × (V × Bool))) (e : E) :
    (row left right edges p e).natAbs ≤ p.length := by
  induction p with
  | nil => simp [row]
  | cons a p ih =>
    have hc : (if edgeBetween left right edges a.1.1 a.2.1 = some e then
        sign a.1.2 else 0 : ℤ).natAbs ≤ 1 := by
      split
      · cases a.1.2 <;> decide
      · decide
    have hh := Int.natAbs_add_le
      (if edgeBetween left right edges a.1.1 a.2.1 = some e then sign a.1.2 else 0)
      (row left right edges p e)
    simp only [row, List.length_cons]
    omega

/-- The actual odd-row coefficients have linear, rather than arbitrary, size. -/
theorem oddRow_natAbs_lt (left right : E → V) (edges : List E) (hedges : ∀ e, e ∈ edges)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (root : V)
    (hc : Incidence.Connected left right) (hnb : ¬ Incidence.Bipartite left right) (e : E) :
    (oddRow left right edges nodes root e).natAbs < 2 * Fintype.card V := by
  have hl := (paritySearch_correct left right edges hedges nodes hnodes root hc hnb).2.2
  have hr := row_natAbs_le left right edges
    ((paritySearch left right edges nodes root).route (root, true)) e
  change (row left right edges ((paritySearch left right edges nodes root).route (root, true)) e).natAbs < _
  omega

end WeightedMIS.ComputedOddRow
