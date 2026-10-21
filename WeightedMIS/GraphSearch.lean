module

public import WeightedMIS.MaxFlowReach
public import WeightedMIS.Incidence
public import WeightedMIS.EdgeTransport

/-!
# Deterministic reachability in endpoint graphs

An edge is selected by scanning the supplied list. Reachability returns actual
vertex routes, and each route can therefore be converted to original edge
labels without any choice operator.
-/

@[expose] public section

namespace WeightedMIS.GraphSearch

open scoped BigOperators
open MaxFlowReach ShortestPath

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- The first supplied edge joining the two requested vertices. -/
def edgeBetween (left right : E → V) (edges : List E) (u v : V) : Option E :=
  edges.find? fun e => decide ((left e = u ∧ right e = v) ∨ (left e = v ∧ right e = u))

/-- Decidable adjacency computed from the edge list. -/
def Adjacent (left right : E → V) (edges : List E) (u v : V) : Prop :=
  (edgeBetween left right edges u v).isSome = true

instance (left right : E → V) (edges : List E) :
    DecidableRel (Adjacent left right edges) := fun _ _ => inferInstanceAs (Decidable (_ = true))

theorem edgeBetween_some (left right : E → V) (edges : List E) (u v : V) (e : E)
    (he : edgeBetween left right edges u v = some e) :
    (left e = u ∧ right e = v) ∨ (left e = v ∧ right e = u) := by
  have h := List.find?_some he
  simpa only [decide_eq_true_eq] using h

theorem adjacent_iff (left right : E → V) (edges : List E) (complete : ∀ e, e ∈ edges)
    (u v : V) : Adjacent left right edges u v ↔ EdgeTransport.Adj left right u v := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h
    exact ⟨e, edgeBetween_some left right edges u v e he⟩
  · rintro ⟨e, he⟩
    by_contra hn
    have hz : edgeBetween left right edges u v = none := by
      cases h : edgeBetween left right edges u v <;> simp [Adjacent, h] at hn ⊢
    have hh := List.find?_eq_none.mp hz e (complete e)
    exact hh (by simpa only [decide_eq_true_eq] using he)

/-- Propagate membership along an actual graph walk in a closed reached set. -/
theorem closed_walk (left right : E → V) (edges : List E) (complete : ∀ e, e ∈ edges)
    (S : Finset V) (hclosed : ∀ u ∈ S, ∀ v ∉ S, ¬ Adjacent left right edges u v)
    {a b : V} {n : ℕ} (p : Incidence.Walk left right a b n) (ha : a ∈ S) : b ∈ S := by
  induction p with
  | nil => exact ha
  | @forward b n e hb p ih =>
    by_contra hn
    apply hclosed b ih (right e) hn
    apply (adjacent_iff left right edges complete b (right e)).mpr
    exact ⟨e, Or.inl ⟨hb.symm, rfl⟩⟩
  | @backward b n e hb p ih =>
    by_contra hn
    apply hclosed b ih (left e) hn
    apply (adjacent_iff left right edges complete b (left e)).mpr
    exact ⟨e, Or.inr ⟨rfl, hb.symm⟩⟩

/-- The actual route table computed from one root. -/
def search (left right : E → V) (edges : List E) (nodes : List V) (root : V) : State V :=
  explore (Adjacent left right edges) nodes (Fintype.card V) (initial root)

/-- In a connected graph the executable search reaches every vertex and
returns a simple path whose every ordered pair has an original edge label. -/
theorem search_correct (left right : E → V) (edges : List E) (hedges : ∀ e, e ∈ edges)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (root : V)
    (hc : Incidence.Connected left right) (v : V) :
    v ∈ (search left right edges nodes root).seen ∧
      IsWalk Prod.fst Prod.snd root v ((search left right edges nodes root).route v) ∧
      IsSimple Prod.snd root ((search left right edges nodes root).route v) ∧
      (∀ a ∈ (search left right edges nodes root).route v, Adjacent left right edges a.1 a.2) ∧
      ((search left right edges nodes root).route v).length + 1 ≤ Fintype.card V := by
  have hs := search_spec (Adjacent left right edges) nodes hnodes root v
  change root ∈ (search left right edges nodes root).seen ∧ _ at hs
  obtain ⟨n, p⟩ := hc root v
  have hv := closed_walk left right edges hedges _ hs.2.2 p hs.1
  have hw := hs.2.1 hv
  refine ⟨hv, hw.1, hw.2.1, hw.2.2, ?_⟩
  have hi := explore_invariant (Adjacent left right edges) nodes root (Fintype.card V)
    (initial root) (initial_invariant (Adjacent left right edges) root)
  exact invariant_route_length _ _ _ hi v hv

/-- The edge sum used to propagate an integer vertex value along a route. -/
def edgeSum (left right : E → V) (edges : List E) (y : E → ℤ) (u v : V) : ℤ :=
  match edgeBetween left right edges u v with
  | none => 0
  | some e => 1 - y e

theorem edgeSum_eq (left right : E → V) (edges : List E) (y : E → ℤ) (z : V → ℤ)
    (hz : ∀ e, z (left e) + z (right e) = 1 - y e) (u v : V)
    (ha : Adjacent left right edges u v) : edgeSum left right edges y u v = z u + z v := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp ha
  have h := edgeBetween_some left right edges u v e he
  simp only [edgeSum, he]
  rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · simpa only [hl, hr] using (hz e).symm
  · simpa only [hl, hr, add_comm] using (hz e).symm

/-- Explicit integer propagation along the stored route. -/
def propagate (left right : E → V) (edges : List E) (y : E → ℤ) :
    List (V × V) → ℤ → ℤ
  | [], value => value
  | a :: rest, value => propagate left right edges y rest (edgeSum left right edges y a.1 a.2 - value)

/-- Integer propagation agrees with every actual realizing vector. -/
theorem propagate_eq (left right : E → V) (edges : List E) (y : E → ℤ) (z : V → ℤ)
    (hz : ∀ e, z (left e) + z (right e) = 1 - y e)
    {s t : V} (p : List (V × V)) (hp : IsWalk Prod.fst Prod.snd s t p)
    (hs : ∀ a ∈ p, Adjacent left right edges a.1 a.2) :
    propagate left right edges y p (z s) = z t := by
  induction p generalizing s with
  | nil =>
    change s = t at hp
    subst t
    rfl
  | cons a p ih =>
    have he := edgeSum_eq left right edges y z hz a.1 a.2 (hs a (by simp))
    have hb : ∀ b ∈ p, Adjacent left right edges b.1 b.2 := fun b hb => hs b (by simp [hb])
    change propagate left right edges y p (edgeSum left right edges y a.1 a.2 - z s) = z t
    rw [he, hp.1, add_sub_cancel_left]
    exact ih hp.2 hb

end WeightedMIS.GraphSearch
