module

public import WeightedMIS.MaxFlowReach

/-!
# Materialized reached vertices and shared reverse routes

A newly discovered route is one cons cell followed by its predecessor's route.
The association list stores actual paths rather than a chain of closures.
-/

@[expose] public section

namespace WeightedMIS.MaxFlowListReach

variable {V : Type*} [DecidableEq V]

abbrev Routes (V : Type*) := List (V × List (V × V))

def lookup (routes : Routes V) (v : V) : List (V × V) :=
  match routes with
  | [] => []
  | (u, path) :: rest => if v = u then path else lookup rest v

structure State (V : Type*) where
  seen : List V
  routes : Routes V

def decode (q : State V) : MaxFlowReach.State V :=
  ⟨q.seen.toFinset, fun v => (lookup q.routes v).reverse⟩

def extend (q : State V) (a : V × V) : State V :=
  ⟨a.2 :: q.seen, (a.2, a :: lookup q.routes a.1) :: q.routes⟩

def initial (s : V) : State V := ⟨[s], [(s, [])]⟩

theorem decode_initial (s : V) : decode (initial s) = MaxFlowReach.initial s := by
  unfold decode initial MaxFlowReach.initial lookup
  congr
  funext v
  split <;> rfl

theorem decode_extend (q : State V) (a : V × V) :
    decode (extend q a) = MaxFlowReach.extend (decode q) a := by
  unfold decode extend MaxFlowReach.extend
  congr 1
  · simp
  · funext v
    by_cases hv : v = a.2 <;> simp [lookup, hv]

def explore (rel : V → V → Prop) [DecidableRel rel] (nodes : List V) :
    ℕ → State V → State V
  | 0, q => q
  | fuel + 1, q =>
    match MaxFlowReach.crossing rel nodes q.seen.toFinset with
    | none => q
    | some a => explore rel nodes fuel (extend q a)

theorem explore_refines (rel : V → V → Prop) [DecidableRel rel] (nodes : List V)
    (fuel : ℕ) (q : State V) :
    decode (explore rel nodes fuel q) = MaxFlowReach.explore rel nodes fuel (decode q) := by
  induction fuel generalizing q with
  | zero => rfl
  | succ fuel ih =>
    simp only [explore, MaxFlowReach.explore]
    change decode (match MaxFlowReach.crossing rel nodes q.seen.toFinset with
      | none => q
      | some a => explore rel nodes fuel (extend q a)) =
      match MaxFlowReach.crossing rel nodes q.seen.toFinset with
      | none => decode q
      | some a => MaxFlowReach.explore rel nodes fuel (MaxFlowReach.extend (decode q) a)
    cases he : MaxFlowReach.crossing rel nodes q.seen.toFinset with
    | none => simp [decode, he]
    | some a =>
      change decode (explore rel nodes fuel (extend q a)) =
        MaxFlowReach.explore rel nodes fuel (MaxFlowReach.extend (decode q) a)
      rw [ih, decode_extend]

theorem explore_lengths (rel : V → V → Prop) [DecidableRel rel] (nodes : List V)
    (fuel : ℕ) (q : State V) :
    (explore rel nodes fuel q).seen.length ≤ q.seen.length + fuel ∧
    (explore rel nodes fuel q).routes.length ≤ q.routes.length + fuel := by
  induction fuel generalizing q with
  | zero => simp [explore]
  | succ fuel ih =>
    simp only [explore]
    split
    · constructor <;> omega
    · rename_i a _
      have hh := ih (extend q a)
      simp only [extend, List.length_cons] at hh ⊢
      constructor <;> omega

/-- The concrete list state inherits the existing simple-route and cut theorem. -/
theorem search_spec [Fintype V] (rel : V → V → Prop) [DecidableRel rel]
    (nodes : List V) (complete : ∀ v, v ∈ nodes) (s t : V) :
    let q := explore rel nodes (Fintype.card V) (initial s)
    s ∈ q.seen ∧
      (t ∈ q.seen → ShortestPath.IsWalk Prod.fst Prod.snd s t (lookup q.routes t).reverse ∧
        ShortestPath.IsSimple Prod.snd s (lookup q.routes t).reverse ∧
        ∀ a ∈ lookup q.routes t, rel a.1 a.2) ∧
      (∀ u ∈ q.seen, ∀ v ∉ q.seen, ¬ rel u v) := by
  have hspec := MaxFlowReach.search_spec rel nodes complete s t
  rw [← decode_initial, ← explore_refines] at hspec
  simpa [decode] using hspec

end WeightedMIS.MaxFlowListReach
