module

public import WeightedMIS.ShortestPath
public import Mathlib.Tactic

/-!
# Executable residual reachability with simple-path witnesses

The search repeatedly scans an explicit vertex list for an arc from the reached
set to an unreached vertex. Each successful round adds one vertex and extends
its simple path. At most the number of vertices rounds are needed. The scan is
quadratic and the number of scans is linear in the vertex-list length.
-/

@[expose] public section

namespace WeightedMIS.MaxFlowReach

open ShortestPath

variable {V : Type*} [DecidableEq V]

structure State (V : Type*) where
  seen : Finset V
  route : V → List (V × V)

/-- Scan the given finite list of ordered pairs for a crossing arc. -/
def crossing (rel : V → V → Prop) [DecidableRel rel] (nodes : List V)
    (S : Finset V) : Option (V × V) :=
  (nodes.product nodes).find? fun p => decide (p.1 ∈ S ∧ p.2 ∉ S ∧ rel p.1 p.2)

/-- Store the route to the new vertex. -/
def extend (q : State V) (a : V × V) : State V :=
  ⟨insert a.2 q.seen, fun v => if v = a.2 then q.route a.1 ++ [a] else q.route v⟩

/-- Each round either stops or discovers one new vertex. -/
def explore (rel : V → V → Prop) [DecidableRel rel] (nodes : List V) :
    ℕ → State V → State V
  | 0, q => q
  | fuel + 1, q =>
      match crossing rel nodes q.seen with
      | none => q
      | some a => explore rel nodes fuel (extend q a)

/-- Initial reached state. -/
def initial (s : V) : State V := ⟨{s}, fun _ => []⟩

/-- The search carries actual simple paths, all supported on the relation. -/
structure Invariant (rel : V → V → Prop) (s : V) (q : State V) : Prop where
  source : s ∈ q.seen
  walk : ∀ v ∈ q.seen, IsWalk Prod.fst Prod.snd s v (q.route v)
  simple : ∀ v ∈ q.seen, IsSimple Prod.snd s (q.route v)
  visited : ∀ v ∈ q.seen, ∀ u ∈ vertices Prod.snd s (q.route v), u ∈ q.seen
  supported : ∀ v ∈ q.seen, ∀ a ∈ q.route v, rel a.1 a.2

theorem initial_invariant (rel : V → V → Prop) (s : V) :
    Invariant rel s (initial s) := by
  constructor
  · simp [initial]
  · intro v hv
    have he : v = s := by simpa [initial] using hv
    simp [initial, IsWalk, he]
  · intro v _
    simp [initial, IsSimple, vertices]
  · intro v _ u hu
    simpa [initial, vertices] using hu
  · intro v _ a ha
    simp [initial] at ha

theorem crossing_some (rel : V → V → Prop) [DecidableRel rel]
    (nodes : List V) (S : Finset V) (a : V × V)
    (ha : crossing rel nodes S = some a) : a.1 ∈ S ∧ a.2 ∉ S ∧ rel a.1 a.2 := by
  have hh := List.find?_some ha
  simpa only [decide_eq_true_eq] using hh

theorem crossing_none (rel : V → V → Prop) [DecidableRel rel]
    (nodes : List V) (complete : ∀ v, v ∈ nodes) (S : Finset V)
    (ha : crossing rel nodes S = none) : ∀ u ∈ S, ∀ v ∉ S, ¬ rel u v := by
  intro u hu v hv huv
  have hh := List.find?_eq_none.mp ha (u, v)
    (List.mem_product.mpr ⟨complete u, complete v⟩)
  simpa [hu, hv, huv] using hh

/-- Every successful crossing preserves the path invariant. -/
theorem extend_invariant (rel : V → V → Prop) (s : V) (q : State V)
    (hq : Invariant rel s q) (a : V × V)
    (ha : a.1 ∈ q.seen ∧ a.2 ∉ q.seen ∧ rel a.1 a.2) :
    Invariant rel s (extend q a) := by
  have hwalk : IsWalk Prod.fst Prod.snd s a.2 (q.route a.1 ++ [a]) :=
    walk_append Prod.fst Prod.snd (hq.walk a.1 ha.1) ⟨rfl, rfl⟩
  have htrace : vertices Prod.snd s (q.route a.1 ++ [a]) =
      vertices Prod.snd s (q.route a.1) ++ [a.2] := by
    simp [vertices]
  have hsimple : IsSimple Prod.snd s (q.route a.1 ++ [a]) := by
    rw [IsSimple, htrace]
    apply List.Nodup.append (hq.simple a.1 ha.1) (by simp)
    intro u hu hv
    have he : u = a.2 := by simpa using hv
    exact ha.2.1 (he ▸ hq.visited a.1 ha.1 u hu)
  constructor
  · exact Finset.mem_insert_of_mem hq.source
  · intro v hv
    by_cases he : v = a.2
    · simpa [extend, he] using hwalk
    · have hv' : v ∈ q.seen := (Finset.mem_insert.mp hv).resolve_left he
      simpa [extend, he] using hq.walk v hv'
  · intro v hv
    by_cases he : v = a.2
    · simpa [extend, he] using hsimple
    · have hv' : v ∈ q.seen := (Finset.mem_insert.mp hv).resolve_left he
      simpa [extend, he] using hq.simple v hv'
  · intro v hv u hu
    by_cases he : v = a.2
    · have hu' : u ∈ vertices Prod.snd s (q.route a.1) ++ [a.2] := by
        simpa only [extend, ite_eq_left he, htrace] using hu
      rcases List.mem_append.mp hu' with hu' | hu'
      · exact Finset.mem_insert_of_mem (hq.visited a.1 ha.1 u hu')
      · have he' : u = a.2 := by simpa using hu'
        simp [extend, he']
    · have hv' : v ∈ q.seen := (Finset.mem_insert.mp hv).resolve_left he
      have hu' : u ∈ vertices Prod.snd s (q.route v) := by simpa [extend, he] using hu
      exact Finset.mem_insert_of_mem (hq.visited v hv' u hu')
  · intro v hv b hb
    by_cases he : v = a.2
    · have hb' : b ∈ q.route a.1 ++ [a] := by simpa [extend, he] using hb
      rcases List.mem_append.mp hb' with hb' | hb'
      · exact hq.supported a.1 ha.1 b hb'
      · have he' : b = a := by simpa using hb'
        simpa [he'] using ha.2.2
    · have hv' : v ∈ q.seen := (Finset.mem_insert.mp hv).resolve_left he
      have hb' : b ∈ q.route v := by simpa [extend, he] using hb
      exact hq.supported v hv' b hb'

theorem explore_invariant (rel : V → V → Prop) [DecidableRel rel]
    (nodes : List V) (s : V) (fuel : ℕ) (q : State V) (hq : Invariant rel s q) :
    Invariant rel s (explore rel nodes fuel q) := by
  induction fuel generalizing q with
  | zero => exact hq
  | succ fuel ih =>
      simp only [explore]
      split
      · exact hq
      · rename_i a ha
        exact ih _ (extend_invariant rel s q hq a (crossing_some rel nodes q.seen a ha))

/-- At most one successful scan per vertex is required to reach closure. -/
theorem explore_closed [Fintype V] (rel : V → V → Prop) [DecidableRel rel]
    (nodes : List V) (fuel : ℕ) (q : State V)
    (hbound : Fintype.card V ≤ fuel + q.seen.card) :
    crossing rel nodes (explore rel nodes fuel q).seen = none := by
  induction fuel generalizing q with
  | zero =>
      have he : q.seen = Finset.univ := Finset.eq_univ_of_card q.seen
        (by have := Finset.card_le_univ q.seen; omega)
      simp [explore, crossing, he]
  | succ fuel ih =>
      simp only [explore]
      split
      · assumption
      · rename_i a ha
        apply ih
        have hnot := (crossing_some rel nodes q.seen a ha).2.1
        simp only [extend, Finset.card_insert_of_notMem hnot]
        omega

/-- The concrete search returns either a genuine simple path or a closed cut. -/
theorem search_spec [Fintype V] (rel : V → V → Prop) [DecidableRel rel]
    (nodes : List V) (complete : ∀ v, v ∈ nodes) (s t : V) :
    let q := explore rel nodes (Fintype.card V) (initial s)
    s ∈ q.seen ∧
      (t ∈ q.seen → IsWalk Prod.fst Prod.snd s t (q.route t) ∧
        IsSimple Prod.snd s (q.route t) ∧ ∀ a ∈ q.route t, rel a.1 a.2) ∧
      (∀ u ∈ q.seen, ∀ v ∉ q.seen, ¬ rel u v) := by
  dsimp only
  have hi := explore_invariant rel nodes s (Fintype.card V) (initial s)
    (initial_invariant rel s)
  have hc := explore_closed rel nodes (Fintype.card V) (initial s) (by omega)
  exact ⟨hi.source, fun ht => ⟨hi.walk t ht, hi.simple t ht, hi.supported t ht⟩,
    crossing_none rel nodes complete _ hc⟩

/-- Instrument the actual sequential predicate scan by its number of queries. -/
def countedFind {A : Type*} (p : A → Bool) : List A → Option A × ℕ
  | [] => (none, 0)
  | a :: rest => if p a then (some a, 1) else
      let r := countedFind p rest
      (r.1, r.2 + 1)

theorem countedFind_spec {A : Type*} (p : A → Bool) (xs : List A) :
    (countedFind p xs).1 = xs.find? p ∧ (countedFind p xs).2 ≤ xs.length := by
  induction xs with
  | nil => simp [countedFind]
  | cons a xs ih =>
      by_cases ha : p a
      · simp [countedFind, ha]
      · simp only [countedFind, ha, Bool.false_eq_true, ite_false, List.find?_cons,
          List.length_cons]
        exact ⟨ih.1, by omega⟩

/-- Relation queries of exactly the scans performed by `explore`. -/
def exploreQueries (rel : V → V → Prop) [DecidableRel rel] (nodes : List V) :
    ℕ → State V → ℕ
  | 0, _ => 0
  | fuel + 1, q =>
      let inspected := (countedFind
        (fun p : V × V => decide (p.1 ∈ q.seen ∧ p.2 ∉ q.seen ∧ rel p.1 p.2))
        (nodes.product nodes)).2
      match crossing rel nodes q.seen with
      | none => inspected
      | some a => inspected + exploreQueries rel nodes fuel (extend q a)

/-- The entire reachability search makes at most n m² relation queries, for n
rounds and a supplied list of m vertices. -/
theorem exploreQueries_le (rel : V → V → Prop) [DecidableRel rel]
    (nodes : List V) (fuel : ℕ) (q : State V) :
    exploreQueries rel nodes fuel q ≤ fuel * nodes.length ^ 2 := by
  induction fuel generalizing q with
  | zero => simp [exploreQueries]
  | succ fuel ih =>
      have hh := (countedFind_spec
        (fun p : V × V => decide (p.1 ∈ q.seen ∧ p.2 ∉ q.seen ∧ rel p.1 p.2))
        (nodes.product nodes)).2
      have hlen : (nodes.product nodes).length = nodes.length * nodes.length :=
        List.length_product nodes nodes
      rw [hlen] at hh
      simp only [exploreQueries]
      split
      · nlinarith
      · rename_i a _
        have hr := ih (extend q a)
        nlinarith

/-- Returned simple routes have at most n-1 arcs. -/
theorem invariant_route_length [Fintype V] (rel : V → V → Prop) (s : V)
    (q : State V) (hq : Invariant rel s q) (v : V) (hv : v ∈ q.seen) :
    (q.route v).length + 1 ≤ Fintype.card V := by
  have hh := (hq.simple v hv).length_le_card
  simpa [IsSimple, vertices] using hh

end WeightedMIS.MaxFlowReach
