module

public import WeightedMIS.RegisterRouteLookup
public import WeightedMIS.ResidualCrossingRefinement
public import WeightedMIS.MaxFlowListReach

/-! # Word-list reachability with materialized reverse-route association lists -/

@[expose] public section

namespace WeightedMIS.ResidualListReach

open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords

structure State (n b : ℕ) where
  seen : List (Bits n)
  routes : List (RegisterRouteLookup.Route n b)

def extend {n b : ℕ} (q : State n b) (d : Bits b) (a : Arc n b) : State n b :=
  ⟨a.target :: q.seen,
    (a.target, {a with capacity := d} :: RegisterRouteLookup.lookup a.source q.routes) :: q.routes⟩

def initial {n b : ℕ} (s : Bits n) : State n b := ⟨[s], [(s, [])]⟩

def explore {n b : ℕ} (table : List (Arc n b)) (d : Bits b) : ℕ → State n b → State n b
  | 0, q => q
  | fuel + 1, q => match RegisterResidualCrossing.crossing q.seen d table with
    | none => q
    | some a => explore table d fuel (extend q d a)

theorem explore_lengths {n b : ℕ} (table : List (Arc n b)) (d : Bits b)
    (fuel : ℕ) (q : State n b) :
    (explore table d fuel q).seen.length ≤ q.seen.length + fuel ∧
      (explore table d fuel q).routes.length ≤ q.routes.length + fuel := by
  induction fuel generalizing q with
  | zero => simp [explore]
  | succ fuel ih =>
    simp only [explore]
    split
    · constructor <;> omega
    · rename_i a _
      have hh := ih (extend q d a)
      simp only [extend, List.length_cons] at hh ⊢
      constructor <;> omega


/-- All stored paths have a common explicit length bound. -/
def PathsBound {n b : ℕ} (q : State n b) (L : ℕ) : Prop :=
  ∀ entry ∈ q.routes, entry.2.length ≤ L

theorem lookup_length {n b : ℕ} (routes : List (RegisterRouteLookup.Route n b))
    (L : ℕ) (hbound : ∀ entry ∈ routes, entry.2.length ≤ L) (query : Bits n) :
    (RegisterRouteLookup.lookup query routes).length ≤ L := by
  induction routes with
  | nil => simp [RegisterRouteLookup.lookup]
  | cons entry routes ih =>
    simp only [RegisterRouteLookup.lookup]
    split
    · exact hbound entry (by simp)
    · exact ih (fun e he => hbound e (List.mem_cons_of_mem entry he))

theorem extend_pathsBound {n b : ℕ} (q : State n b) (L : ℕ) (hq : PathsBound q L)
    (d : Bits b) (a : Arc n b) : PathsBound (extend q d a) (L + 1) := by
  intro entry hentry
  simp only [extend, List.mem_cons] at hentry
  rcases hentry with rfl | hentry
  · have hl := lookup_length q.routes L hq a.source
    simp only [List.length_cons]
    omega
  · exact (hq entry hentry).trans (by omega)

theorem explore_pathsBound {n b : ℕ} (table : List (Arc n b)) (d : Bits b)
    (fuel : ℕ) (q : State n b) (L : ℕ) (hq : PathsBound q L) :
    PathsBound (explore table d fuel q) (L + fuel) := by
  induction fuel generalizing q L with
  | zero => simpa [explore] using hq
  | succ fuel ih =>
    simp only [explore]
    split
    · intro entry he
      exact (hq entry he).trans (by omega)
    · rename_i a _
      have hh := ih (extend q d a) (L + 1) (extend_pathsBound q L hq d a)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem search_lookup_length {n b : ℕ} (table : List (Arc n b)) (d : Bits b)
    (nodes : List (Bits n)) (source query : Bits n) :
    (RegisterRouteLookup.lookup query (explore table d nodes.length (initial source)).routes).length ≤ nodes.length := by
  have hi : PathsBound (initial (b := b) source) 0 := by
    intro entry he
    simp [initial] at he
    simp [he]
  have hh := explore_pathsBound table d nodes.length (initial source) 0 hi
  have hb : PathsBound (explore table d nodes.length (initial source)) nodes.length := by
    simpa only [Nat.zero_add] using hh
  exact lookup_length _ _ hb query

section Refinement

open ResidualCrossingRefinement
variable {V : Type*} [Fintype V] [DecidableEq V] {n b : ℕ}

def encodeRoutes (enc : V → Bits n) (d : Bits b) (routes : MaxFlowListReach.Routes V) :
    List (RegisterRouteLookup.Route n b) :=
  routes.map fun entry => (enc entry.1, entry.2.map (encodeArc enc (fun _ _ => d)))

def encodeState (enc : V → Bits n) (d : Bits b) (q : MaxFlowListReach.State V) : State n b :=
  ⟨q.seen.map enc, encodeRoutes enc d q.routes⟩

theorem lookup_encoded (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value)) (d : Bits b)
    (routes : MaxFlowListReach.Routes V) (u : V) :
    RegisterRouteLookup.lookup (enc u) (encodeRoutes enc d routes) =
      (MaxFlowListReach.lookup routes u).map (encodeArc enc (fun _ _ => d)) := by
  induction routes with
  | nil => rfl
  | cons entry routes ih =>
    have he : (enc u).value = (enc entry.1).value ↔ u = entry.1 :=
      ⟨fun h => hinj h, congrArg (fun v => (enc v).value)⟩
    simp only [encodeRoutes, List.map_cons, RegisterRouteLookup.lookup,
      MaxFlowListReach.lookup, he]
    split
    · rfl
    · exact ih

theorem encode_initial (enc : V → Bits n) (d : Bits b) (s : V) :
    encodeState enc d (MaxFlowListReach.initial s) = initial (enc s) := rfl

theorem extend_encoded (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value)) (d : Bits b)
    (caps : V → V → Bits b) (q : MaxFlowListReach.State V) (a : V × V) :
    extend (encodeState enc d q) d (encodeArc enc caps a) =
      encodeState enc d (MaxFlowListReach.extend q a) := by
  simp only [extend, encodeState, encodeRoutes, MaxFlowListReach.extend, List.map_cons, encodeArc]
  have hl := lookup_encoded enc hinj d q.routes a.1
  simp only [encodeRoutes] at hl
  rw [hl]

/-- Every concrete word-list discovery matches the original verified residual
search, including the first matching route and the full stored path. -/
theorem explore_encoded (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (caps : V → V → Bits b) (c : V → V → ℕ) (s t : V) (f : V → V → ℤ)
    (hf : MaxFlowCore.Feasible c s t f)
    (hcap : ∀ u v, (caps u v).value = MaxFlowResidual.matrix c f u v)
    (nodes : List V) (d : Bits b) (fuel : ℕ) (q : MaxFlowListReach.State V) :
    explore ((nodes.product nodes).map (encodeArc enc caps)) d fuel (encodeState enc d q) =
      encodeState enc d (MaxFlowListReach.explore (MaxFlowScaling.relation c f d.value) nodes fuel q) := by
  induction fuel generalizing q with
  | zero => rfl
  | succ fuel ih =>
    simp only [explore, MaxFlowListReach.explore]
    change (match RegisterResidualCrossing.crossing (q.seen.map enc) d
        ((nodes.product nodes).map (encodeArc enc caps)) with
      | none => encodeState enc d q
      | some a => explore _ d fuel (extend (encodeState enc d q) d a)) = _
    rw [crossing_list_exact enc hinj caps c s t f hf hcap nodes q.seen d]
    cases he : MaxFlowReach.crossing (MaxFlowScaling.relation c f d.value) nodes q.seen.toFinset with
    | none => rfl
    | some a =>
      simp only [Option.map_some]
      rw [extend_encoded enc hinj, ih]

end Refinement
end WeightedMIS.ResidualListReach
