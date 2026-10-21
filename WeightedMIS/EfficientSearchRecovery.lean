module

public import WeightedMIS.EfficientSearchCorrectness

/-!
# Recovery of the actual predecessor path

The search stores reverse paths by shared list extension.  This file proves
that the stored list itself is a valid walk with exactly the reported cost;
the existential witness used by Dijkstra correctness is not substituted for
the algorithm's output.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch

variable {Label : Type*} {vbits cbits : ℕ}

abbrev RawArc (Label : Type*) (vbits cbits : ℕ) :=
  Bits vbits × Arc Label vbits cbits

abbrev rawSource (edge : RawArc Label vbits cbits) := edge.1
abbrev rawTarget (edge : RawArc Label vbits cbits) := edge.2.target
abbrev rawWeight (edge : RawArc Label vbits cbits) := edge.2.weight.value

structure PathEvidence (graph : Graph Label vbits cbits) (source target : Bits vbits)
    (reversePath : Trace Label vbits cbits) (distance : Bits cbits) : Prop where
  member : ∀ edge ∈ reversePath, edge ∈ graph.elements
  walk : ShortestPath.IsWalk rawSource rawTarget source target reversePath.reverse
  cost : Dijkstra.cost rawWeight reversePath.reverse = distance.value

def QueueEvidence (graph : Graph Label vbits cbits) (source : Bits vbits)
    (queue : Queue Label vbits cbits) : Prop :=
  ∀ item ∈ queue.elements,
    PathEvidence graph source item.2.vertex item.2.reversePath item.1

def SettledEvidence (graph : Graph Label vbits cbits) (source : Bits vbits)
    (settled : Settled Label vbits cbits) : Prop :=
  ∀ item ∈ settled.elements,
    PathEvidence graph source item.1 item.2.2 item.2.1

theorem PathEvidence.extend {graph : Graph Label vbits cbits} {source vertex : Bits vbits}
    {path : Trace Label vbits cbits} {distance : Bits cbits}
    (h : PathEvidence graph source vertex path distance) (edge : Arc Label vbits cbits)
    (he : (vertex, edge) ∈ graph.elements) (hsafe : (Bits.add distance edge.weight).2.1 = false) :
    PathEvidence graph source edge.target ((vertex, edge) :: path)
      (Bits.add distance edge.weight).1 := by
  constructor
  · intro e hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact he
    · exact h.member e hm
  · simp only [List.reverse_cons]
    exact ShortestPath.walk_append rawSource rawTarget h.walk ⟨rfl, rfl⟩
  · simp [Dijkstra.cost_append, h.cost, Bits.add_value_of_no_overflow _ _ hsafe]

theorem relax_evidence (graph : Graph Label vbits cbits) (source : Bits vbits)
    (candidate : Candidate Label vbits cbits) (distance : Bits cbits)
    (edges : List (Arc Label vbits cbits)) (queue : Queue Label vbits cbits)
    (hc : PathEvidence graph source candidate.vertex candidate.reversePath distance)
    (he : ∀ edge ∈ edges, (candidate.vertex, edge) ∈ graph.elements)
    (hq : QueueEvidence graph source queue)
    (hsafe : (relax candidate distance edges queue).2.1 = false) :
    QueueEvidence graph source (relax candidate distance edges queue).1 := by
  induction edges generalizing queue with
  | nil => exact hq
  | cons edge rest ih =>
    change ((Bits.add distance edge.weight).2.1 ||
      (relax candidate distance rest
        (Radix.insert (Bits.add distance edge.weight).1
          ⟨edge.target, (candidate.vertex, edge) :: candidate.reversePath⟩ queue).1).2.1) = false at hsafe
    have hs := Bool.or_eq_false_iff.mp hsafe
    have hqi : QueueEvidence graph source
        (Radix.insert (Bits.add distance edge.weight).1
          ⟨edge.target, (candidate.vertex, edge) :: candidate.reversePath⟩ queue).1 := by
      intro item hi
      rcases (Radix.mem_insert _ _ _ _).mp hi with rfl | hi
      · exact hc.extend edge (he edge (by simp)) hs.1
      · exact hq item hi
    exact ih _ (fun e hm => he e (List.mem_cons_of_mem edge hm)) hqi hs.2

theorem run_evidence (graph : Graph Label vbits cbits) (source : Bits vbits) (fuel : ℕ)
    (queue : Queue Label vbits cbits) (settled : Settled Label vbits cbits)
    (hq : QueueEvidence graph source queue) (hs : SettledEvidence graph source settled)
    (hsafe : (run graph fuel queue settled).status ≠ .overflow) :
    QueueEvidence graph source (run graph fuel queue settled).queue ∧
      SettledEvidence graph source (run graph fuel queue settled).settled := by
  induction fuel generalizing queue settled with
  | zero => exact ⟨hq, hs⟩
  | succ fuel ih =>
    cases hp : (Radix.pop queue).1 with
    | none => simpa [run, hp] using And.intro hq hs
    | some item =>
      obtain ⟨distance, candidate, queue'⟩ := item
      have he := Radix.pop_elements queue hp
      have hc := hq (distance, candidate) (by rw [he]; exact List.mem_cons_self)
      have hq' : QueueEvidence graph source queue' := by
        intro item hm
        exact hq item (by rw [he]; exact List.mem_cons_of_mem _ hm)
      cases hk : (Radix.lookup candidate.vertex settled).1 with
      | cons x xs =>
        have hs' : (run graph fuel queue' settled).status ≠ .overflow := by
          simpa [run, hp, hk] using hsafe
        simpa [run, hp, hk] using ih queue' settled hq' hs hs'
      | nil =>
        have hstored : SettledEvidence graph source
            (Radix.insert candidate.vertex (distance, candidate.reversePath) settled).1 := by
          intro item hm
          rcases (Radix.mem_insert _ _ _ _).mp hm with rfl | hm
          · exact hc
          · exact hs item hm
        cases hov : (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').2.1
        · have hrelax := relax_evidence graph source candidate distance
            (Radix.lookup candidate.vertex graph).1 queue' hc
            (fun edge hm => (Radix.mem_lookup _ _ _).mp hm) hq' hov
          have hs' : (run graph fuel
              (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').1
              (Radix.insert candidate.vertex (distance, candidate.reversePath) settled).1).status ≠
                .overflow := by simpa [run, hp, hk, hov] using hsafe
          simpa [run, hp, hk, hov] using ih _ _ hrelax hstored hs'
        · simp [run, hp, hk, hov] at hsafe

theorem initial_evidence (graph : Graph Label vbits cbits) (source : Bits vbits) :
    QueueEvidence graph source (initialQueue source) := by
  intro item hm
  simp only [initialQueue, Radix.mem_insert, Radix.elements, List.not_mem_nil, or_false] at hm
  subst item
  exact ⟨by simp, rfl, by simp⟩

theorem solve_evidence (graph : Graph Label vbits cbits) (source : Bits vbits)
    (weightBound : ℕ) (hg : GraphBound graph weightBound)
    (hwidth : (graph.elements.length + 2) * weightBound < 2 ^ cbits) :
    SettledEvidence graph source (solve graph source).settled := by
  have hs := solve_no_overflow graph source weightBound hg hwidth
  simp only [solve, Radix.countEntries_value] at hs ⊢
  exact (run_evidence graph source _ _ _ (initial_evidence graph source)
    (by intro item hm; exact (List.not_mem_nil hm).elim) hs).2

/-- Lookup the stored distance and reverse predecessor chain. -/
def lookupResult (result : Result Label vbits cbits) (target : Bits vbits) :
    Option (Bits cbits × Trace Label vbits cbits) :=
  (Radix.lookup target result.settled).1.head?

/-- The path returned by the actual algorithm is valid and globally optimal
among all directed walks of the supplied finite graph. -/
theorem solve_recovers_minimum (graph : Graph Label vbits cbits) (source target : Bits vbits)
    (weightBound : ℕ) (hg : GraphBound graph weightBound)
    (hwidth : (graph.elements.length + 2) * weightBound < 2 ^ cbits)
    (hreach : ∃ path, ShortestPath.IsWalk (arcSource (graph := graph)) arcTarget source target path) :
    ∃ distance reversePath,
      lookupResult (solve graph source) target = some (distance, reversePath) ∧
      PathEvidence graph source target reversePath distance ∧
      ∀ path, ShortestPath.IsWalk (arcSource (graph := graph)) arcTarget source target path →
        distance.value ≤ Dijkstra.cost arcWeight path := by
  obtain ⟨distanceValue, hd, hmin⟩ :=
    solve_distances_exact graph source target weightBound hg hwidth hreach
  have he := solve_evidence graph source weightBound hg hwidth
  cases hl : (Radix.lookup target (solve graph source).settled).1 with
  | nil => simp [distances, hl] at hd
  | cons item rest =>
    have hvalue : item.1.value = distanceValue := by simpa [distances, hl] using hd
    refine ⟨item.1, item.2, ?_, ?_, ?_⟩
    · simp [lookupResult, hl]
    · exact he (target, item) ((Radix.mem_lookup _ _ _).mp (by rw [hl]; exact List.mem_cons_self))
    · simpa [hvalue] using hmin.2

def QueueDepth (queue : Queue Label vbits cbits) (fuel bound : ℕ) : Prop :=
  ∀ item ∈ queue.elements, item.2.reversePath.length + fuel ≤ bound

def SettledDepth (settled : Settled Label vbits cbits) (bound : ℕ) : Prop :=
  ∀ item ∈ settled.elements, item.2.2.length < bound

theorem relax_depth (candidate : Candidate Label vbits cbits) (distance : Bits cbits)
    (edges : List (Arc Label vbits cbits)) (queue : Queue Label vbits cbits)
    (fuel bound : ℕ) (hc : candidate.reversePath.length + (fuel + 1) ≤ bound)
    (hq : QueueDepth queue fuel bound) :
    QueueDepth (relax candidate distance edges queue).1 fuel bound := by
  induction edges generalizing queue with
  | nil => exact hq
  | cons edge rest ih =>
    apply ih
    intro item hm
    rcases (Radix.mem_insert _ _ _ _).mp hm with rfl | hm
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
    · exact hq item hm

theorem run_stored_depth (graph : Graph Label vbits cbits) (fuel bound : ℕ)
    (queue : Queue Label vbits cbits) (settled : Settled Label vbits cbits)
    (hq : QueueDepth queue fuel bound) (hs : SettledDepth settled bound) :
    SettledDepth (run graph fuel queue settled).settled bound := by
  induction fuel generalizing queue settled with
  | zero => exact hs
  | succ fuel ih =>
    cases hp : (Radix.pop queue).1 with
    | none => simpa [run, hp] using hs
    | some item =>
      obtain ⟨distance, candidate, queue'⟩ := item
      have he := Radix.pop_elements queue hp
      have hc := hq (distance, candidate) (by rw [he]; exact List.mem_cons_self)
      have hq' : QueueDepth queue' fuel bound := by
        intro item hm
        have hi := hq item (by rw [he]; exact List.mem_cons_of_mem _ hm)
        omega
      cases hk : (Radix.lookup candidate.vertex settled).1 with
      | cons x xs => simpa [run, hp, hk] using ih queue' settled hq' hs
      | nil =>
        have hstored : SettledDepth
            (Radix.insert candidate.vertex (distance, candidate.reversePath) settled).1 bound := by
          intro item hm
          rcases (Radix.mem_insert _ _ _ _).mp hm with rfl | hm
          · dsimp at hc ⊢
            omega
          · exact hs item hm
        have hexpanded := relax_depth candidate distance
          (Radix.lookup candidate.vertex graph).1 queue' fuel bound hc hq'
        cases hov : (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').2.1
        · simpa [run, hp, hk, hov] using ih _ _ hexpanded hstored
        · simpa [run, hp, hk, hov] using hstored

theorem solve_stored_depth (graph : Graph Label vbits cbits) (source : Bits vbits) :
    SettledDepth (solve graph source).settled (graph.elements.length + 2) := by
  simp only [solve, Radix.countEntries_value]
  apply run_stored_depth
  · intro item hm
    simp only [ Radix.mem_insert, Radix.elements, List.not_mem_nil, or_false] at hm
    subst item
    simp
  · intro item hm
    exact (List.not_mem_nil hm).elim

/-- Tail-recursive reversal with one charged list-cell step per input cell. -/
def reverseCount {α : Type*} : List α → List α → List α × ℕ
  | [], acc => (acc, 1)
  | x :: xs, acc =>
      let result := reverseCount xs (x :: acc)
      (result.1, result.2 + 1)

theorem reverseCount_value {α : Type*} (xs acc : List α) :
    (reverseCount xs acc).1 = xs.reverse ++ acc := by
  induction xs generalizing acc <;> simp [reverseCount, *, List.append_assoc]

theorem reverseCount_steps {α : Type*} (xs acc : List α) :
    (reverseCount xs acc).2 = xs.length + 1 := by
  induction xs generalizing acc <;> simp [reverseCount, *]

/-- Recover a forward path, accounting for dictionary lookup and reversal. -/
def recover (result : Result Label vbits cbits) (target : Bits vbits) :
    Option (Bits cbits × Trace Label vbits cbits) × ℕ :=
  let found := Radix.lookup target result.settled
  match found.1 with
  | [] => (none, found.2 + 1)
  | (distance, path) :: _ =>
      let reversed := reverseCount path []
      (some (distance, reversed.1), found.2 + reversed.2 + 1)

theorem recover_lookup (result : Result Label vbits cbits) (target : Bits vbits)
    (distance : Bits cbits) (path : Trace Label vbits cbits)
    (h : lookupResult result target = some (distance, path)) :
    (recover result target).1 = some (distance, path.reverse) := by
  cases he : (Radix.lookup target result.settled).1 with
  | nil => simp [lookupResult, he] at h
  | cons item rest =>
    have hi : item = (distance, path) := by simpa [lookupResult, he] using h
    subst item
    simp [recover, he, reverseCount_value]

theorem solve_recovery_work (graph : Graph Label vbits cbits) (source target : Bits vbits) :
    (recover (solve graph source) target).2 ≤ vbits + graph.elements.length + 5 := by
  have hl := Radix.lookup_steps target (solve graph source).settled
  cases he : (Radix.lookup target (solve graph source).settled).1 with
  | nil => simp [recover, he]; omega
  | cons item rest =>
    have hm : (target, item) ∈ (solve graph source).settled.elements :=
      (Radix.mem_lookup _ _ _).mp (by rw [he]; exact List.mem_cons_self)
    have hd := solve_stored_depth graph source (target, item) hm
    simp only [recover, he, reverseCount_steps]
    dsimp at hd
    omega

/-- Correct forward output and a near-linear structural-work bound for the
entire search, including initialization and predecessor reconstruction. -/
theorem solve_specification (graph : Graph Label vbits cbits) (source target : Bits vbits)
    (weightBound : ℕ) (hcanonical : graph.canonical) (hg : GraphBound graph weightBound)
    (hwidth : (graph.elements.length + 2) * weightBound < 2 ^ cbits)
    (hreach : ∃ path, ShortestPath.IsWalk (arcSource (graph := graph)) arcTarget source target path) :
    ∃ distance path,
      (recover (solve graph source) target).1 = some (distance, path) ∧
      (∀ edge ∈ path, edge ∈ graph.elements) ∧
      ShortestPath.IsWalk rawSource rawTarget source target path ∧
      Dijkstra.cost rawWeight path = distance.value ∧
      (∀ other, ShortestPath.IsWalk (arcSource (graph := graph)) arcTarget source target other →
        distance.value ≤ Dijkstra.cost arcWeight other) ∧
      (solve graph source).work + (recover (solve graph source) target).2 ≤
        (5 * cbits + 6 * vbits + 26) * (graph.elements.length + 1) + 11 := by
  obtain ⟨distance, reversePath, hlookup, hp, hmin⟩ :=
    solve_recovers_minimum graph source target weightBound hg hwidth hreach
  refine ⟨distance, reversePath.reverse, recover_lookup _ _ _ _ hlookup, ?_,
    hp.walk, hp.cost, hmin, ?_⟩
  · intro edge hm
    exact hp.member edge (List.mem_reverse.mp hm)
  · have hs := solve_work_le graph source hcanonical
    have hr := solve_recovery_work graph source target
    nlinarith

end WeightedMIS.EfficientSearch
