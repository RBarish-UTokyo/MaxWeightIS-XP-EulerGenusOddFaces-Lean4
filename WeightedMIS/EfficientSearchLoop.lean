module

public import WeightedMIS.EfficientSearchArithmetic

/-!
# Executable sparse lazy Dijkstra loop

Adjacency lists, settled labels and the priority queue are binary tries.  Every
queue item contains a reverse path, extended by one shared list constructor.
The algorithm checks overflow instead of silently accepting modular distances.
The work counter charges trie inspections, full-adder cells and loop control;
it is an explicit structural cost semantics, not a Turing-machine simulation.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch

variable {Label : Type*} {vbits cbits : ℕ}

structure Arc (Label : Type*) (vbits cbits : ℕ) where
  target : Bits vbits
  weight : Bits cbits
  label : Label

abbrev Trace (Label : Type*) (vbits cbits : ℕ) :=
  List (Bits vbits × Arc Label vbits cbits)

structure Candidate (Label : Type*) (vbits cbits : ℕ) where
  vertex : Bits vbits
  reversePath : Trace Label vbits cbits

abbrev Queue (Label : Type*) (vbits cbits : ℕ) :=
  Radix (Candidate Label vbits cbits) cbits

abbrev Settled (Label : Type*) (vbits cbits : ℕ) :=
  Radix (Bits cbits × Trace Label vbits cbits) vbits

abbrev Graph (Label : Type*) (vbits cbits : ℕ) :=
  Radix (Arc Label vbits cbits) vbits

/-- Insert one outgoing candidate per adjacency-list entry. -/
def relax (u : Candidate Label vbits cbits) (distance : Bits cbits) :
    List (Arc Label vbits cbits) → Queue Label vbits cbits →
      Queue Label vbits cbits × Bool × ℕ
  | [], queue => (queue, false, 1)
  | edge :: rest, queue =>
      let added := Bits.add distance edge.weight
      let next : Candidate Label vbits cbits :=
        ⟨edge.target, (u.vertex, edge) :: u.reversePath⟩
      let inserted := Radix.insert added.1 next queue
      let result := relax u distance rest inserted.1
      (result.1, added.2.1 || result.2.1,
        added.2.2 + inserted.2 + result.2.2 + 1)

theorem relax_steps (u : Candidate Label vbits cbits) (distance : Bits cbits)
    (edges : List (Arc Label vbits cbits)) (queue : Queue Label vbits cbits) :
    (relax u distance edges queue).2.2 = (2 * cbits + 3) * edges.length + 1 := by
  induction edges generalizing queue with
  | nil => simp [relax]
  | cons e es ih =>
    simp only [relax, Bits.add_steps, Radix.insert_steps, ih, List.length_cons]
    ring

theorem relax_size (u : Candidate Label vbits cbits) (distance : Bits cbits)
    (edges : List (Arc Label vbits cbits)) (queue : Queue Label vbits cbits) :
    (Radix.elements (relax u distance edges queue).1).length =
      (Radix.elements queue).length + edges.length := by
  induction edges generalizing queue with
  | nil => simp [relax]
  | cons e es ih => simp [relax, ih, Radix.insert_size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem relax_canonical (u : Candidate Label vbits cbits) (distance : Bits cbits)
    (edges : List (Arc Label vbits cbits)) (queue : Queue Label vbits cbits)
    (hq : queue.canonical) : (relax u distance edges queue).1.canonical := by
  induction edges generalizing queue with
  | nil => exact hq
  | cons e es ih =>
    exact ih _ (Radix.insert_canonical _ _ _ hq)

inductive Status
  | finished
  | exhausted
  | overflow
  deriving DecidableEq, Repr

structure Result (Label : Type*) (vbits cbits : ℕ) where
  status : Status
  settled : Settled Label vbits cbits
  queue : Queue Label vbits cbits
  work : ℕ

/-- Fuel is a bound on queue extractions.  A stale duplicate is discarded;
a fresh vertex is settled once and its outgoing adjacency list is expanded. -/
def run (graph : Graph Label vbits cbits) : ℕ →
    Queue Label vbits cbits → Settled Label vbits cbits → Result Label vbits cbits
  | 0, queue, settled => ⟨.exhausted, settled, queue, 1⟩
  | fuel + 1, queue, settled =>
      let removed := Radix.pop queue
      match removed.1 with
      | none => ⟨.finished, settled, queue, removed.2 + 1⟩
      | some (distance, candidate, queue') =>
          let known := Radix.lookup candidate.vertex settled
          match known.1 with
          | _ :: _ =>
              let result := run graph fuel queue' settled
              { result with work := removed.2 + known.2 + result.work + 1 }
          | [] =>
              let stored := Radix.insert candidate.vertex
                (distance, candidate.reversePath) settled
              let outgoing := Radix.lookup candidate.vertex graph
              let expanded := relax candidate distance outgoing.1 queue'
              if expanded.2.1 then
                ⟨.overflow, stored.1, expanded.1,
                  removed.2 + known.2 + stored.2 + outgoing.2 + expanded.2.2 + 1⟩
              else
                let result := run graph fuel expanded.1 stored.1
                { result with work := removed.2 + known.2 + stored.2 + outgoing.2 +
                    expanded.2.2 + result.work + 1 }

/-- Unexpanded adjacency entries, counted with multiplicity. -/
def remaining (graph : Graph Label vbits cbits) (settled : Settled Label vbits cbits) : ℕ :=
  (graph.elements.filter (fun edge => (Radix.lookup edge.1 settled).1.isEmpty)).length

def potential (graph : Graph Label vbits cbits) (queue : Queue Label vbits cbits)
    (settled : Settled Label vbits cbits) : ℕ :=
  queue.elements.length + remaining graph settled

theorem remaining_le (graph : Graph Label vbits cbits)
    (settled : Settled Label vbits cbits) : remaining graph settled ≤ graph.elements.length :=
  List.length_filter_le _ _

theorem remaining_insert (graph : Graph Label vbits cbits)
    (settled : Settled Label vbits cbits) (vertex : Bits vbits)
    (value : Bits cbits × Trace Label vbits cbits)
    (hfresh : (Radix.lookup vertex settled).1 = []) :
    remaining graph (Radix.insert vertex value settled).1 +
      (Radix.lookup vertex graph).1.length = remaining graph settled := by
  rw [Radix.lookup_length]
  unfold remaining
  have key_test (key : Bits vbits) :
      (Radix.lookup key (Radix.insert vertex value settled).1).1.isEmpty =
        (!(key == vertex) && (Radix.lookup key settled).1.isEmpty) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.isEmpty_iff, Bool.and_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne, Radix.lookup_insert_empty]
  simp only [key_test]
  induction graph.elements with
  | nil => simp
  | cons edge rest ih =>
    by_cases heq : edge.1 = vertex
    · simp [heq, hfresh]
      omega
    · simp [heq, List.filter_cons]
      split <;> simp_all
      omega

theorem fresh_potential_decreases (graph : Graph Label vbits cbits)
    (queue queue' : Queue Label vbits cbits) (settled : Settled Label vbits cbits)
    (distance : Bits cbits) (candidate : Candidate Label vbits cbits)
    (hpop : (Radix.pop queue).1 = some (distance, candidate, queue'))
    (hfresh : (Radix.lookup candidate.vertex settled).1 = []) :
    potential graph
        (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').1
        (Radix.insert candidate.vertex (distance, candidate.reversePath) settled).1 + 1 =
      potential graph queue settled := by
  have hp := Radix.pop_elements queue hpop
  have hr := remaining_insert graph settled candidate.vertex
    (distance, candidate.reversePath) hfresh
  simp only [potential, relax_size, hp, List.length_cons]
  omega

theorem stale_potential_decreases (graph : Graph Label vbits cbits)
    (queue queue' : Queue Label vbits cbits) (settled : Settled Label vbits cbits)
    (distance : Bits cbits) (candidate : Candidate Label vbits cbits)
    (hpop : (Radix.pop queue).1 = some (distance, candidate, queue')) :
    potential graph queue' settled + 1 = potential graph queue settled := by
  simp [potential, Radix.pop_elements queue hpop, Nat.add_comm, Nat.add_left_comm]

/-- Enough extraction fuel prevents exhaustion, including the final empty-queue
inspection.  Overflow is a separate, explicitly reported result. -/
theorem run_not_exhausted (graph : Graph Label vbits cbits) (fuel : ℕ)
    (queue : Queue Label vbits cbits) (settled : Settled Label vbits cbits)
    (hq : queue.canonical) (hfuel : potential graph queue settled < fuel) :
    (run graph fuel queue settled).status ≠ .exhausted := by
  induction fuel generalizing queue settled with
  | zero => omega
  | succ fuel ih =>
    cases hp : (Radix.pop queue).1 with
    | none => simp [run, hp]
    | some item =>
      obtain ⟨distance, candidate, queue'⟩ := item
      have hq' := Radix.pop_canonical queue hq hp
      cases hk : (Radix.lookup candidate.vertex settled).1 with
      | cons x xs =>
        have hd := stale_potential_decreases graph queue queue' settled distance candidate hp
        simpa [run, hp, hk] using ih queue' settled hq' (by omega)
      | nil =>
        have hd := fresh_potential_decreases graph queue queue' settled distance candidate hp hk
        have hc := relax_canonical candidate distance
          (Radix.lookup candidate.vertex graph).1 queue' hq'
        cases hov : (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').2.1
        · simpa [run, hp, hk, hov] using ih _ _ hc (by omega)
        · simp [run, hp, hk, hov]

/-- The amortized structural-work budget pays each outgoing entry once, when
its source is settled, and each queue extraction once. -/
def budget (graph : Graph Label vbits cbits) (queue : Queue Label vbits cbits)
    (settled : Settled Label vbits cbits) : ℕ :=
  (2 * cbits + 3 * vbits + 12) * potential graph queue settled +
    (2 * cbits + 3) * remaining graph settled + 2

theorem run_work_le (graph : Graph Label vbits cbits) (fuel : ℕ)
    (queue : Queue Label vbits cbits) (settled : Settled Label vbits cbits)
    (hq : queue.canonical) : (run graph fuel queue settled).work ≤ budget graph queue settled := by
  induction fuel generalizing queue settled with
  | zero => simp [run, budget]
  | succ fuel ih =>
    cases hp : (Radix.pop queue).1 with
    | none =>
      have he := Radix.canonical_empty queue hq ((Radix.pop_none queue).mp hp)
      subst queue
      simp [run, Radix.pop, budget]
    | some item =>
      obtain ⟨distance, candidate, queue'⟩ := item
      have hq' := Radix.pop_canonical queue hq hp
      have hpop := Radix.pop_steps queue hq
      have hknown := Radix.lookup_steps candidate.vertex settled
      cases hk : (Radix.lookup candidate.vertex settled).1 with
      | cons x xs =>
        have hd := stale_potential_decreases graph queue queue' settled distance candidate hp
        have hih := ih queue' settled hq'
        simp only [run, hp, hk]
        unfold budget at *
        nlinarith
      | nil =>
        have hd := fresh_potential_decreases graph queue queue' settled distance candidate hp hk
        have hr := remaining_insert graph settled candidate.vertex
          (distance, candidate.reversePath) hk
        have hc := relax_canonical candidate distance
          (Radix.lookup candidate.vertex graph).1 queue' hq'
        have hout := Radix.lookup_steps candidate.vertex graph
        have hstored := Radix.insert_steps candidate.vertex
          (distance, candidate.reversePath) settled
        have hrelax := relax_steps candidate distance
          (Radix.lookup candidate.vertex graph).1 queue'
        have hih := ih _ (Radix.insert candidate.vertex
          (distance, candidate.reversePath) settled).1 hc
        cases hov : (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').2.1
        · simp only [run, hp, hk, hov, Bool.false_eq_true, ↓reduceIte]
          unfold budget at *
          nlinarith
        · simp only [run, hp, hk, hov, ↓reduceIte]
          unfold budget at *
          nlinarith

/-- Initialize the queue with the zero-cost, empty source path. -/
def initialQueue (source : Bits vbits) : Queue Label vbits cbits :=
  (Radix.insert (Bits.zero cbits) ⟨source, []⟩ .empty).1

def solve (graph : Graph Label vbits cbits) (source : Bits vbits) :
    Result Label vbits cbits :=
  let counted := Radix.countEntries graph
  let initialized := Radix.insert (Bits.zero cbits) (Candidate.mk source []) .empty
  let result := run graph (counted.1 + 2) initialized.1 .empty
  { result with work := counted.2 + initialized.2 + result.work + 2 }

theorem solve_not_exhausted (graph : Graph Label vbits cbits) (source : Bits vbits) :
    (solve graph source).status ≠ .exhausted := by
  simp only [solve, Radix.countEntries_value]
  apply run_not_exhausted
  · exact Radix.insert_canonical _ _ _ trivial
  · simp [potential, Radix.insert_size, remaining, Radix.elements,
      Radix.lookup]
    omega

/-- Linear dependence on the number of sparse adjacency entries, with explicit
polynomial dependence on the widths of stored vertex and cost words. -/
theorem solve_work_le (graph : Graph Label vbits cbits) (source : Bits vbits) :
    graph.canonical → (solve graph source).work ≤
      (5 * cbits + 5 * vbits + 20) * (graph.elements.length + 1) + 6 := by
  intro hg
  have h := run_work_le graph (graph.elements.length + 2) (initialQueue source) .empty
    (Radix.insert_canonical _ _ _ trivial)
  have hcount := Radix.countEntries_steps graph hg
  simp only [solve, Radix.countEntries_value, Radix.insert_steps]
  change (Radix.countEntries graph).2 + (cbits + 1) +
    (run graph (graph.elements.length + 2) (initialQueue source) .empty).work + 2 ≤ _
  simp [budget, potential, initialQueue, Radix.insert_size, remaining, Radix.elements,
    Radix.lookup] at h
  dsimp only [initialQueue] at *
  nlinarith

end WeightedMIS.EfficientSearch
