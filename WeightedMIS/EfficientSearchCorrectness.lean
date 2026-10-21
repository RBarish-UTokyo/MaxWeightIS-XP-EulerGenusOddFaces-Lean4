module

public import WeightedMIS.EfficientSearchBounds
public import WeightedMIS.DijkstraCorrectness

/-!
# Correctness of the executable radix search

The abstract lazy-Dijkstra invariant is instantiated by the actual trie
contents.  Graph arcs are precisely the entries of the supplied adjacency
structure.  Minimum selection, dictionary updates and outgoing relaxations
are all discharged by properties of the executable operations.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch

variable {Label : Type*} {vbits cbits : ℕ}

abbrev StoredArc (graph : Graph Label vbits cbits) :=
  {edge : Bits vbits × Arc Label vbits cbits // edge ∈ graph.elements}

abbrev arcSource {graph : Graph Label vbits cbits} (edge : StoredArc graph) := edge.val.1
abbrev arcTarget {graph : Graph Label vbits cbits} (edge : StoredArc graph) := edge.val.2.target
abbrev arcWeight {graph : Graph Label vbits cbits} (edge : StoredArc graph) := edge.val.2.weight.value

def outgoing (graph : Graph Label vbits cbits) (vertex : Bits vbits) : List (StoredArc graph) :=
  (Radix.lookup vertex graph).1.attach.map fun edge =>
    ⟨(vertex, edge.val), (Radix.mem_lookup vertex graph edge.val).mp edge.property⟩

theorem mem_outgoing (graph : Graph Label vbits cbits) (vertex : Bits vbits)
    (edge : StoredArc graph) : edge ∈ outgoing graph vertex ↔ arcSource edge = vertex := by
  constructor
  · intro h
    obtain ⟨a, _, ha⟩ := List.mem_map.mp h
    exact (congrArg (fun e : StoredArc graph => e.val.1) ha).symm
  · intro h
    have hm : edge.val.2 ∈ (Radix.lookup vertex graph).1 := by
      apply (Radix.mem_lookup _ _ _).mpr
      simpa [← h] using edge.property
    apply List.mem_map.mpr
    refine ⟨⟨edge.val.2, hm⟩, List.mem_attach _ _, ?_⟩
    apply Subtype.ext
    exact Prod.ext h.symm rfl

def frontier (queue : Queue Label vbits cbits) : List (ℕ × Bits vbits) :=
  queue.elements.map (fun item => (item.1.value, item.2.vertex))

def distances (settled : Settled Label vbits cbits) (vertex : Bits vbits) : Option ℕ :=
  ((Radix.lookup vertex settled).1.head?).map (fun result => result.1.value)

theorem distances_empty : distances (Radix.empty : Settled Label vbits cbits) = fun _ => none := by
  funext vertex
  simp [distances, Radix.lookup]

theorem distances_none (settled : Settled Label vbits cbits) (vertex : Bits vbits) :
    distances settled vertex = none ↔ (Radix.lookup vertex settled).1 = [] := by
  simp [distances]

theorem distances_insert (settled : Settled Label vbits cbits) (vertex : Bits vbits)
    (distance : Bits cbits) (path : Trace Label vbits cbits) :
    distances (Radix.insert vertex (distance, path) settled).1 =
      Function.update (distances settled) vertex (some distance.value) := by
  funext query
  simp only [distances, Radix.lookup_insert]
  by_cases h : query = vertex <;> simp [h, Function.update, distances]

theorem frontier_pop (queue queue' : Queue Label vbits cbits)
    (distance : Bits cbits) (candidate : Candidate Label vbits cbits)
    (hp : (Radix.pop queue).1 = some (distance, candidate, queue')) :
    frontier queue = (distance.value, candidate.vertex) :: frontier queue' := by
  simp [frontier, Radix.pop_elements queue hp]

theorem frontier_insert (queue : Queue Label vbits cbits) (distance : Bits cbits)
    (candidate : Candidate Label vbits cbits) (q : ℕ × Bits vbits) :
    q ∈ frontier (Radix.insert distance candidate queue).1 ↔
      q = (distance.value, candidate.vertex) ∨ q ∈ frontier queue := by
  simp only [frontier, List.mem_map, Radix.mem_insert]
  constructor
  · rintro ⟨item, heq | hmem, hq⟩
    · subst item
      exact Or.inl hq.symm
    · exact Or.inr ⟨item, hmem, hq⟩
  · rintro (heq | ⟨item, hmem, hq⟩)
    · exact ⟨(distance, candidate), Or.inl rfl, heq.symm⟩
    · exact ⟨item, Or.inr hmem, hq⟩

theorem frontier_relax (candidate : Candidate Label vbits cbits) (distance : Bits cbits)
    (edges : List (Arc Label vbits cbits)) (queue : Queue Label vbits cbits)
    (hsafe : (relax candidate distance edges queue).2.1 = false)
    (q : ℕ × Bits vbits) :
    q ∈ frontier (relax candidate distance edges queue).1 ↔
      q ∈ frontier queue ∨ ∃ edge ∈ edges,
        q = (distance.value + edge.weight.value, edge.target) := by
  induction edges generalizing queue with
  | nil => simp [relax]
  | cons edge rest ih =>
    change ((Bits.add distance edge.weight).2.1 ||
      (relax candidate distance rest
        (Radix.insert (Bits.add distance edge.weight).1
          ⟨edge.target, (candidate.vertex, edge) :: candidate.reversePath⟩ queue).1).2.1) = false at hsafe
    have hs := Bool.or_eq_false_iff.mp hsafe
    have hadd := Bits.add_value_of_no_overflow distance edge.weight hs.1
    simp only [relax, ih _ hs.2, frontier_insert, hadd, List.mem_cons]
    aesop

theorem natural_relax_outgoing (graph : Graph Label vbits cbits) (vertex : Bits vbits)
    (distance : ℕ) (q : ℕ × Bits vbits) :
    q ∈ Dijkstra.relax arcTarget arcWeight distance (outgoing graph vertex) ↔
      ∃ edge ∈ (Radix.lookup vertex graph).1,
        q = (distance + edge.weight.value, edge.target) := by
  simp only [Dijkstra.relax, outgoing, List.mem_map]
  constructor
  · rintro ⟨edge, ⟨raw, _, rfl⟩, hq⟩
    exact ⟨raw.val, raw.property, hq.symm⟩
  · rintro ⟨raw, hraw, hq⟩
    refine ⟨⟨(vertex, raw), (Radix.mem_lookup _ _ _).mp hraw⟩, ?_, hq.symm⟩
    exact ⟨⟨raw, hraw⟩, List.mem_attach _ _, rfl⟩

def Correct (graph : Graph Label vbits cbits) (source : Bits vbits)
    (queue : Queue Label vbits cbits) (settled : Settled Label vbits cbits) : Prop :=
  Dijkstra.Invariant (arcSource (graph := graph)) arcTarget arcWeight source
    (distances settled) (frontier queue)

theorem run_correct (graph : Graph Label vbits cbits) (source : Bits vbits) (fuel : ℕ)
    (queue : Queue Label vbits cbits) (settled : Settled Label vbits cbits)
    (hi : Correct graph source queue settled)
    (hsafe : (run graph fuel queue settled).status ≠ .overflow) :
    Correct graph source (run graph fuel queue settled).queue
      (run graph fuel queue settled).settled := by
  induction fuel generalizing queue settled with
  | zero => exact hi
  | succ fuel ih =>
    cases hp : (Radix.pop queue).1 with
    | none => simpa [run, hp] using hi
    | some item =>
      obtain ⟨distance, candidate, queue'⟩ := item
      have hf := frontier_pop queue queue' distance candidate hp
      change Dijkstra.Invariant _ _ _ _ _ _ at hi
      rw [hf] at hi
      cases hk : (Radix.lookup candidate.vertex settled).1 with
      | cons x xs =>
        have hd : distances settled candidate.vertex ≠ none := by simp [distances, hk]
        have hi' := hi.discard hd
        have hs' : (run graph fuel queue' settled).status ≠ .overflow := by
          simpa [run, hp, hk] using hsafe
        simpa [run, hp, hk] using ih queue' settled hi' hs'
      | nil =>
        have hd : distances settled candidate.vertex = none := (distances_none _ _).mpr hk
        have hmin : ∀ q ∈ (distance.value, candidate.vertex) :: frontier queue',
            distance.value ≤ q.1 := by
          intro q hq
          rw [← hf] at hq
          obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hq
          exact Radix.pop_minimum queue hp hraw
        have hsettle := hi.settle hd hmin (outgoing graph candidate.vertex)
          (mem_outgoing graph candidate.vertex)
        cases hov : (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').2.1
        · have hi' : Correct graph source
              (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').1
              (Radix.insert candidate.vertex (distance, candidate.reversePath) settled).1 := by
            unfold Correct
            rw [distances_insert]
            apply hsettle.congr_frontier
            intro q
            simp only [List.mem_append, natural_relax_outgoing, frontier_relax _ _ _ _ hov]
          have hs' : (run graph fuel
              (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').1
              (Radix.insert candidate.vertex (distance, candidate.reversePath) settled).1).status ≠
                .overflow := by simpa [run, hp, hk, hov] using hsafe
          simpa [run, hp, hk, hov] using ih _ _ hi' hs'
        · simp [run, hp, hk, hov] at hsafe

theorem run_finished_empty (graph : Graph Label vbits cbits) (fuel : ℕ)
    (queue : Queue Label vbits cbits) (settled : Settled Label vbits cbits)
    (hfinish : (run graph fuel queue settled).status = .finished) :
    frontier (run graph fuel queue settled).queue = [] := by
  induction fuel generalizing queue settled with
  | zero => simp [run] at hfinish
  | succ fuel ih =>
    cases hp : (Radix.pop queue).1 with
    | none => simp [run, hp, frontier, (Radix.pop_none queue).mp hp]
    | some item =>
      obtain ⟨distance, candidate, queue'⟩ := item
      cases hk : (Radix.lookup candidate.vertex settled).1 with
      | cons x xs =>
        simpa [run, hp, hk] using ih queue' settled (by simpa [run, hp, hk] using hfinish)
      | nil =>
        cases hov : (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').2.1
        · simpa [run, hp, hk, hov] using ih
            (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').1
            (Radix.insert candidate.vertex (distance, candidate.reversePath) settled).1
            (by simpa [run, hp, hk, hov] using hfinish)
        · simp [run, hp, hk, hov] at hfinish

theorem initial_correct (graph : Graph Label vbits cbits) (source : Bits vbits) :
    Correct graph source (initialQueue source) .empty := by
  unfold Correct
  rw [distances_empty]
  apply (Dijkstra.initial (arcSource (graph := graph)) arcTarget arcWeight source).congr_frontier
  intro q
  simp only [initialQueue, frontier_insert]
  simp [frontier, Radix.elements]

theorem solve_correct (graph : Graph Label vbits cbits) (source : Bits vbits)
    (weightBound : ℕ) (hg : GraphBound graph weightBound)
    (hwidth : (graph.elements.length + 2) * weightBound < 2 ^ cbits) :
    Correct graph source (solve graph source).queue (solve graph source).settled := by
  have hs := solve_no_overflow graph source weightBound hg hwidth
  simp only [solve, Radix.countEntries_value] at hs ⊢
  exact run_correct graph source _ _ _ (initial_correct graph source) hs

/-- The concrete output dictionary contains the attained shortest distance of
every reachable vertex. -/
theorem solve_distances_exact (graph : Graph Label vbits cbits) (source target : Bits vbits)
    (weightBound : ℕ) (hg : GraphBound graph weightBound)
    (hwidth : (graph.elements.length + 2) * weightBound < 2 ^ cbits)
    (hreach : ∃ path, ShortestPath.IsWalk (arcSource (graph := graph)) arcTarget source target path) :
    ∃ distance, distances (solve graph source).settled target = some distance ∧
      Dijkstra.Exact (arcSource (graph := graph)) arcTarget arcWeight source target distance := by
  have hi := solve_correct graph source weightBound hg hwidth
  have hf := solve_finished graph source weightBound hg hwidth
  have he : frontier (solve graph source).queue = [] := by
    simp only [solve, Radix.countEntries_value] at hf ⊢
    exact run_finished_empty _ _ _ _ hf
  unfold Correct at hi
  rw [he] at hi
  exact hi.complete target hreach

end WeightedMIS.EfficientSearch
