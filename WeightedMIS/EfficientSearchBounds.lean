module

public import WeightedMIS.EfficientSearchLoop

/-!
# Word bounds and overflow exclusion for the radix search

The bound uses the number of adjacency entries, including parallel arcs.  It
therefore needs no prior reachability computation and no simple-path oracle.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch

variable {Label : Type*} {vbits cbits : ℕ}

def QueueBound (queue : Queue Label vbits cbits) (fuel weightBound : ℕ) : Prop :=
  ∀ item ∈ queue.elements, item.1.value + fuel * weightBound < 2 ^ cbits

def GraphBound (graph : Graph Label vbits cbits) (weightBound : ℕ) : Prop :=
  ∀ edge ∈ graph.elements, edge.2.weight.value ≤ weightBound

theorem QueueBound.mono {queue : Queue Label vbits cbits} {fuel fuel' weightBound : ℕ}
    (h : QueueBound queue fuel weightBound) (hle : fuel' ≤ fuel) :
    QueueBound queue fuel' weightBound := by
  intro item hitem
  have hi := h item hitem
  have hm := Nat.mul_le_mul_right weightBound hle
  omega

theorem QueueBound.pop {queue queue' : Queue Label vbits cbits}
    {fuel weightBound : ℕ} {key : Bits cbits} {candidate : Candidate Label vbits cbits}
    (h : QueueBound queue fuel weightBound)
    (hp : (Radix.pop queue).1 = some (key, candidate, queue')) :
    key.value + fuel * weightBound < 2 ^ cbits ∧ QueueBound queue' fuel weightBound := by
  have he := Radix.pop_elements queue hp
  constructor
  · exact h (key, candidate) (by rw [he]; exact List.mem_cons_self)
  · intro item hi
    exact h item (by rw [he]; exact List.mem_cons_of_mem _ hi)

theorem relax_safe (u : Candidate Label vbits cbits) (distance : Bits cbits)
    (edges : List (Arc Label vbits cbits)) (queue : Queue Label vbits cbits)
    (fuel weightBound : ℕ)
    (he : ∀ e ∈ edges, e.weight.value ≤ weightBound)
    (hd : distance.value + (fuel + 1) * weightBound < 2 ^ cbits)
    (hq : QueueBound queue fuel weightBound) :
    (relax u distance edges queue).2.1 = false ∧
      QueueBound (relax u distance edges queue).1 fuel weightBound := by
  induction edges generalizing queue with
  | nil => exact ⟨rfl, hq⟩
  | cons edge rest ih =>
    have hew := he edge (by simp)
    have hsum : distance.value + edge.weight.value < 2 ^ cbits := by
      have hm : weightBound ≤ (fuel + 1) * weightBound := by nlinarith
      omega
    have hadd := Bits.add_value_of_lt distance edge.weight hsum
    have hnew : QueueBound
        (Radix.insert (Bits.add distance edge.weight).1
          (Candidate.mk edge.target ((u.vertex, edge) :: u.reversePath)) queue).1
        fuel weightBound := by
      intro item hi
      rcases (Radix.mem_insert _ _ _ _).mp hi with rfl | hi
      · simp only [hadd.2]
        nlinarith
      · exact hq item hi
    have hrest := ih _ (fun e hm => he e (List.mem_cons_of_mem edge hm)) hnew
    simp only [relax, hadd.1, Bool.false_or]
    exact hrest

theorem run_no_overflow (graph : Graph Label vbits cbits) (fuel weightBound : ℕ)
    (queue : Queue Label vbits cbits) (settled : Settled Label vbits cbits)
    (hg : GraphBound graph weightBound) (hq : QueueBound queue fuel weightBound) :
    (run graph fuel queue settled).status ≠ .overflow := by
  induction fuel generalizing queue settled with
  | zero => simp [run]
  | succ fuel ih =>
    cases hp : (Radix.pop queue).1 with
    | none => simp [run, hp]
    | some item =>
      obtain ⟨distance, candidate, queue'⟩ := item
      obtain ⟨hd, hq'⟩ := hq.pop hp
      have hq'' := hq'.mono (Nat.le_succ fuel)
      cases hk : (Radix.lookup candidate.vertex settled).1 with
      | cons x xs => simpa [run, hp, hk] using ih queue' settled hq''
      | nil =>
        have hs := relax_safe candidate distance (Radix.lookup candidate.vertex graph).1
          queue' fuel weightBound
          (fun edge he => hg (candidate.vertex, edge) ((Radix.mem_lookup _ _ _).mp he)) hd hq''
        simpa [run, hp, hk, hs.1] using ih _ _ hs.2

theorem initialQueue_bound (source : Bits vbits) (fuel weightBound : ℕ)
    (hbound : fuel * weightBound < 2 ^ cbits) :
    QueueBound (initialQueue (Label := Label) (cbits := cbits) source) fuel weightBound := by
  intro item hitem
  simp only [initialQueue, Radix.mem_insert, Radix.elements, List.not_mem_nil, or_false] at hitem
  subst item
  simpa using hbound

/-- A concrete input-width inequality rules out every overflow branch. -/
theorem solve_no_overflow (graph : Graph Label vbits cbits) (source : Bits vbits)
    (weightBound : ℕ) (hg : GraphBound graph weightBound)
    (hwidth : (graph.elements.length + 2) * weightBound < 2 ^ cbits) :
    (solve graph source).status ≠ .overflow := by
  simp only [solve, Radix.countEntries_value]
  exact run_no_overflow graph _ weightBound _ _ hg (initialQueue_bound source _ _ hwidth)

theorem solve_finished (graph : Graph Label vbits cbits) (source : Bits vbits)
    (weightBound : ℕ) (hg : GraphBound graph weightBound)
    (hwidth : (graph.elements.length + 2) * weightBound < 2 ^ cbits) :
    (solve graph source).status = .finished := by
  have he := solve_not_exhausted graph source
  have ho := solve_no_overflow graph source weightBound hg hwidth
  cases hs : (solve graph source).status <;> simp_all

end WeightedMIS.EfficientSearch
