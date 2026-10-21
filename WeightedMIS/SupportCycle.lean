module

public import WeightedMIS.ShortestPath

/-!
# A cycle in a finite directed support graph

A nonempty set of arcs in which every target has another supported outgoing
arc contains a nonempty closed walk. At most one visit per state is needed:
the selected cycle has distinct target states and uses only supported arcs.
The proof constructs a walk of length equal to the state count, independent
of any flow multiplicities.
-/

@[expose] public section

namespace WeightedMIS.SupportCycle

open WeightedMIS.ShortestPath

variable {V A : Type*}

private theorem walk_after (source target : A → V) (active : A → Prop)
    (hnext : ∀ a, active a → ∃ b, active b ∧ source b = target a)
    (n : ℕ) (a : A) (ha : active a) :
    ∃ t p, IsWalk source target (target a) t p ∧ p.length = n ∧ ∀ b ∈ p, active b := by
  induction n generalizing a with
  | zero => exact ⟨target a, [], rfl, rfl, by simp⟩
  | succ n ih =>
      obtain ⟨b, hb, hs⟩ := hnext a ha
      obtain ⟨t, p, hp, hlen, hactive⟩ := ih b hb
      refine ⟨t, b :: p, ⟨hs, hp⟩, by simp [hlen], ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hb
      · exact hactive c hc

private theorem cycle_of_not_simple (source target : A → V) {s t : V} {p : List A}
    (hp : IsWalk source target s t p) (hns : ¬ IsSimple target s p) :
    ∃ u q, IsWalk source target u u q ∧ q ≠ [] ∧ q.Sublist p := by
  classical
  induction p generalizing s with
  | nil => exact False.elim (hns (by simp [IsSimple, vertices]))
  | cons a p ih =>
      by_cases ht : IsSimple target (target a) p
      · have hs : s ∈ vertices target (target a) p := by
          by_contra h
          exact hns (List.nodup_cons.mpr ⟨h, ht⟩)
        obtain ⟨pre, post, heq, hpre, _, _⟩ := split_at_vertex source target hp.2 hs
        refine ⟨s, a :: pre, ⟨hp.1, hpre⟩, by simp, ?_⟩
        apply List.Sublist.cons_cons
        rw [heq]
        exact List.sublist_append_left pre post
      · obtain ⟨u, q, hq, hne, hsub⟩ := ih hp.2 ht
        exact ⟨u, q, hq, hne, hsub.cons a⟩

/-- Every nonempty closed walk contains a nonempty cycle with distinct target
states, preserving a sublist of its arc occurrences. -/
theorem simple_cycle_sublist (source target : A → V) {s : V} {p : List A}
    (hp : IsWalk source target s s p) (hne : p ≠ []) :
    ∃ u q, IsWalk source target u u q ∧ q ≠ [] ∧
      (q.map target).Nodup ∧ q.Sublist p := by
  cases p with
  | nil => exact False.elim (hne rfl)
  | cons a p =>
      obtain ⟨q, hq, hs, hsub⟩ := exists_simple_path_sublist source target hp.2
      exact ⟨s, a :: q, ⟨hp.1, hq⟩, by simp, hs, hsub.cons_cons a⟩

/-- A supported successor at every supported arc target yields a cycle of
length at most the state count. No magnitude-dependent walk is constructed. -/
theorem exists_supported_cycle [Fintype V] (source target : A → V) (active : A → Prop)
    (hne : ∃ a, active a)
    (hnext : ∀ a, active a → ∃ b, active b ∧ source b = target a) :
    ∃ u p, IsWalk source target u u p ∧ p ≠ [] ∧ (p.map target).Nodup ∧
      p.length ≤ Fintype.card V ∧ ∀ a ∈ p, active a := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨t, p, hp, hlen, hactive⟩ := walk_after source target active hnext
    (Fintype.card V) a ha
  have hns : ¬ IsSimple target (target a) p := by
    intro hs
    have hlt := simple_length_lt_card target hs
    omega
  obtain ⟨u, q, hq, hqne, hqsub⟩ := cycle_of_not_simple source target hp hns
  obtain ⟨v, r, hr, hrne, hrnd, hrsub⟩ := simple_cycle_sublist source target hq hqne
  refine ⟨v, r, hr, hrne, hrnd, ?_, ?_⟩
  · simpa using hrnd.length_le_card
  · intro b hb
    exact hactive b ((hrsub.trans hqsub).subset hb)

end WeightedMIS.SupportCycle
