module

public import WeightedMIS.ResidualListReach

/-!
# Reached sets of the finite searches are exactly reflexive-transitive closures

The abstract search `MaxFlowReach.explore` with fuel `Fintype.card V` reaches
exactly the vertices related to the source by the reflexive-transitive closure
of the searched relation.

The word-level residual search `ResidualListReach.explore`, which is the
reference function of the compiled residual search, reaches exactly the words
related to the source by the closure of the usable-arc relation: an arc of the
table whose capacity is at least the threshold word. This holds with fuel equal
to the length of any node list containing the source and every arc target.
Membership is value-level membership as decided by `RegisterMembership.found`.
-/

@[expose] public section

namespace WeightedMIS.MaxFlowReach

variable {V : Type*} [DecidableEq V]

/-- Every vertex added by the search is reachable from the source. -/
theorem explore_sound (rel : V → V → Prop) [DecidableRel rel] (nodes : List V) (s : V)
    (fuel : ℕ) (q : State V) (hq : ∀ v ∈ q.seen, Relation.ReflTransGen rel s v) :
    ∀ v ∈ (explore rel nodes fuel q).seen, Relation.ReflTransGen rel s v := by
  induction fuel generalizing q with
  | zero => exact hq
  | succ fuel ih =>
    simp only [explore]
    split
    · exact hq
    · rename_i a ha
      apply ih
      have hc := crossing_some rel nodes q.seen a ha
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Relation.ReflTransGen.tail (hq a.1 hc.1) hc.2.2
      · exact hq v hv

/-- The reached set of the full search is the reflexive-transitive closure. -/
theorem seen_iff_rtg [Fintype V] (rel : V → V → Prop) [DecidableRel rel]
    (nodes : List V) (complete : ∀ v, v ∈ nodes) (s v : V) :
    v ∈ (explore rel nodes (Fintype.card V) (initial s)).seen ↔
      Relation.ReflTransGen rel s v := by
  constructor
  · apply explore_sound rel nodes s
    intro u hu
    have he : u = s := by simpa [initial] using hu
    rw [he]
  · intro hv
    have hs := search_spec rel nodes complete s s
    induction hv with
    | refl => exact hs.1
    | tail _ hbc ih =>
      by_contra hn
      exact hs.2.2 _ ih _ hn hbc

end WeightedMIS.MaxFlowReach

namespace WeightedMIS.ResidualListReach

open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords

theorem bits_value_inj {n : ℕ} : Function.Injective (@Bits.value n) := by
  intro a b h
  induction n with
  | zero => cases a; cases b; rfl
  | succ n ih =>
    cases a with
    | cons x xs =>
      cases b with
      | cons y ys =>
        have hx := xs.value_lt
        have hy := ys.value_lt
        have hxy : x = y := by
          cases x <;> cases y <;> simp_all [Bits.value]
          all_goals omega
        subst hxy
        have hv : xs.value = ys.value := by
          cases x <;> simp_all [Bits.value]
        rw [ih hv]

theorem found_iff_mem {n : ℕ} (query : Bits n) (keys : List (Bits n)) :
    RegisterMembership.found query keys = true ↔ query ∈ keys := by
  rw [RegisterMembership.found_iff]
  constructor
  · rintro ⟨key, hk, he⟩
    rwa [← bits_value_inj he]
  · intro hq
    exact ⟨query, hq, rfl⟩

/-- Arcs usable by the residual search at threshold `d`. -/
def ArcRel {n b : ℕ} (table : List (Arc n b)) (d : Bits b) (u v : Bits n) : Prop :=
  ∃ a ∈ table, a.source = u ∧ a.target = v ∧ d.value ≤ a.capacity.value

variable {n b : ℕ}

theorem crossing_some_rel (table : List (Arc n b)) (d : Bits b) (seen : List (Bits n))
    (a : Arc n b) (ha : RegisterResidualCrossing.crossing seen d table = some a) :
    a.source ∈ seen ∧ a.target ∉ seen ∧ ArcRel table d a.source a.target := by
  obtain ⟨hmem, hs, ht, hc⟩ := RegisterResidualCrossing.crossing_some seen d table a ha
  rw [← RegisterMembership.found_iff, found_iff_mem] at hs ht
  exact ⟨hs, ht, a, hmem, rfl, rfl, hc⟩

/-- Every word added by the search is related to the source. -/
theorem explore_sound (table : List (Arc n b)) (d : Bits b) (s : Bits n) (fuel : ℕ)
    (q : State n b) (hq : ∀ v ∈ q.seen, Relation.ReflTransGen (ArcRel table d) s v) :
    ∀ v ∈ (explore table d fuel q).seen, Relation.ReflTransGen (ArcRel table d) s v := by
  induction fuel generalizing q with
  | zero => exact hq
  | succ fuel ih =>
    simp only [explore]
    split
    · exact hq
    · rename_i a ha
      apply ih
      have hc := crossing_some_rel table d q.seen a ha
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Relation.ReflTransGen.tail (hq a.source hc.1) hc.2.2
      · exact hq v hv

/-- Reached words are never removed. -/
theorem explore_superset (table : List (Arc n b)) (d : Bits b) (fuel : ℕ) (q : State n b) :
    ∀ v ∈ q.seen, v ∈ (explore table d fuel q).seen := by
  induction fuel generalizing q with
  | zero => exact fun v hv => hv
  | succ fuel ih =>
    simp only [explore]
    split
    · exact fun v hv => hv
    · rename_i a _
      exact fun v hv => ih (extend q d a) v (List.mem_cons_of_mem _ hv)

/-- A duplicate-free list of words all occurring in `nodes` is not longer than `nodes`. -/
theorem length_le_of_subset (seen nodes : List (Bits n)) (hnd : seen.Nodup)
    (hsub : ∀ v ∈ seen, v ∈ nodes) : seen.length ≤ nodes.length := by
  have h1 : seen.toFinset.card = seen.length := List.toFinset_card_of_nodup hnd
  have h2 : seen.toFinset ⊆ nodes.toFinset := by
    intro v hv
    exact List.mem_toFinset.mpr (hsub v (List.mem_toFinset.mp hv))
  have h3 := Finset.card_le_card h2
  have h4 := List.toFinset_card_le nodes
  omega

/-- If all arc targets lie in `nodes`, enough fuel closes the reached set. -/
theorem explore_closed (table : List (Arc n b)) (d : Bits b) (nodes : List (Bits n))
    (htargets : ∀ a ∈ table, a.target ∈ nodes) (fuel : ℕ) (q : State n b)
    (hnd : q.seen.Nodup) (hsub : ∀ v ∈ q.seen, v ∈ nodes)
    (hbound : nodes.length < fuel + q.seen.length) :
    RegisterResidualCrossing.crossing (explore table d fuel q).seen d table = none := by
  induction fuel generalizing q with
  | zero =>
    have := length_le_of_subset q.seen nodes hnd hsub
    omega
  | succ fuel ih =>
    simp only [explore]
    split
    · assumption
    · rename_i a ha
      have hc := crossing_some_rel table d q.seen a ha
      apply ih
      · exact List.nodup_cons.mpr ⟨hc.2.1, hnd⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · obtain ⟨a', ha', _, ht, _⟩ := hc.2.2
          rw [← ht]
          exact htargets a' ha'
        · exact hsub v hv
      · simp only [extend, List.length_cons]
        omega

/-- The word-level residual search with fuel `nodes.length` reaches exactly
the closure of the usable-arc relation. -/
theorem mem_explore_iff (table : List (Arc n b)) (d : Bits b) (nodes : List (Bits n))
    (s : Bits n) (hs : s ∈ nodes) (htargets : ∀ a ∈ table, a.target ∈ nodes) (v : Bits n) :
    v ∈ (explore table d nodes.length (initial s)).seen ↔
      Relation.ReflTransGen (ArcRel table d) s v := by
  constructor
  · apply explore_sound table d s
    intro u hu
    have he : u = s := by simpa [initial] using hu
    rw [he]
  · intro hv
    have hclosed := explore_closed table d nodes htargets nodes.length (initial s)
      (by simp [initial]) (by simpa [initial] using hs) (by simp [initial])
    have hsrc := explore_superset table d nodes.length (initial s) s (by simp [initial])
    induction hv with
    | refl => exact hsrc
    | tail _ hbc ih =>
      rename_i x y _
      by_contra hn
      obtain ⟨a, ha, hsa, hta, hca⟩ := hbc
      have hlt := RegisterResidualCrossing.crossing_none _ d table hclosed a ha
        (by rw [← RegisterMembership.found_iff, found_iff_mem, hsa]; exact ih)
        (by rw [← RegisterMembership.found_iff, found_iff_mem, hta]; exact hn)
      omega

/-- Value-level form, as decided by the compiled membership scan. -/
theorem found_explore_iff (table : List (Arc n b)) (d : Bits b) (nodes : List (Bits n))
    (s : Bits n) (hs : RegisterMembership.found s nodes = true)
    (htargets : ∀ a ∈ table, RegisterMembership.found a.target nodes = true) (v : Bits n) :
    RegisterMembership.found v (explore table d nodes.length (initial s)).seen = true ↔
      Relation.ReflTransGen (ArcRel table d) s v := by
  rw [found_iff_mem]
  rw [found_iff_mem] at hs
  exact mem_explore_iff table d nodes s hs
    (fun a ha => (found_iff_mem _ _).mp (htargets a ha)) v

end WeightedMIS.ResidualListReach

namespace WeightedMIS.ReachSeen

/-- Transport of reflexive-transitive closures along an encoding whose steps
are exactly the encoded steps. -/
theorem rtg_encode {α β : Type*} (rel : α → α → Prop) (wrel : β → β → Prop) (enc : α → β)
    (hstep : ∀ a y, wrel (enc a) y ↔ ∃ c, y = enc c ∧ rel a c) (s : α) (y : β) :
    Relation.ReflTransGen wrel (enc s) y ↔ ∃ t, y = enc t ∧ Relation.ReflTransGen rel s t := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨s, rfl, .refl⟩
    | tail _ hyz ih =>
      obtain ⟨t, rfl, ht⟩ := ih
      obtain ⟨c, rfl, hc⟩ := (hstep t _).mp hyz
      exact ⟨c, rfl, ht.tail hc⟩
  · rintro ⟨t, rfl, ht⟩
    induction ht with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail ((hstep _ _).mpr ⟨_, rfl, hbc⟩)

theorem rtg_encode_iff {α β : Type*} (rel : α → α → Prop) (wrel : β → β → Prop) (enc : α → β)
    (hinj : Function.Injective enc)
    (hstep : ∀ a y, wrel (enc a) y ↔ ∃ c, y = enc c ∧ rel a c) (s t : α) :
    Relation.ReflTransGen wrel (enc s) (enc t) ↔ Relation.ReflTransGen rel s t := by
  rw [rtg_encode rel wrel enc hstep]
  constructor
  · rintro ⟨u, hu, h⟩
    rwa [hinj hu]
  · intro h
    exact ⟨t, rfl, h⟩

end WeightedMIS.ReachSeen
