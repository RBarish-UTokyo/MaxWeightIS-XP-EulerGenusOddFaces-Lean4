module

public import WeightedMIS.ShortestPath

/-!
# Correctness of lazy Dijkstra steps

The frontier contains natural-distance labels, with repeated vertices allowed.
Each label has a genuine walk witness. Every settled vertex has its exact
shortest distance, and every arc crossing from a settled to an unsettled vertex
has its relaxation in the frontier. The first-exit argument proves that
extracting a minimum unsettled label is correct. These invariants are preserved
by the explicit discard and settle-and-enqueue transitions.
-/

@[expose] public section

namespace WeightedMIS.Dijkstra

open ShortestPath

variable {V E : Type*}

/-- Exact sum of natural arc costs along a walk. -/
def cost (c : E → ℕ) (p : List E) : ℕ := (p.map c).sum

@[simp] theorem cost_nil (c : E → ℕ) : cost c [] = 0 := rfl

@[simp] theorem cost_cons (c : E → ℕ) (e : E) (p : List E) :
    cost c (e :: p) = c e + cost c p := rfl

@[simp] theorem cost_append (c : E → ℕ) (p q : List E) :
    cost c (p ++ q) = cost c p + cost c q := by simp [cost]

/-- An attained distance label and its comparison with every directed walk. -/
def Exact (src dst : E → V) (c : E → ℕ) (s v : V) (d : ℕ) : Prop :=
  (∃ p, IsWalk src dst s v p ∧ cost c p = d) ∧
    ∀ p, IsWalk src dst s v p → d ≤ cost c p

/-- The first arc leaving a set splits a genuine walk into its prefix, that
arc, and the remaining suffix. -/
theorem first_exit (src dst : E → V) (S : Set V) {s t : V} {p : List E}
    (hp : IsWalk src dst s t p) (hs : s ∈ S) (ht : t ∉ S) :
    ∃ pre e post, p = pre ++ e :: post ∧ IsWalk src dst s (src e) pre ∧
      src e ∈ S ∧ dst e ∉ S ∧ IsWalk src dst (dst e) t post := by
  classical
  induction p generalizing s with
  | nil =>
      have he : s = t := hp
      exact (ht (he ▸ hs)).elim
  | cons e p ih =>
      by_cases hdst : dst e ∈ S
      · obtain ⟨pre, f, post, heq, hpre, hsrc, hdst', hpost⟩ := ih hp.2 hdst
        exact ⟨e :: pre, f, post, by simp [heq], ⟨hp.1, hpre⟩,
          hsrc, hdst', hpost⟩
      · exact ⟨[], e, p, rfl, hp.1.symm, hp.1 ▸ hs, hdst, hp.2⟩

/-- All four assertions refer to the actual graph and the actual frontier. -/
structure Invariant (src dst : E → V) (c : E → ℕ) (s : V)
    (dist : V → Option ℕ) (frontier : List (ℕ × V)) : Prop where
  source : dist s ≠ none ∨ (0, s) ∈ frontier
  witness : ∀ q ∈ frontier, ∃ p, IsWalk src dst s q.2 p ∧ cost c p = q.1
  settled : ∀ v d, dist v = some d → Exact src dst c s v d
  boundary : ∀ e d, dist (src e) = some d → dist (dst e) = none →
    (d + c e, dst e) ∈ frontier

theorem initial (src dst : E → V) (c : E → ℕ) (s : V) :
    Invariant src dst c s (fun _ => none) [(0, s)] := by
  constructor
  · simp
  · intro q hq
    have hq' : q = (0, s) := by simpa using hq
    subst q
    exact ⟨[], rfl, rfl⟩
  · intro v d h
    contradiction
  · intro e d h
    contradiction

/-- The invariant depends on frontier membership, so changing the queue's
internal order or representation does not alter it. -/
theorem Invariant.congr_frontier {src dst : E → V} {c : E → ℕ} {s : V}
    {dist : V → Option ℕ} {q q' : List (ℕ × V)}
    (h : Invariant src dst c s dist q) (he : ∀ a, a ∈ q ↔ a ∈ q') :
    Invariant src dst c s dist q' := by
  refine ⟨h.source.imp_right ((he _).mp), ?_, h.settled, ?_⟩
  · intro a ha
    exact h.witness a ((he a).mpr ha)
  · intro e d hd ht
    exact (he _).mp (h.boundary e d hd ht)

/-- Every walk to an unsettled vertex has a frontier label no more expensive
than that walk. This is the cut argument behind Dijkstra's greedy step. -/
theorem Invariant.frontier_le_walk {src dst : E → V} {c : E → ℕ} {s : V}
    {dist : V → Option ℕ} {frontier : List (ℕ × V)}
    (h : Invariant src dst c s dist frontier) {v : V} {p : List E}
    (hp : IsWalk src dst s v p) (hv : dist v = none) :
    ∃ q ∈ frontier, q.1 ≤ cost c p := by
  classical
  rcases h.source with hs | hs
  · obtain ⟨pre, e, post, heq, hpre, hsrc, hdst, _⟩ :=
      first_exit src dst {u | dist u ≠ none} hp hs (by simpa using hv)
    obtain ⟨d, hd⟩ : ∃ d, dist (src e) = some d := Option.ne_none_iff_exists'.mp hsrc
    have hdst' : dist (dst e) = none := by simpa using hdst
    have hb := h.boundary e d hd hdst'
    have hmin := (h.settled (src e) d hd).2 pre hpre
    refine ⟨(d + c e, dst e), hb, ?_⟩
    rw [heq, cost_append, cost_cons]
    dsimp
    omega
  · exact ⟨(0, s), hs, Nat.zero_le _⟩

/-- A minimum frontier entry at an unsettled vertex has its true shortest
distance. Minimum extraction is a checkable property of the concrete queue. -/
theorem Invariant.minimum_exact {src dst : E → V} {c : E → ℕ} {s : V}
    {dist : V → Option ℕ} {frontier : List (ℕ × V)}
    (h : Invariant src dst c s dist frontier) (d : ℕ) (v : V)
    (hmem : (d, v) ∈ frontier) (hv : dist v = none)
    (hmin : ∀ q ∈ frontier, d ≤ q.1) : Exact src dst c s v d := by
  refine ⟨h.witness _ hmem, ?_⟩
  intro p hp
  obtain ⟨q, hq, hle⟩ := h.frontier_le_walk hp hv
  exact (hmin q hq).trans hle

/-- Stale entries may be discarded because boundary obligations only point
to unsettled vertices. -/
theorem Invariant.discard {src dst : E → V} {c : E → ℕ} {s : V}
    {dist : V → Option ℕ} {frontier : List (ℕ × V)} {d : ℕ} {v : V}
    (h : Invariant src dst c s dist ((d, v) :: frontier)) (hv : dist v ≠ none) :
    Invariant src dst c s dist frontier := by
  constructor
  · rcases h.source with hs | hs
    · exact Or.inl hs
    · rcases List.mem_cons.mp hs with heq | hmem
      · have hsv : s = v := congrArg Prod.snd heq
        exact Or.inl (hsv ▸ hv)
      · exact Or.inr hmem
  · intro q hq
    exact h.witness q (List.mem_cons_of_mem _ hq)
  · exact h.settled
  · intro e de hde he
    rcases List.mem_cons.mp (h.boundary e de hde he) with hsame | hmem
    · have htarget : dst e = v := congrArg Prod.snd hsame
      exact (hv (htarget ▸ he)).elim
    · exact hmem

/-- The concrete lazy-Dijkstra relaxation list at a newly settled vertex. -/
def relax (dst : E → V) (c : E → ℕ) (d : ℕ) (outgoing : List E) : List (ℕ × V) :=
  outgoing.map fun e => (d + c e, dst e)

/-- Settling a minimum nonstale entry and inserting every outgoing relaxation
preserves correctness. No optimization oracle is a premise. -/
theorem Invariant.settle [DecidableEq V]
    {src dst : E → V} {c : E → ℕ} {s : V}
    {dist : V → Option ℕ} {frontier : List (ℕ × V)} {d : ℕ} {v : V}
    (h : Invariant src dst c s dist ((d, v) :: frontier)) (hv : dist v = none)
    (hmin : ∀ q ∈ (d, v) :: frontier, d ≤ q.1)
    (outgoing : List E) (hout : ∀ e, e ∈ outgoing ↔ src e = v) :
    Invariant src dst c s (Function.update dist v (some d))
      (frontier ++ relax dst c d outgoing) := by
  classical
  have hexact := h.minimum_exact d v (by simp) hv hmin
  constructor
  · by_cases hsv : s = v
    · left
      simp [hsv]
    · rcases h.source with hs | hs
      · left
        simpa [Function.update_of_ne hsv] using hs
      · right
        apply List.mem_append_left
        rcases List.mem_cons.mp hs with heq | hmem
        · exact (hsv (congrArg Prod.snd heq)).elim
        · exact hmem
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact h.witness q (List.mem_cons_of_mem _ hq)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
      obtain ⟨p, hp, hcost⟩ := hexact.1
      refine ⟨p ++ [e], walk_append src dst hp ⟨(hout e).mp he, rfl⟩, ?_⟩
      simp [hcost]
  · intro u du hdu
    by_cases huv : u = v
    · subst u
      have hd : du = d := by simpa using hdu.symm
      simpa [hd] using hexact
    · exact h.settled u du (by simpa [Function.update_of_ne huv] using hdu)
  · intro e de hde he
    have htarget : dst e ≠ v := by
      intro hh
      simp [hh] at he
    have he' : dist (dst e) = none := by
      simpa [Function.update_of_ne htarget] using he
    by_cases hsrc : src e = v
    · have hde' : de = d := by simpa [hsrc] using hde.symm
      subst de
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨e, (hout e).mpr hsrc, rfl⟩
    · have hde' : dist (src e) = some de := by
        simpa [Function.update_of_ne hsrc] using hde
      apply List.mem_append_left
      rcases List.mem_cons.mp (h.boundary e de hde' he') with heq | hmem
      · exact (htarget (congrArg Prod.snd heq)).elim
      · exact hmem

/-- An empty frontier certifies that every reachable vertex has been settled,
and its stored value is the attained shortest distance. -/
theorem Invariant.complete {src dst : E → V} {c : E → ℕ} {s : V}
    {dist : V → Option ℕ} (h : Invariant src dst c s dist [])
    (v : V) (hv : ∃ p, IsWalk src dst s v p) :
    ∃ d, dist v = some d ∧ Exact src dst c s v d := by
  cases hd : dist v with
  | none =>
      obtain ⟨p, hp⟩ := hv
      obtain ⟨q, hq, _⟩ := h.frontier_le_walk hp hd
      simp at hq
  | some d => exact ⟨d, rfl, h.settled v d hd⟩

end WeightedMIS.Dijkstra
