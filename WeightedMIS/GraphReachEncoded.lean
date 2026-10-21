module

public import WeightedMIS.ReachSeen
public import WeightedMIS.ComputedComponents
public import WeightedMIS.BipartiteRecovery
public import WeightedMIS.SparseSearchGraph

/-!
# Encoded graph reachability, component roots and parity colorings

Vertices are fixed-width words `word W v`. An edge list of endpoint words
yields two residual arcs per edge (adjacency) or four (parity double cover,
whose vertex words carry the parity bit as their leading bit). All arcs have
capacity word `one` and the search threshold is `one`, so every arc is usable
and the word-level residual search `ResidualListReach.explore` computes plain
reachability.

The encoded reached sets, root tests, root lists, parity membership and color
classes agree with `ComputedComponents.routes`, `ComputedComponents.roots`,
`ComputedOddRow.paritySearch` and `BipartiteRecovery.colorClass`.
-/

@[expose] public section

namespace WeightedMIS.GraphReachEncoded

open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords
open WeightedMIS.ResidualListReach (ArcRel found_iff_mem)

/-- A natural number as a fixed-width big-endian word. -/
def word (W i : ℕ) : Bits W := SparseSearchGraph.encodeBits W i

theorem word_value {W i : ℕ} (h : i < 2 ^ W) : (word W i).value = i :=
  SparseSearchGraph.encodeBits_value W i h

theorem word_injective {W n : ℕ} (hn : n < 2 ^ W) {v w : Fin n}
    (h : word W v.val = word W w.val) : v = w :=
  Fin.ext (SparseSearchGraph.encodeBits_injective (by omega) (by omega) h)

theorem word_eq_iff {W n : ℕ} (hn : n < 2 ^ W) (v w : Fin n) :
    word W v.val = word W w.val ↔ v = w :=
  ⟨word_injective hn, fun h => h ▸ rfl⟩

/-- The unit capacity and threshold word. -/
def one : Bits 1 := .cons true .nil

@[simp] theorem one_value : one.value = 1 := by simp [one, Bits.value]

/-- The words of all vertices in ascending order. -/
def rangeWords (W n : ℕ) : List (Bits W) := (List.finRange n).map fun v => word W v.val

theorem rangeWords_eq_range (W n : ℕ) : rangeWords W n = (List.range n).map (word W) := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  rfl

theorem mem_rangeWords (W : ℕ) {n : ℕ} (v : Fin n) : word W v.val ∈ rangeWords W n :=
  List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩

theorem filter_rangeWords (W n : ℕ) (p : Bits W → Bool) :
    (rangeWords W n).filter p =
      ((List.finRange n).filter fun v => p (word W v.val)).map fun v => word W v.val := by
  rw [rangeWords, List.filter_map]
  rfl

/-- A finite vertex set as its ascending list of words. -/
def setWords (W : ℕ) {k : ℕ} (S : Finset (Fin k)) : List (Bits W) :=
  ((List.finRange k).filter (· ∈ S)).map fun v => word W v.val

/-- The endpoint words of all edges, in edge order. -/
def edgeWords (W : ℕ) {n m : ℕ} (left right : Fin m → Fin n) : List (Bits W × Bits W) :=
  (List.finRange m).map fun e => (word W (left e).val, word W (right e).val)

/-- Both orientations of every edge, with unit capacity. -/
def adjArcs {W : ℕ} (edges : List (Bits W × Bits W)) : List (Arc W 1) :=
  edges.flatMap fun p => [⟨p.1, p.2, one⟩, ⟨p.2, p.1, one⟩]

/-- A parity copy of a vertex word: the parity bit is the leading bit. -/
def parityWord {W : ℕ} (b : Bool) (v : Bits W) : Bits (W + 1) := .cons b v

theorem parityWord_eq_iff {W : ℕ} (b c : Bool) (v w : Bits W) :
    parityWord b v = parityWord c w ↔ b = c ∧ v = w := by
  simp [parityWord]

/-- Four parity-flipping arcs per edge `(l, r)`:
`(l,f)→(r,t)`, `(l,t)→(r,f)`, `(r,t)→(l,f)`, `(r,f)→(l,t)`. -/
def parityArcs {W : ℕ} (edges : List (Bits W × Bits W)) : List (Arc (W + 1) 1) :=
  edges.flatMap fun p =>
    [⟨parityWord false p.1, parityWord true p.2, one⟩,
     ⟨parityWord true p.1, parityWord false p.2, one⟩,
     ⟨parityWord true p.2, parityWord false p.1, one⟩,
     ⟨parityWord false p.2, parityWord true p.1, one⟩]

/-- Both parity copies of every vertex word. -/
def parityNodeWords {W : ℕ} (nodes : List (Bits W)) : List (Bits (W + 1)) :=
  nodes.flatMap fun v => [parityWord false v, parityWord true v]

/-- The reached words of the residual search with unit threshold. -/
def reachE {k : ℕ} (table : List (Arc k 1)) (nodes : List (Bits k)) (s : Bits k) :
    List (Bits k) :=
  (ResidualListReach.explore table one nodes.length (ResidualListReach.initial s)).seen

/-- The reached parity copies from the even copy of `root`. -/
def parityReachE {W : ℕ} (edges : List (Bits W × Bits W)) (nodes : List (Bits W))
    (root : Bits W) : List (Bits (W + 1)) :=
  reachE (parityArcs edges) (parityNodeWords nodes) (parityWord false root)

/-- A vertex names its component when no reached vertex has a smaller value. -/
def isRootE {W : ℕ} (seen : List (Bits W)) (v : Bits W) : Bool :=
  seen.all fun u => decide (v.value ≤ u.value)

def rootsE {W : ℕ} (edges : List (Bits W × Bits W)) (nodes : List (Bits W)) : List (Bits W) :=
  nodes.filter fun v => isRootE (reachE (adjArcs edges) nodes v) v

/-- The vertices whose odd parity copy is not reached. -/
def colorWordsE {W : ℕ} (seen : List (Bits (W + 1))) (nodes : List (Bits W)) : List (Bits W) :=
  nodes.filter fun v => !RegisterMembership.found (parityWord true v) seen

/-! ## Arc relations of the encoded tables -/

theorem adjArcs_rel {W : ℕ} (edges : List (Bits W × Bits W)) (u y : Bits W) :
    ArcRel (adjArcs edges) one u y ↔
      ∃ p ∈ edges, (u = p.1 ∧ y = p.2) ∨ (u = p.2 ∧ y = p.1) := by
  constructor
  · rintro ⟨a, ha, rfl, rfl, -⟩
    obtain ⟨p, hp, ha⟩ := List.mem_flatMap.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨p, hp, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨p, hp, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨p, hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨⟨p.1, p.2, one⟩, List.mem_flatMap.mpr ⟨p, hp, by simp⟩, rfl, rfl, le_refl _⟩
    · exact ⟨⟨p.2, p.1, one⟩, List.mem_flatMap.mpr ⟨p, hp, by simp⟩, rfl, rfl, le_refl _⟩

theorem parityArcs_rel {W : ℕ} (edges : List (Bits W × Bits W)) (u y : Bits (W + 1)) :
    ArcRel (parityArcs edges) one u y ↔
      ∃ p ∈ edges, ∃ c : Bool, (u = parityWord c p.1 ∧ y = parityWord (!c) p.2) ∨
        (u = parityWord c p.2 ∧ y = parityWord (!c) p.1) := by
  constructor
  · rintro ⟨a, ha, rfl, rfl, -⟩
    obtain ⟨p, hp, ha⟩ := List.mem_flatMap.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨p, hp, false, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨p, hp, true, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨p, hp, true, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨p, hp, false, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨p, hp, c, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> cases c
    · exact ⟨⟨parityWord false p.1, parityWord true p.2, one⟩,
        List.mem_flatMap.mpr ⟨p, hp, by simp⟩, rfl, rfl, le_refl _⟩
    · exact ⟨⟨parityWord true p.1, parityWord false p.2, one⟩,
        List.mem_flatMap.mpr ⟨p, hp, by simp⟩, rfl, rfl, le_refl _⟩
    · exact ⟨⟨parityWord false p.2, parityWord true p.1, one⟩,
        List.mem_flatMap.mpr ⟨p, hp, by simp⟩, rfl, rfl, le_refl _⟩
    · exact ⟨⟨parityWord true p.2, parityWord false p.1, one⟩,
        List.mem_flatMap.mpr ⟨p, hp, by simp⟩, rfl, rfl, le_refl _⟩

theorem mem_parityNodeWords {W : ℕ} (nodes : List (Bits W)) (b : Bool) (v : Bits W)
    (hv : v ∈ nodes) : parityWord b v ∈ parityNodeWords nodes :=
  List.mem_flatMap.mpr ⟨v, hv, by cases b <;> simp⟩

section Graph

variable {W n m : ℕ} (left right : Fin m → Fin n)

theorem mem_edgeWords (p : Bits W × Bits W) :
    p ∈ edgeWords W left right ↔ ∃ e, p = (word W (left e).val, word W (right e).val) := by
  simp [edgeWords, eq_comm]

/-- Encoded adjacency steps are exactly graph adjacencies. -/
theorem adj_step (hn : n < 2 ^ W) (a : Fin n) (y : Bits W) :
    ArcRel (adjArcs (edgeWords W left right)) one (word W a.val) y ↔
      ∃ c, y = word W c.val ∧ GraphSearch.Adjacent left right (List.finRange m) a c := by
  simp only [adjArcs_rel, GraphSearch.adjacent_iff left right _ (fun e => List.mem_finRange e),
    EdgeTransport.Adj]
  constructor
  · rintro ⟨p, hp, h⟩
    obtain ⟨e, rfl⟩ := (mem_edgeWords left right p).mp hp
    rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · exact ⟨right e, rfl, e, Or.inl ⟨(word_injective hn h1).symm, rfl⟩⟩
    · exact ⟨left e, rfl, e, Or.inr ⟨rfl, (word_injective hn h1).symm⟩⟩
  · rintro ⟨c, rfl, e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨_, (mem_edgeWords left right _).mpr ⟨e, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, (mem_edgeWords left right _).mpr ⟨e, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem adj_targets (a : Arc W 1) (ha : a ∈ adjArcs (edgeWords W left right)) :
    RegisterMembership.found a.target (rangeWords W n) = true := by
  rw [found_iff_mem]
  obtain ⟨p, hp, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨e, rfl⟩ := (mem_edgeWords left right p).mp hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact mem_rangeWords W (right e)
  · exact mem_rangeWords W (left e)

theorem rtg_adj_iff (hn : n < 2 ^ W) (root : Fin n) (y : Bits W) :
    Relation.ReflTransGen (ArcRel (adjArcs (edgeWords W left right)) one) (word W root.val) y ↔
      ∃ v, y = word W v.val ∧ v ∈ (ComputedComponents.routes left right root).seen := by
  rw [ReachSeen.rtg_encode (GraphSearch.Adjacent left right (List.finRange m)) _
    (fun v : Fin n => word W v.val) (adj_step left right hn)]
  simp only [ComputedComponents.routes, GraphSearch.search,
    MaxFlowReach.seen_iff_rtg _ _ (fun v => List.mem_finRange v)]

/-- The encoded adjacency search reaches exactly the component of the source. -/
theorem found_reach_iff (hn : n < 2 ^ W) (root v : Fin n) :
    RegisterMembership.found (word W v.val)
        (reachE (adjArcs (edgeWords W left right)) (rangeWords W n) (word W root.val)) = true ↔
      v ∈ (ComputedComponents.routes left right root).seen := by
  rw [reachE, ResidualListReach.found_explore_iff _ _ _ _
    ((found_iff_mem _ _).mpr (mem_rangeWords W root)) (adj_targets left right),
    rtg_adj_iff left right hn]
  constructor
  · rintro ⟨u, hu, hs⟩
    rwa [word_injective hn hu]
  · intro hv
    exact ⟨v, rfl, hv⟩

theorem found_reach_iff_reachable (hn : n < 2 ^ W) (root v : Fin n) :
    RegisterMembership.found (word W v.val)
        (reachE (adjArcs (edgeWords W left right)) (rangeWords W n) (word W root.val)) = true ↔
      Incidence.Reachable left right root v := by
  rw [found_reach_iff left right hn, ComputedComponents.seen_iff_reachable]

/-- Every encoded reached word is the word of a reached vertex. -/
theorem mem_reach (hn : n < 2 ^ W) (root : Fin n) (x : Bits W)
    (hx : x ∈ reachE (adjArcs (edgeWords W left right)) (rangeWords W n) (word W root.val)) :
    ∃ v, x = word W v.val ∧ v ∈ (ComputedComponents.routes left right root).seen := by
  rw [← rtg_adj_iff left right hn]
  exact (ResidualListReach.mem_explore_iff _ _ _ _ (mem_rangeWords W root)
    (fun a ha => (found_iff_mem _ _).mp (adj_targets left right a ha)) x).mp hx

theorem find?_finRange_le {k : ℕ} (p : Fin k → Bool) (r : Fin k)
    (hr : (List.finRange k).find? p = some r) (u : Fin k) (hu : p u = true) : r ≤ u := by
  obtain ⟨-, as, bs, hl, hnot⟩ := List.find?_eq_some_iff_append.mp hr
  have hmem : u ∈ as ++ r :: bs := hl ▸ List.mem_finRange u
  have hpw := List.pairwise_lt_finRange k
  rw [hl, List.pairwise_append] at hpw
  rcases List.mem_append.mp hmem with hu' | hu'
  · have := hnot u hu'
    simp [hu] at this
  · rcases List.mem_cons.mp hu' with rfl | hu'
    · exact le_refl _
    · exact le_of_lt (List.rel_of_pairwise_cons hpw.2.1 hu')

/-- A vertex is its own representative exactly when it is the least reached vertex. -/
theorem representative_eq_self_iff (v : Fin n) :
    ComputedComponents.representative left right v = v ↔
      ∀ u ∈ (ComputedComponents.routes left right v).seen, v ≤ u := by
  have hself : v ∈ (ComputedComponents.routes left right v).seen :=
    (ComputedComponents.seen_iff_reachable left right v v).mpr
      (Incidence.reachable_refl left right v)
  cases hf : ComputedComponents.firstReached left right v with
  | none => exact (ComputedComponents.firstReached_ne_none left right v hf).elim
  | some r =>
    have hr : r ∈ (ComputedComponents.routes left right v).seen := by
      simpa using List.find?_some hf
    have hle := fun u hu => find?_finRange_le _ r hf u (by simpa using hu)
    simp only [ComputedComponents.representative, hf, Option.getD_some]
    constructor
    · rintro rfl
      exact hle
    · intro h
      exact le_antisymm (hle v hself) (h r hr)

/-- The encoded root test decides the computed representative condition. -/
theorem isRoot_iff (hn : n < 2 ^ W) (v : Fin n) :
    isRootE (reachE (adjArcs (edgeWords W left right)) (rangeWords W n) (word W v.val))
        (word W v.val) = true ↔
      ComputedComponents.representative left right v = v := by
  rw [representative_eq_self_iff, isRootE, List.all_eq_true]
  constructor
  · intro h u hu
    have hx := (found_iff_mem _ _).mp ((found_reach_iff left right hn v u).mpr hu)
    have := h _ hx
    simp only [decide_eq_true_eq, word_value (show v.val < 2 ^ W by omega),
      word_value (show u.val < 2 ^ W by omega)] at this
    exact Fin.le_def.mpr this
  · intro h x hx
    obtain ⟨u, rfl, hu⟩ := mem_reach left right hn v x hx
    simp only [decide_eq_true_eq, word_value (show v.val < 2 ^ W by omega),
      word_value (show u.val < 2 ^ W by omega)]
    exact Fin.le_def.mp (h u hu)

/-- The encoded root list is the word list of the computed roots. -/
theorem roots_encode (hn : n < 2 ^ W) :
    rootsE (edgeWords W left right) (rangeWords W n) =
      (ComputedComponents.roots left right).map fun v => word W v.val := by
  rw [rootsE, filter_rangeWords, ComputedComponents.roots]
  congr 1
  apply List.filter_congr
  intro v _
  exact Bool.eq_iff_iff.mpr ((isRoot_iff left right hn v).trans decide_eq_true_iff.symm)

/-! ## Parity search -/

/-- Parity copies of vertices as words. -/
def parityEnc (W : ℕ) {n : ℕ} (a : Fin n × Bool) : Bits (W + 1) := parityWord a.2 (word W a.1.val)

theorem parityEnc_injective (hn : n < 2 ^ W) : Function.Injective (parityEnc W (n := n)) := by
  rintro ⟨v, b⟩ ⟨w, c⟩ h
  obtain ⟨hb, hv⟩ := (parityWord_eq_iff _ _ _ _).mp h
  simp only at hb hv
  rw [hb, word_injective hn hv]

theorem parity_step (hn : n < 2 ^ W) (a : Fin n × Bool) (y : Bits (W + 1)) :
    ArcRel (parityArcs (edgeWords W left right)) one (parityEnc W a) y ↔
      ∃ c, y = parityEnc W c ∧ ComputedOddRow.AdjacentParity left right (List.finRange m) a c := by
  obtain ⟨v, b⟩ := a
  simp only [parityArcs_rel, ComputedOddRow.AdjacentParity,
    GraphSearch.adjacent_iff left right _ (fun e => List.mem_finRange e), EdgeTransport.Adj,
    parityEnc, parityWord_eq_iff]
  constructor
  · rintro ⟨p, hp, c, h⟩
    obtain ⟨e, rfl⟩ := (mem_edgeWords left right p).mp hp
    rcases h with ⟨⟨rfl, h1⟩, rfl⟩ | ⟨⟨rfl, h1⟩, rfl⟩
    · exact ⟨(right e, !b), rfl, ⟨e, Or.inl ⟨(word_injective hn h1).symm, rfl⟩⟩, rfl⟩
    · exact ⟨(left e, !b), rfl, ⟨e, Or.inr ⟨rfl, (word_injective hn h1).symm⟩⟩, rfl⟩
  · rintro ⟨⟨w, c⟩, rfl, ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hc⟩
    · simp only at hc
      subst hc
      exact ⟨_, (mem_edgeWords left right _).mpr ⟨e, rfl⟩, b, Or.inl ⟨⟨rfl, rfl⟩, rfl⟩⟩
    · simp only at hc
      subst hc
      exact ⟨_, (mem_edgeWords left right _).mpr ⟨e, rfl⟩, b, Or.inr ⟨⟨rfl, rfl⟩, rfl⟩⟩

theorem parity_targets (a : Arc (W + 1) 1) (ha : a ∈ parityArcs (edgeWords W left right)) :
    RegisterMembership.found a.target (parityNodeWords (rangeWords W n)) = true := by
  rw [found_iff_mem]
  obtain ⟨p, hp, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨e, rfl⟩ := (mem_edgeWords left right p).mp hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    exact mem_parityNodeWords _ _ _ (mem_rangeWords W _)

/-- Encoded parity membership is membership in the computed parity search. -/
theorem parity_found_iff (hn : n < 2 ^ W) (root v : Fin n) (b : Bool) :
    RegisterMembership.found (parityWord b (word W v.val))
        (parityReachE (edgeWords W left right) (rangeWords W n) (word W root.val)) = true ↔
      (v, b) ∈ (ComputedOddRow.paritySearch left right (List.finRange m)
        (List.finRange n) root).seen := by
  rw [parityReachE, reachE, ResidualListReach.found_explore_iff _ _ _ _
    ((found_iff_mem _ _).mpr (mem_parityNodeWords _ false _ (mem_rangeWords W root)))
    (parity_targets left right)]
  change Relation.ReflTransGen _ (parityEnc W (root, false)) (parityEnc W (v, b)) ↔ _
  rw [ReachSeen.rtg_encode_iff _ _ _ (parityEnc_injective hn) (parity_step left right hn),
    ComputedOddRow.paritySearch, MaxFlowReach.seen_iff_rtg _ _
      (ComputedOddRow.parityNodes_complete _ (fun v => List.mem_finRange v))]

/-- The encoded color class is the computed color class `false`. -/
theorem colorClass_encode (hn : n < 2 ^ W) (root : Fin n) :
    colorWordsE (parityReachE (edgeWords W left right) (rangeWords W n) (word W root.val))
        (rangeWords W n) =
      setWords W (BipartiteRecovery.colorClass
        (BipartiteRecovery.coloring left right (List.finRange m) (List.finRange n) root) false) := by
  rw [colorWordsE, filter_rangeWords, setWords]
  congr 1
  apply List.filter_congr
  intro v _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', BipartiteRecovery.colorClass, BipartiteRecovery.coloring,
    Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, decide_eq_false_iff_not]
  rw [← Bool.not_eq_true, parity_found_iff left right hn root v true]

end Graph

end WeightedMIS.GraphReachEncoded
