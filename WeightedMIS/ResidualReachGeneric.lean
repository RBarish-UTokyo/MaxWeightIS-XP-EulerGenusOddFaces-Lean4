module

public import WeightedMIS.ReachSeen
public import WeightedMIS.GraphReachEncoded

/-!
# Word-list reachability refines the abstract search for any relation

`ResidualListReach.explore_encoded` relates the word-level residual search to
`MaxFlowListReach.explore` for the residual relation of a feasible flow. The
proof only uses that the word-level crossing scan returns the encoding of the
abstract crossing. This file states that refinement for an arbitrary relation
and an arbitrary arc table whose crossing scan agrees with the abstract one.

The instance used by the recovery stage is the table of all ordered vertex
pairs, in `List.product` order, filtered by graph adjacency, with the unit
capacity word. The search from the root word then stores, for every vertex,
the reverse of the route of `GraphSearch.search` encoded as arcs; every stored
route pair is adjacent.
-/

@[expose] public section

namespace WeightedMIS.ResidualReachGeneric

open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords
open WeightedMIS.ResidualCrossingRefinement (encodeArc encoded_list_membership)
open WeightedMIS.GraphReachEncoded

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V] {n b : ℕ}

/-- The word-level search follows the abstract list search of any relation
whenever the word-level crossing scan is the encoded abstract crossing. -/
theorem explore_encoded_rel (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (rel : V → V → Prop) [DecidableRel rel] (nodes : List V) (caps : V → V → Bits b)
    (d : Bits b) (table : List (Arc n b))
    (hcross : ∀ seen : List V, RegisterResidualCrossing.crossing (seen.map enc) d table =
      (MaxFlowReach.crossing rel nodes seen.toFinset).map (encodeArc enc caps))
    (fuel : ℕ) (q : MaxFlowListReach.State V) :
    ResidualListReach.explore table d fuel (ResidualListReach.encodeState enc d q) =
      ResidualListReach.encodeState enc d (MaxFlowListReach.explore rel nodes fuel q) := by
  induction fuel generalizing q with
  | zero => rfl
  | succ fuel ih =>
    simp only [ResidualListReach.explore, MaxFlowListReach.explore]
    change (match RegisterResidualCrossing.crossing (q.seen.map enc) d table with
      | none => ResidualListReach.encodeState enc d q
      | some a => ResidualListReach.explore table d fuel
          (ResidualListReach.extend (ResidualListReach.encodeState enc d q) d a)) = _
    rw [hcross q.seen]
    cases he : MaxFlowReach.crossing rel nodes q.seen.toFinset with
    | none => rfl
    | some a =>
      simp only [Option.map_some]
      rw [ResidualListReach.extend_encoded enc hinj, ih]

/-- The crossing scan of a filtered product table with capacities at least the
threshold is the encoded abstract crossing. -/
theorem crossing_filter (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (rel : V → V → Prop) [DecidableRel rel] (nodes : List V) (caps : V → V → Bits b)
    (d : Bits b) (hcaps : ∀ u v, d.value ≤ (caps u v).value) (seen : List V) :
    RegisterResidualCrossing.crossing (seen.map enc) d
        (((nodes.product nodes).filter (fun a => decide (rel a.1 a.2))).map (encodeArc enc caps)) =
      (MaxFlowReach.crossing rel nodes seen.toFinset).map (encodeArc enc caps) := by
  unfold RegisterResidualCrossing.crossing MaxFlowReach.crossing
  rw [List.find?_map, List.find?_filter]
  congr 1
  apply congrArg (fun pred => (nodes.product nodes).find? pred)
  funext a
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq]
  rw [RegisterResidualPredicate.accepts_iff]
  simp only [encodeArc, encoded_list_membership enc hinj, List.mem_toFinset]
  have hc := hcaps a.1 a.2
  tauto

/-- Stored reverse routes of the encoded search are the reversed abstract routes. -/
theorem lookup_explore (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (rel : V → V → Prop) [DecidableRel rel] (nodes : List V) (caps : V → V → Bits b)
    (d : Bits b) (table : List (Arc n b))
    (hcross : ∀ seen : List V, RegisterResidualCrossing.crossing (seen.map enc) d table =
      (MaxFlowReach.crossing rel nodes seen.toFinset).map (encodeArc enc caps))
    (fuel : ℕ) (s v : V) :
    RegisterRouteLookup.lookup (enc v)
        (ResidualListReach.explore table d fuel (ResidualListReach.initial (enc s))).routes =
      ((MaxFlowReach.explore rel nodes fuel (MaxFlowReach.initial s)).route v).reverse.map
        (encodeArc enc (fun _ _ => d)) := by
  have hi := explore_encoded_rel enc hinj rel nodes caps d table hcross fuel
    (MaxFlowListReach.initial s)
  rw [ResidualListReach.encode_initial] at hi
  rw [hi, ← MaxFlowListReach.decode_initial, ← MaxFlowListReach.explore_refines]
  simp only [ResidualListReach.encodeState, MaxFlowListReach.decode, List.reverse_reverse]
  exact ResidualListReach.lookup_encoded enc hinj d _ v

omit [Fintype V] in
/-- Every pair on every stored abstract route is related. -/
theorem explore_supported (rel : V → V → Prop) [DecidableRel rel] (nodes : List V)
    (fuel : ℕ) (q : MaxFlowReach.State V) (hq : ∀ v, ∀ a ∈ q.route v, rel a.1 a.2) :
    ∀ v, ∀ a ∈ (MaxFlowReach.explore rel nodes fuel q).route v, rel a.1 a.2 := by
  induction fuel generalizing q with
  | zero => exact hq
  | succ fuel ih =>
    simp only [MaxFlowReach.explore]
    split
    · exact hq
    · rename_i a ha
      apply ih
      have hc := MaxFlowReach.crossing_some rel nodes q.seen a ha
      intro v x hx
      simp only [MaxFlowReach.extend] at hx
      split at hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact hq a.1 x hx
        · rw [List.mem_singleton.mp hx]
          exact hc.2.2
      · exact hq v x hx

end Generic

/-! ## The adjacency table of a graph -/

section Graph

variable {W n m : ℕ} (left right : Fin m → Fin n)

/-- All ordered adjacent vertex pairs in `List.product` order, with unit capacity. -/
def adjTable (W : ℕ) : List (Arc W 1) :=
  (((List.finRange n).product (List.finRange n)).filter
      (fun a => decide (GraphSearch.Adjacent left right (List.finRange m) a.1 a.2))).map
    (encodeArc (fun v : Fin n => word W v.val) (fun _ _ => one))

theorem word_value_injective (hn : n < 2 ^ W) :
    Function.Injective (fun v : Fin n => (word W v.val).value) := by
  intro v w h
  simp only [word_value (show v.val < 2 ^ W by omega),
    word_value (show w.val < 2 ^ W by omega)] at h
  exact Fin.ext h

theorem adjTable_crossing (hn : n < 2 ^ W) (seen : List (Fin n)) :
    RegisterResidualCrossing.crossing (seen.map fun v => word W v.val) one (adjTable left right W) =
      (MaxFlowReach.crossing (GraphSearch.Adjacent left right (List.finRange m))
        (List.finRange n) seen.toFinset).map
        (encodeArc (fun v : Fin n => word W v.val) (fun _ _ => one)) :=
  crossing_filter _ (word_value_injective hn) _ _ _ one (fun _ _ => le_refl _) seen

/-- The stored reverse route of every vertex is the reversed route of
`GraphSearch.search`, encoded with unit capacities. -/
theorem lookup_search (hn : n < 2 ^ W) (root v : Fin n) :
    RegisterRouteLookup.lookup (word W v.val)
        (ResidualListReach.explore (adjTable left right W) one (rangeWords W n).length
          (ResidualListReach.initial (word W root.val))).routes =
      ((GraphSearch.search left right (List.finRange m) (List.finRange n) root).route v).reverse.map
        (encodeArc (fun v : Fin n => word W v.val) (fun _ _ => one)) := by
  have hl : (rangeWords W n).length = Fintype.card (Fin n) := by simp [rangeWords]
  rw [hl]
  exact lookup_explore (fun v : Fin n => word W v.val) (word_value_injective hn) _ _ _ one _
    (adjTable_crossing left right hn) _ root v

/-- Every pair of every route of `GraphSearch.search` is adjacent. -/
theorem search_supported (root v : Fin n) :
    ∀ a ∈ (GraphSearch.search left right (List.finRange m) (List.finRange n) root).route v,
      GraphSearch.Adjacent left right (List.finRange m) a.1 a.2 :=
  explore_supported _ _ _ _ (fun _ a ha => by simp [MaxFlowReach.initial] at ha) v

end Graph

end WeightedMIS.ResidualReachGeneric
