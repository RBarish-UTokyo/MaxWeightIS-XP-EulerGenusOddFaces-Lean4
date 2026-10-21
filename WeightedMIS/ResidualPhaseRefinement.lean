module

public import WeightedMIS.ResidualListPhase
public import WeightedMIS.ResidualUpdateRefinement

/-! # Binary residual phases refine the actual capacity-scaling algorithm -/

@[expose] public section

namespace WeightedMIS.ResidualPhaseRefinement

open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords
open WeightedMIS.ResidualCrossingRefinement WeightedMIS.ResidualListReach

variable {V : Type*} [Fintype V] [DecidableEq V] {n b : ℕ}

def listSearch (c : V → V → ℕ) (nodes : List V) (s : V) (d : ℕ) (f : V → V → ℤ) :=
  MaxFlowListReach.explore (MaxFlowScaling.relation c f d) nodes (Fintype.card V)
    (MaxFlowListReach.initial s)

theorem listSearch_decode (c : V → V → ℕ) (nodes : List V) (s : V) (d : ℕ)
    (f : V → V → ℤ) : MaxFlowListReach.decode (listSearch c nodes s d f) =
      MaxFlowScaling.search c nodes s d f := by
  rw [listSearch, MaxFlowListReach.explore_refines, MaxFlowListReach.decode_initial]
  rfl

theorem search_encoded (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value)) (caps : V → V → Bits b)
    (c : V → V → ℕ) (s t : V) (f : V → V → ℤ) (hf : MaxFlowCore.Feasible c s t f)
    (hcap : ∀ u v, (caps u v).value = MaxFlowResidual.matrix c f u v)
    (nodes : List V) (hlen : nodes.length = Fintype.card V) (d : Bits b) :
    ResidualListPhase.search ((nodes.product nodes).map (encodeArc enc caps)) d
      (nodes.map enc) (enc s) = encodeState enc d (listSearch c nodes s d.value f) := by
  unfold ResidualListPhase.search
  rw [List.length_map, hlen, ← encode_initial enc d]
  exact explore_encoded enc hinj caps c s t f hf hcap nodes d _ _

theorem found_map (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value)) (seen : List V) (v : V) :
    RegisterMembership.found (enc v) (seen.map enc) = decide (v ∈ seen) := by
  apply Bool.eq_iff_iff.mpr
  rw [RegisterMembership.found_iff, decide_eq_true_eq]
  exact encoded_list_membership enc hinj seen v

/-- The capacities are the words actually produced by the phase. Their
matrix values and reached cut agree with the integer-flow specification. -/
def Represents (enc : V → Bits n) (nodes : List V) (c : V → V → ℕ) (s t : V)
    (words : ResidualListPhase.Result n b) (result : MaxFlowScaling.Result V) : Prop :=
  MaxFlowCore.Feasible c s t result.flow ∧
    ∃ caps : V → V → Bits b,
      words.table = (nodes.product nodes).map (encodeArc enc caps) ∧
      (∀ u v, (caps u v).value = MaxFlowResidual.matrix c result.flow u v) ∧
      words.seen.toFinset = result.cut.image enc

theorem phase_refines (enc : V → Bits n)
    (hinj : Function.Injective (fun v => (enc v).value))
    (c : V → V → ℕ) (s t : V) (nodes : List V) (complete : ∀ v, v ∈ nodes)
    (hlen : nodes.length = Fintype.card V) (d : Bits b) (fuel : ℕ)
    (f : V → V → ℤ) (hf : MaxFlowCore.Feasible c s t f)
    (caps : V → V → Bits b)
    (hcap : ∀ u v, (caps u v).value = MaxFlowResidual.matrix c f u v)
    (hwidth : ∀ u v, c u v + c v u < 2 ^ b) :
    Represents enc nodes c s t
      (ResidualListPhase.phase d (nodes.map enc) (enc s) (enc t) fuel
        ((nodes.product nodes).map (encodeArc enc caps)))
      (MaxFlowScaling.phase c nodes s t d.value fuel f) := by
  induction fuel generalizing f caps with
  | zero =>
    refine ⟨hf, caps, rfl, hcap, ?_⟩
    change (ResidualListPhase.search _ d _ _).seen.toFinset =
      (MaxFlowScaling.search c nodes s d.value f).seen.image enc
    rw [search_encoded enc hinj caps c s t f hf hcap nodes hlen d,
      ← listSearch_decode c nodes s d.value f]
    simp only [encodeState, MaxFlowListReach.decode]
    ext key
    simp
  | succ fuel ih =>
    let q := listSearch c nodes s d.value f
    have hsearch := search_encoded enc hinj caps c s t f hf hcap nodes hlen d
    have hdecode := listSearch_decode c nodes s d.value f
    have hseen : q.seen.toFinset = (MaxFlowScaling.search c nodes s d.value f).seen :=
      congrArg MaxFlowReach.State.seen hdecode
    have hroute : (MaxFlowListReach.lookup q.routes t).reverse =
        (MaxFlowScaling.search c nodes s d.value f).route t :=
      congrArg (fun state : MaxFlowReach.State V => state.route t) hdecode
    have hfound : RegisterMembership.found (enc t)
        (ResidualListPhase.search ((nodes.product nodes).map (encodeArc enc caps))
          d (nodes.map enc) (enc s)).seen = decide (t ∈ q.seen) := by
      rw [hsearch]
      exact found_map enc hinj q.seen t
    have hmem : t ∈ (MaxFlowScaling.search c nodes s d.value f).seen ↔ t ∈ q.seen := by
      rw [← hseen, List.mem_toFinset]
    by_cases ht : t ∈ q.seen
    · have spec := MaxFlowListReach.search_spec (MaxFlowScaling.relation c f d.value)
        nodes complete s t
      have hp := spec.2.1 ht
      let path := MaxFlowListReach.lookup q.routes t
      have hwalk : ShortestPath.IsWalk Prod.fst Prod.snd s t path.reverse := hp.1
      have hnodup : path.reverse.Nodup := MaxFlowCore.simple_nodup hp.2.1
      have hsupported : ∀ a ∈ path.reverse, (d.value : ℤ) ≤ MaxFlowCore.residual c f a.1 a.2 := by
        intro a ha
        exact hp.2.2 a (List.mem_reverse.mp ha)
      let nextFlow := MaxFlowCore.augment f path.reverse d.value
      have hnext : MaxFlowCore.Feasible c s t nextFlow :=
        MaxFlowCore.augment_feasible c s t f hf path.reverse hwalk hnodup d.value hsupported
      let nextCaps := ResidualUpdateRefinement.updatedCaps enc caps (fun _ _ => d) path d
      have hnextCaps (u v : V) : (nextCaps u v).value = MaxFlowResidual.matrix c nextFlow u v := by
        have hu := ResidualUpdateRefinement.updatedCaps_value enc hinj caps (fun _ _ => d)
          c s t f hf hcap path.reverse hwalk hnodup d hsupported hwidth u v
        simpa only [nextCaps, nextFlow, ResidualUpdateRefinement.updatedCaps, List.map_reverse,
          RegisterResidualUpdate.update_reverse] using hu
      have recur := ih nextFlow hnext nextCaps hnextCaps
      have hpath : RegisterRouteLookup.lookup (enc t)
          (ResidualListPhase.search ((nodes.product nodes).map (encodeArc enc caps))
            d (nodes.map enc) (enc s)).routes = path.map (encodeArc enc (fun _ _ => d)) := by
        rw [hsearch]
        exact lookup_encoded enc hinj d q.routes t
      have htable := ResidualUpdateRefinement.table_map enc caps (fun _ _ => d)
        path (nodes.product nodes) d
      have hold : t ∈ (MaxFlowScaling.search c nodes s d.value f).seen := hmem.mpr ht
      simp only [ResidualListPhase.phase, hfound, ht, decide_true,
        ↓reduceIte, hpath, htable, MaxFlowScaling.phase, hold] at ⊢
      have heflow : MaxFlowCore.augment f ((MaxFlowScaling.search c nodes s d.value f).route t) d.value =
          nextFlow := by rw [← hroute]
      rw [heflow]
      exact recur
    · have hold : t ∉ (MaxFlowScaling.search c nodes s d.value f).seen := mt hmem.mp ht
      simp only [ResidualListPhase.phase, hfound, ht, decide_false, Bool.false_eq_true,
        ↓reduceIte, MaxFlowScaling.phase, hold]
      refine ⟨hf, caps, rfl, hcap, ?_⟩
      rw [hsearch, ← hseen]
      simp only [encodeState]
      ext key
      simp [q]

end WeightedMIS.ResidualPhaseRefinement
