module

public import WeightedMIS.ComputedOddRow
public import WeightedMIS.InducedReduction

/-!
# Deterministic bipartite detection and all-half recovery

The parity search either reaches the opposite copy of the root or directly
supplies a two-coloring. When the all-half LP point is optimal, either color
class is a maximum-weight independent set. This includes isolated components.
-/

@[expose] public section

namespace WeightedMIS.BipartiteRecovery

open scoped BigOperators
open ComputedOddRow GraphSearch MaxFlowReach Persistence

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The color is the membership bit of the opposite-parity search copy. -/
def coloring (left right : E → V) (edges : List E) (nodes : List V) (root : V) (v : V) : Bool :=
  decide ((v, true) ∈ (paritySearch left right edges nodes root).seen)

/-- If the opposite root is unreachable, each vertex has exactly one reached
parity copy, and edges flip that copy. -/
theorem coloring_correct (left right : E → V) (edges : List E) (hedges : ∀ e, e ∈ edges)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (root : V)
    (hc : Incidence.Connected left right)
    (hno : (root, true) ∉ (paritySearch left right edges nodes root).seen) :
    ∀ e, coloring left right edges nodes root (left e) ≠ coloring left right edges nodes root (right e) := by
  let S := (paritySearch left right edges nodes root).seen
  have hs := search_spec (AdjacentParity left right edges) (parityNodes nodes)
    (parityNodes_complete nodes hnodes) (root, false) (root, true)
  change (root, false) ∈ S ∧ _ at hs
  have hex (v : V) : (v, false) ∈ S ∨ (v, true) ∈ S := by
    obtain ⟨n, p⟩ := hc root v
    have hv := closed_walk_phase left right edges hedges S hs.2.2 p false hs.1
    cases h : phase n false <;> simp only [h] at hv
    · exact Or.inl hv
    · exact Or.inr hv
  have hnotboth (v : V) : ¬ ((v, false) ∈ S ∧ (v, true) ∈ S) := by
    rintro ⟨hf, ht⟩
    obtain ⟨n, p⟩ := hc v root
    have hf' := closed_walk_phase left right edges hedges S hs.2.2 p false hf
    have ht' := closed_walk_phase left right edges hedges S hs.2.2 p true ht
    by_cases hn : n % 2 = 0
    · exact hno (by simpa only [phase, ite_eq_left hn] using ht')
    · exact hno (by simpa only [phase, ite_eq_right hn, Bool.not_false] using hf')
  have hedge (e : E) (b : Bool) (hb : (left e, b) ∈ S) : (right e, !b) ∈ S := by
    by_contra hn
    apply hs.2.2 (left e, b) hb (right e, !b) hn
    refine ⟨?_, rfl⟩
    exact (adjacent_iff left right edges hedges _ _).mpr ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  intro e heq
  have heq' : ((left e, true) ∈ S) ↔ ((right e, true) ∈ S) := by
    have h := congrArg (fun b : Bool => b = true) heq
    simpa only [coloring, decide_eq_true_eq, S] using h.to_iff
  by_cases hl : (left e, true) ∈ S
  · have hr := hedge e true hl
    exact hnotboth (right e) ⟨by simpa using hr, heq'.mp hl⟩
  · have hlf := (hex (left e)).resolve_right hl
    have hr := hedge e false hlf
    exact hl (heq'.mpr (by simpa using hr))

/-- The rational characteristic vector is feasible for every independent set. -/
theorem indicator_feasible (adj : V → V → Prop) (I : Finset V) (hi : Independent adj I) :
    Feasible adj (indicator I) := by
  constructor
  · intro v
    by_cases hv : v ∈ I <;> simp [indicator, hv]
  · intro u v huv
    have hh := hi u v huv
    by_cases hu : u ∈ I <;> by_cases hv : v ∈ I <;> simp_all [indicator]

def colorClass (color : V → Bool) (b : Bool) : Finset V := Finset.univ.filter fun v => color v = b

theorem colorClass_independent (adj : V → V → Prop) (color : V → Bool)
    (hc : ∀ u v, adj u v → color u ≠ color v) (b : Bool) :
    Independent adj (colorClass color b) := by
  intro u v huv hu hv
  have hu' : color u = b := by simpa [colorClass] using hu
  have hv' : color v = b := by simpa [colorClass] using hv
  exact hc u v huv (hu'.trans hv'.symm)

/-- The two color objectives add to twice the all-half objective. -/
theorem colorClass_weight_sum (w : V → ℚ) (color : V → Bool) :
    weight w (colorClass color false) + weight w (colorClass color true) =
      2 * objective w (fun _ => 1 / 2) := by
  unfold weight objective
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  cases hv : color v <;> simp [indicator, colorClass, hv] <;> ring

/-- Every color class of an all-half optimal bipartite instance is an actual
maximum independent set, for arbitrary rational vertex weights. -/
theorem colorClass_maximum (adj : V → V → Prop) (w : V → ℚ) (color : V → Bool)
    (hc : ∀ u v, adj u v → color u ≠ color v)
    (ho : Optimal adj w (fun _ => 1 / 2)) (b : Bool) :
    Independent adj (colorClass color b) ∧
      weight w (colorClass color b) = objective w (fun _ => 1 / 2) ∧
      ∀ J, Independent adj J → weight w J ≤ weight w (colorClass color b) := by
  have h0 := colorClass_independent adj color hc false
  have h1 := colorClass_independent adj color hc true
  have hb0 := ho.2 _ (indicator_feasible adj _ h0)
  have hb1 := ho.2 _ (indicator_feasible adj _ h1)
  change weight w (colorClass color false) ≤ _ at hb0
  change weight w (colorClass color true) ≤ _ at hb1
  have hsum := colorClass_weight_sum w color
  have he : weight w (colorClass color b) = objective w (fun _ => 1 / 2) := by
    cases b <;> linarith
  refine ⟨colorClass_independent adj color hc b, he, ?_⟩
  intro J hJ
  rw [he]
  exact ho.2 _ (indicator_feasible adj J hJ)

/-- The negative result of the actual parity search produces an optimum for
an all-half residual component. -/
theorem searched_color_maximum (left right : E → V) (edges : List E) (hedges : ∀ e, e ∈ edges)
    (nodes : List V) (hnodes : ∀ v, v ∈ nodes) (root : V)
    (hc : Incidence.Connected left right)
    (hno : (root, true) ∉ (paritySearch left right edges nodes root).seen)
    (w : V → ℚ) (ho : Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2)) :
    let I := colorClass (coloring left right edges nodes root) false
    Independent (EdgeTransport.Adj left right) I ∧
      ∀ J, Independent (EdgeTransport.Adj left right) J → weight w J ≤ weight w I := by
  have hcol := coloring_correct left right edges hedges nodes hnodes root hc hno
  have hne : ∀ u v, EdgeTransport.Adj left right u v →
      coloring left right edges nodes root u ≠ coloring left right edges nodes root v := by
    rintro u v ⟨e, ⟨hl, hr⟩ | ⟨hl, hr⟩⟩
    · simpa only [hl, hr] using hcol e
    · simpa only [hl, hr, ne_comm] using hcol e
  have hm := colorClass_maximum (EdgeTransport.Adj left right) w
    (coloring left right edges nodes root) hne ho false
  exact ⟨hm.1, hm.2.2⟩

end WeightedMIS.BipartiteRecovery
