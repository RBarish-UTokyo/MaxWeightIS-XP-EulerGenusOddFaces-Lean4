module

public import WeightedMIS.EdgeTransport
public import WeightedMIS.CachedPreprocessing

/-!
# Deterministic allocation to original edge labels

For each ordered adjacent pair, scan the supplied edge list and select its
first representing edge. Half the ordered-pair transportation mass is assigned
to that label. This is executable even with parallel edges and loops.
-/

@[expose] public section

namespace WeightedMIS.EdgeAllocation

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Whether the given edge represents this undirected vertex pair. -/
def Matches (left right : E → V) (u v : V) (e : E) : Prop :=
  (left e = u ∧ right e = v) ∨ (left e = v ∧ right e = u)

instance (left right : E → V) (u v : V) (e : E) : Decidable (Matches left right u v e) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

/-- The first actual edge label for an ordered vertex pair. -/
def selected (left right : E → V) (edges : List E) (u v : V) : Option E :=
  edges.find? fun e => decide (Matches left right u v e)

theorem selected_some (left right : E → V) (edges : List E) (u v : V) (e : E)
    (he : selected left right edges u v = some e) : Matches left right u v e := by
  simpa only [decide_eq_true_eq] using List.find?_some he

theorem selected_none (left right : E → V) (edges : List E)
    (complete : ∀ e, e ∈ edges) (u v : V)
    (hn : selected left right edges u v = none) : ¬ EdgeTransport.Adj left right u v := by
  rintro ⟨e, he⟩
  have hh := List.find?_eq_none.mp hn e (complete e)
  exact hh (by simpa only [decide_eq_true_eq] using
    (show Matches left right u v e from he))

/-- Allocate half of each ordered-pair mass to its selected edge. -/
def cost (left right : E → V) (edges : List E) (flow : V → V → ℚ) (e : E) : ℚ :=
  ∑ p : V × V, if selected left right edges p.1 p.2 = some e then flow p.1 p.2 / 2 else 0

/-- Option-valued allocation, with absent targets contributing zero. -/
theorem allocate_option {P : Type*} [Fintype P]
    (pick : P → Option E) (mass : P → ℚ) (test : E → Prop) [DecidablePred test] :
    (∑ e, if test e then (∑ p, if pick p = some e then mass p else 0) else 0) =
      ∑ p, match pick p with | none => 0 | some e => if test e then mass p else 0 := by
  calc
    _ = ∑ e, ∑ p, if pick p = some e then (if test e then mass p else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : test e <;> simp [he]
    _ = ∑ p, ∑ e, if pick p = some e then (if test e then mass p else 0) else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      cases hp : pick p <;> simp

/-- The concrete allocation has nonnegative costs and exactly the original
vertex weights whenever both transportation marginals equal those weights. -/
theorem cost_correct (left right : E → V) (edges : List E)
    (complete : ∀ e, e ∈ edges) (w : V → ℚ) (flow : V → V → ℚ)
    (hflow : ∀ u v, 0 ≤ flow u v)
    (hsupport : ∀ u v, ¬ EdgeTransport.Adj left right u v → flow u v = 0)
    (hrow : ∀ u, ∑ v, flow u v = w u) (hcol : ∀ v, ∑ u, flow u v = w v) :
    (∀ e, 0 ≤ cost left right edges flow e) ∧
      ∀ v, Slack.vertexWeight left right (cost left right edges flow) v = w v := by
  constructor
  · intro e
    apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact div_nonneg (hflow _ _) (by norm_num)
    · rfl
  · intro v
    let g : V × V → ℚ := fun p =>
      (if p.1 = v then flow p.1 p.2 / 2 else 0) +
      (if p.2 = v then flow p.1 p.2 / 2 else 0)
    have hh : Slack.vertexWeight left right (cost left right edges flow) v =
        ∑ p : V × V, g p := by
      unfold Slack.vertexWeight cost
      rw [allocate_option, allocate_option, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      cases hp : selected left right edges p.1 p.2 with
      | none =>
          have hf := hsupport p.1 p.2 (selected_none left right edges complete _ _ hp)
          simp [g, hf]
      | some e =>
          rcases selected_some left right edges p.1 p.2 e hp with ⟨hl, hr⟩ | ⟨hl, hr⟩
          · simp [g, hl, hr]
          · simp [g, hl, hr, add_comm]
    rw [hh, Fintype.sum_prod_type]
    simp_rw [g, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_div, ← Finset.sum_div, hrow, hcol]
    ring

/-- Finite endpoint adjacency is decidable without classical choice. -/
instance adjDecidable (left right : E → V) : DecidableRel (EdgeTransport.Adj left right) :=
  fun u v => inferInstanceAs (Decidable (∃ e, Matches left right u v e))

/-- The computed edge-cost vector from integral maximum flow and first-edge allocation. -/
def computedCost (left right : E → V) (edges : List E) (nodes : List V) (w : V → ℚ) : E → ℚ :=
  cost left right edges (CachedPreprocessing.rationalTransport (EdgeTransport.Adj left right) nodes w)

/-- The deterministic solver supplies the actual rational incidence equality
required by the integer-slack reduction. -/
theorem computedCost_correct (left right : E → V) (edges : List E)
    (edge_complete : ∀ e, e ∈ edges) (nodes : List V) (node_complete : ∀ v, v ∈ nodes)
    (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2)) :
    (∀ e, 0 ≤ computedCost left right edges nodes w e) ∧
      ∀ v, Slack.vertexWeight left right (computedCost left right edges nodes w) v = w v := by
  have ht := CachedPreprocessing.rationalTransport_correct (EdgeTransport.Adj left right)
    (EdgeTransport.adj_symmetric left right) nodes node_complete w hw ho
  exact cost_correct left right edges edge_complete w _ ht.1 ht.2.1 ht.2.2.1 ht.2.2.2

/-- The computed costs have total exactly one half of the total vertex weight. -/
theorem computedCost_total (left right : E → V) (edges : List E)
    (edge_complete : ∀ e, e ∈ edges) (nodes : List V) (node_complete : ∀ v, v ∈ nodes)
    (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) w (fun _ => 1 / 2)) :
    (∑ e, computedCost left right edges nodes w e) = (∑ v, w v) / 2 := by
  have hv := (computedCost_correct left right edges edge_complete nodes node_complete w hw ho).2
  have hsum : (∑ v, w v) = 2 * ∑ e, computedCost left right edges nodes w e := by
    simp_rw [← hv, Slack.vertexWeight]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun v e =>
      if right e = v then computedCost left right edges nodes w e else 0)]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  linarith

end WeightedMIS.EdgeAllocation
